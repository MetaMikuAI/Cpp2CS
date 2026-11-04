using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery;

namespace Cpp2CS.Idioms;

/// <summary>共享泛型形参在值类型指针与引用保存槽之间转换，再复制到私有缓冲区的来源。</summary>
internal static class SharedValueCopies
{
    internal static int? Direction(IdiomState state, TypeRef type, Expr condition, uint bits)
    {
        condition = state.defs.Expand(condition, 24);
        var flag = new Load(new Binary(BinOp.Add, new Symbol(SymbolKind.Class, type), Expr.C(RuntimeLayout.ClassByvalArg + 8, 64), 64), 32);
        var sign = condition is Compare { Cond: Cond.Slt or Cond.Sge, Right: Const { Value: 0, Width: 32 }, Left: var operand } && operand == flag;
        var masked = condition is Compare { Cond: Cond.Eq or Cond.Ne, Right: Const { Value: 0 },
            Left: Binary { Op: BinOp.And, Left: var value, Right: Const { Value: 0x80000000 } } }
            && (value == flag || value is Ir.Convert { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend, Operand: var extended } && extended == flag);
        return sign || masked ? DirectionPass.Direction(condition, e => e == flag ? Expr.C(bits, 32) : null) : null;
    }

    internal static Expr? OriginalInput(IdiomState state, Expr value, TypeRef type)
    {
        if (state.self is not { } self || state.owner.abi.Machine(self, out _) is not { } signature) return null;
        var formal = MethodRef.Open(self.Method);
        return PrivateFrameInputs.Origin(state, value, source => signature.Arguments.Any(a => a.Index >= 0 && ManagedAbi.SharedValue(a.Type)
            && formal.Concrete(self.Method.Parameters[a.Index].Type).Equals(type)
            && a.Pieces is [{ Register: var register }] && source is Use { Variable.Version: 0 } use && use.Variable.Storage == register));
    }

    internal static Store? Previous(IdiomState state, Block at, int before, Expr address)
    {
        Expr Expand(Expr value) => state.defs.Expand(value, 24);
        var seen = new HashSet<Block>();
        while (seen.Add(at))
        {
            for (var i = before - 1; i >= 0; i--)
            {
                if (at.Statements[i] is Store store)
                {
                    var target = Expand(store.Target);
                    if (target == address) return store.Value.Width == 64 ? store : null;
                    if (target is not FrameAddress targetFrame || address is not FrameAddress sought
                        || targetFrame.Offset < sought.Offset + 8 && sought.Offset < targetFrame.Offset + store.Value.Width / 8) return null;
                }
                if (at.Statements[i] is Call call && (address is not FrameAddress callSlot
                    || call.Arguments.Select(Expand).Any(e => PrivateFrameInputs.Exposes(e, callSlot))))
                {
                    if (state.self is not { } self || call.Op is not { Kind: OpKind.InvokeGeneric, Operand: MethodRef invoked }
                        || state.owner.abi.Invoker((MethodRef)GenericContext.Instantiate(invoked, self)!).Indirections
                            .Any(a => a.Transfer != Transfer.Copy || a.Access != MemoryAccess.Read)) return null;
                }
            }
            if (at.IsLandingPad || at.Predecessors.ToArray() is not [var previous]) return null;
            at = previous;
            before = at.Statements.Count;
        }
        return null;
    }

    internal static Expr? Source(IdiomState state, Block block, Call copy, TypeRef type)
    {
        Expr Expand(Expr value) => state.defs.Expand(value, 24);
        var klass = new Symbol(SymbolKind.Class, type);
        var size = new Ir.Convert(ConvKind.ZeroExtend,
            new Load(new Binary(BinOp.Add, klass, Expr.C(RuntimeLayout.ClassStackSlotSize, 64), 64), 32), 64);
        if (copy is not { Op.Kind: OpKind.Import, Op.Operand: "memcpy", Arguments.Length: 3 }
            || Expand(copy.Arguments[2]) != size || Expand(copy.Arguments[1]) is not Select source) return null;
        if (Direction(state, type, source.Condition, 0x80000000) is not { } valueSide
            || Direction(state, type, source.Condition, 0) != 1 - valueSide) return null;
        var value = valueSide == 0 ? source.True : source.False;
        var reference = valueSide == 0 ? source.False : source.True;
        if (OriginalInput(state, value, type) is not { } original || reference is not FrameAddress
            || Previous(state, block, block.Statements.IndexOf(copy), reference) is not { } saved
            || OriginalInput(state, Expand(saved.Value), type) != original) return null;
        return original;
    }

    internal static bool ForwardChecks(IdiomState state)
    {
        Expr Expand(Expr value) => state.defs.Expand(value, 24);
        var changed = false;
        foreach (var block in state.function.Blocks)
        for (var i = 1; i < block.Statements.Count; i++)
        {
            if (block.Statements[i] is not Call { Op.Kind: OpKind.GenericHasValue, Op.Operand: TypeRef type, Arguments: [_, var pointer] } call) continue;
            var previous = i - 1;
            while (previous >= 0 && block.Statements[previous] is Define or Nop) previous--;
            if (previous < 0 || block.Statements[previous] is not Call { Op.Kind: OpKind.Import, Op.Operand: "memcpy", Arguments.Length: 3 } copy
                || Expand(copy.Arguments[0]) != Expand(pointer) || Source(state, block, copy, type) is not { } original) continue;
            if (Expand(pointer) is not Binary { Op: BinOp.Sub, Left: var prefix, Right: Binary { Op: BinOp.And,
                    Left: Binary { Op: BinOp.Add, Left: var size, Right: Const { Value: 15 } },
                    Right: Const { Value: 0x1fffffff0 or 0xfffffffffffffff0 } } }
                || size != Expand(copy.Arguments[2]) || DynamicStackRegion.Ceiling(prefix) is not { } ceiling
                || Expand(copy.Arguments[1]) is not Select source
                || ExprMap.Walk(source).OfType<FrameAddress>().Any(frame => frame.Offset < ceiling.Offset)) continue;
            // 复制的写入保持原位；区间内没有写入或其他调用，可从原形参读取同一值。
            block.Statements[i] = call with { Arguments = [call.Arguments[0], original] };
            changed = true;
        }
        return changed;
    }
}
