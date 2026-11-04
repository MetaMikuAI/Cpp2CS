using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Idioms;

/// <summary>共享泛型形参经私有动态副本进入 invoker 的表示转换。</summary>
internal static class SharedInvokerArguments
{
    internal sealed record Proof(Expr Value, Store Argument, Call Copy, Block Head, Block Reference);

    internal static Proof? Prove(IdiomState state, Block block, Call invoke, Expr array, int parameter, TypeRef type)
    {
        if (state.self is not { } self || state.owner.abi.Machine(self, out _) is not { } signature) return null;
        Expr Expand(Expr value) => state.defs.Expand(value, 24);
        var formal = MethodRef.Open(self.Method);
        bool Input(Expr value) => signature.Arguments.Any(a => a.Index >= 0 && ManagedAbi.SharedValue(a.Type)
            && formal.Concrete(self.Method.Parameters[a.Index].Type).Equals(type)
            && a.Pieces is [{ Register: var register }] && value is Use { Variable.Version: 0 } use && use.Variable.Storage == register);
        Store? Previous(Block at, int before, Expr address)
        {
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
                    if (at.Statements[i] is Call call && call.Arguments.Select(Expand).SelectMany(ExprMap.Walk).Any(e => e is FrameAddress)) return null;
                }
                if (at.IsLandingPad || at.Predecessors.ToArray() is not [var previous]) return null;
                at = previous;
                before = at.Statements.Count;
            }
            return null;
        }
        var address = Expand(parameter == 0 ? array : new Binary(BinOp.Add, array, Expr.C((ulong)parameter * 8, 64), 64));
        if (address is not FrameAddress argumentAddress || Previous(block, block.Statements.IndexOf(invoke), address) is not { } argument
            || Expand(argument.Value) is not Use selected) return null;
        var join = state.function.Blocks.FirstOrDefault(b => b.Statements.OfType<Phi>().Any(p => p.Target == selected.Variable));
        var phi = join?.Statements.OfType<Phi>().Single(p => p.Target == selected.Variable);
        if (join is null || phi is not { Sources.Length: 2 } || join.Predecessors.Count != 2) return null;
        var flag = new Load(new Binary(BinOp.Add, new Symbol(SymbolKind.Class, type), Expr.C(RuntimeLayout.ClassByvalArg + 8, 64), 64), 32);
        int? Direction(Expr condition, uint bits) => DirectionPass.Direction(Expand(condition), e => e == flag ? Expr.C(bits, 32) : null);
        Block? head = null;
        Block? referenceArm = null;
        Expr? destination = null;
        foreach (var predecessor in join.Predecessors)
        {
            if (predecessor.Statements.LastOrDefault() is not Branch branch || predecessor.NormalSuccessors.ToArray() is not [var taken, var fallthrough]
                || Direction(branch.Condition, 0x80000000) is not { } valueSide || Direction(branch.Condition, 0) != 1 - valueSide) continue;
            var direct = valueSide == 0 ? taken : fallthrough;
            var reference = valueSide == 0 ? fallthrough : taken;
            if (direct != join || reference.Predecessors.ToArray() is not [var only] || only != predecessor
                || reference.NormalSuccessors.ToArray() is not [var merged] || merged != join
                || reference.Statements.Any(s => s is not (Define or Jump or Nop))) continue;
            var value = Expand(new Use(phi.Sources[join.Predecessors.IndexOf(predecessor)], 64));
            var loaded = Expand(new Use(phi.Sources[join.Predecessors.IndexOf(reference)], 64));
            if (loaded != new Load(value, 64)) continue;
            head = predecessor;
            referenceArm = reference;
            destination = value;
            break;
        }
        if (head is null || referenceArm is null || destination is null) return null;
        bool PureReference(Expr value) => value == destination || value == new Load(destination, 64)
            || value is not (Load or Intrinsic or Unknown) && ExprMap.Children(value).All(PureReference);
        if (referenceArm.Statements.OfType<Define>().Any(d => !PureReference(Expand(d.Value)))) return null;
        if (join.Statements.OfType<Phi>().Any(p => p != phi && state.Used(p.Target)
            && Expand(new Use(p.Sources[0], p.Target.Width)) != Expand(new Use(p.Sources[1], p.Target.Width)))) return null;
        var size = new Ir.Convert(ConvKind.ZeroExtend,
            new Load(new Binary(BinOp.Add, new Symbol(SymbolKind.Class, type), Expr.C(RuntimeLayout.ClassStackSlotSize, 64), 64), 32), 64);
        if (destination is not Binary { Op: BinOp.Sub, Left: FrameAddress upper, Right: Binary { Op: BinOp.And, Left: Binary { Op: BinOp.Add } aligned, Right: Const mask } }
            || upper.Offset > argumentAddress.Offset
            || aligned.Left != size || aligned.Right is not Const { Value: 15 }
            || mask.Value is not (0x1fffffff0 or 0xfffffffffffffff0)) return null;
        var copies = state.All.OfType<Call>().Where(c => c is { Op.Kind: OpKind.Import, Op.Operand: "memcpy", Arguments.Length: 3 }
            && Expand(c.Arguments[0]) == destination && Expand(c.Arguments[2]) == size).ToArray();
        if (copies is not [var copy] || Expand(copy.Arguments[1]) is not Select source) return null;
        var selectedValue = Direction(source.Condition, 0x80000000) == 0 ? source.True : source.False;
        var selectedReference = Direction(source.Condition, 0) == 0 ? source.True : source.False;
        if (Direction(source.Condition, 0x80000000) is not { } valueDirection || Direction(source.Condition, 0) != 1 - valueDirection
            || !Input(selectedValue) || selectedReference is not FrameAddress) return null;
        var copyBlock = state.function.Blocks.Single(b => b.Statements.Contains(copy));
        if (!Dominators.Compute(state.function).Dominates(copyBlock.Index, block.Index)) return null;
        if (Previous(copyBlock, copyBlock.Statements.IndexOf(copy), selectedReference) is not { } saved || Expand(saved.Value) != selectedValue) return null;
        // 空值检查不观察私有副本；其他调用可能改变原形参或使副本逃逸。
        var visited = new HashSet<Block>();
        bool ReachesCopy(Block current, int end)
        {
            if (!visited.Add(current)) return true;
            for (var i = end - 1; i >= 0; i--)
            {
                var statement = current.Statements[i];
                if (ReferenceEquals(statement, copy)) return true;
                if (statement is Call other && other.Op?.Kind != OpKind.NullCheck
                    || statement is Store store && Expand(store.Target) is not FrameAddress) return false;
            }
            return current.Predecessors.Count > 0 && current.Predecessors.All(p => ReachesCopy(p, p.Statements.Count));
        }
        if (!ReachesCopy(block, block.Statements.IndexOf(invoke))) return null;
        bool Contains(Expr expression) => ExprMap.Walk(Expand(expression)).Any(e => e == destination);
        bool FrameAlias(Expr expression) => expression is not Load && (expression is FrameAddress f
            ? f.Offset <= argumentAddress.Offset + 7 : ExprMap.Children(expression).Any(FrameAlias));
        bool ReadsArgument(Expr expression) => ExprMap.Walk(Expand(expression)).OfType<Load>().Any(load =>
            load.Address != destination && (load.Address is FrameAddress f
                ? f.Offset < argumentAddress.Offset + 8 && argumentAddress.Offset < f.Offset + load.Width / 8
                : FrameAlias(load.Address)));
        IEnumerable<Expr> Observed(Stmt statement) => statement is Call { Target: Const target } call
            && state.owner.calls.Signature(target.Value) is { } known && known.Reads.All(r => r.Bank != Bank.Stack)
            ? ExprMap.Operands(call with { StackPointer = null }) : ExprMap.Operands(statement);
        foreach (var statement in state.All)
        {
            if (ReferenceEquals(statement, copy) || ReferenceEquals(statement, argument) || ReferenceEquals(statement, invoke)) continue;
            if (statement is Phi p)
            {
                if (p != phi && p.Sources.Any(v => v == phi.Target || Contains(new Use(v, v.Width))
                    || FrameAlias(Expand(new Use(v, v.Width))))) return null;
                continue;
            }
            if (ExprMap.Operands(statement).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => u.Variable == phi.Target)) return null;
            if (Observed(statement).Any(ReadsArgument)) return null;
            if (statement is Define define)
            {
                var value = Expand(define.Value);
                if (Contains(value) && value != destination && value != new Load(destination, 64)) return null;
                continue;
            }
            if (Observed(statement).Any(Contains)) return null;
            var escaped = statement is Store store ? new[] { store.Value } : Observed(statement);
            if (escaped.Select(Expand).Any(FrameAlias)) return null;
        }
        if (copy.Defines.Any(v => v is not null && state.Used(v))) return null;
        return new(selectedValue, argument, copy, head, referenceArm);
    }
}
