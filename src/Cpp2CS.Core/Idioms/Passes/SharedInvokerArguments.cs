using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Ssa;
using Cpp2CS.Recovery;

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
        bool DirectInput(Expr value, TypeRef inputType) => signature.Arguments.Any(a => a.Index >= 0 && ManagedAbi.SharedValue(a.Type)
            && formal.Concrete(self.Method.Parameters[a.Index].Type).Equals(inputType)
            && a.Pieces is [{ Register: var register }] && value is Use { Variable.Version: 0 } use && use.Variable.Storage == register);
        bool ExposesFrame(Expr expression, FrameAddress sought) => expression is not Load
            && !(DynamicRegion(expression) is { } region && region.Root.Offset <= sought.Offset)
            && (expression is FrameAddress frame ? frame.Offset < sought.Offset + 8 : ExprMap.Children(expression).Any(e => ExposesFrame(e, sought)));
        Expr? OriginalInput(Expr value, TypeRef inputType)
        {
            if (DirectInput(value, inputType)) return value;
            if (value is not Load { Width: 64, Address: FrameAddress slot }) return null;
            var sites = state.function.Blocks.SelectMany(b => b.Statements.Select((s, i) => (Block: b, Index: i, Statement: s))).ToArray();
            var stores = sites.Where(s => s.Statement is Store store && Expand(store.Target) is FrameAddress frame
                && frame.Offset < slot.Offset + 8 && slot.Offset < frame.Offset + store.Value.Width / 8).ToArray();
            if (stores is not [var written] || written.Statement is not Store { Value.Width: 64 } saved
                || Expand(saved.Target) != slot || !DirectInput(Expand(saved.Value), inputType)) return null;
            var dominators = Dominators.Compute(state.function);
            foreach (var site in sites)
            {
                foreach (var load in ExprMap.Operands(site.Statement).SelectMany(ExprMap.Walk).OfType<Load>())
                    if (Expand(load.Address) is FrameAddress frame && frame.Offset < slot.Offset + 8 && slot.Offset < frame.Offset + load.Width / 8
                        && (frame != slot || load.Width != 64 || !dominators.Dominates(written.Block.Index, site.Block.Index)
                            || written.Block == site.Block && written.Index >= site.Index)) return null;
                IEnumerable<Expr> exposed = site.Statement switch
                {
                    Define => [],
                    Store store when Expand(store.Target) is FrameAddress => [store.Value],
                    Call call => call.Arguments,
                    Phi phi => phi.Sources.Select(v => (Expr)new Use(v, v.Width)),
                    _ => ExprMap.Operands(site.Statement),
                };
                if (exposed.Select(Expand).Any(e => ExposesFrame(e, slot))) return null;
            }
            return Expand(saved.Value);
        }
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
                    if (at.Statements[i] is Call call && (address is not FrameAddress callSlot
                        || call.Arguments.Select(Expand).Any(e => ExposesFrame(e, callSlot))))
                    {
                        if (call.Op is not { Kind: OpKind.InvokeGeneric, Operand: MethodRef invoked }
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
        if (DynamicRegion(destination) is not { } region || region.Root.Offset > argumentAddress.Offset || region.Sizes[^1] != size) return null;
        var copies = state.All.OfType<Call>().Where(c => c is { Op.Kind: OpKind.Import, Op.Operand: "memcpy", Arguments.Length: 3 }
            && Expand(c.Arguments[0]) == destination && Expand(c.Arguments[2]) == size).ToArray();
        if (copies is not [var copy] || Expand(copy.Arguments[1]) is not Select source) return null;
        var selectedValue = Direction(source.Condition, 0x80000000) == 0 ? source.True : source.False;
        var selectedReference = Direction(source.Condition, 0) == 0 ? source.True : source.False;
        if (Direction(source.Condition, 0x80000000) is not { } valueDirection || Direction(source.Condition, 0) != 1 - valueDirection
            || OriginalInput(selectedValue, type) is not { } original || selectedReference is not FrameAddress) return null;
        var copyBlock = state.function.Blocks.Single(b => b.Statements.Contains(copy));
        if (!Dominators.Compute(state.function).Dominates(copyBlock.Index, block.Index)) return null;
        if (Previous(copyBlock, copyBlock.Statements.IndexOf(copy), selectedReference) is not { } saved || OriginalInput(Expand(saved.Value), type) != original) return null;
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
        bool Contains(Expr expression)
        {
            var value = Expand(expression);
            return !(DynamicRegion(value) is { } other && region.Disjoint(other))
                && (value == destination || ExprMap.Children(value).Any(Contains));
        }
        bool FrameAlias(Expr expression) => expression is not Load
            && !(DynamicRegion(expression) is { } dynamic && dynamic.Root.Offset <= argumentAddress.Offset)
            && (expression is FrameAddress f ? f.Offset <= argumentAddress.Offset + 7 : ExprMap.Children(expression).Any(FrameAlias));
        bool ReadsArgument(Expr expression) => ExprMap.Walk(Expand(expression)).OfType<Load>().Any(load =>
            load.Address != destination && (load.Address is FrameAddress f
                ? f.Offset < argumentAddress.Offset + 8 && argumentAddress.Offset < f.Offset + load.Width / 8
                : FrameAlias(load.Address)));
        bool OtherCopy(Call call)
        {
            if (call is not { Op.Kind: OpKind.Import, Op.Operand: "memcpy", Arguments.Length: 3 }
                || DynamicRegion(Expand(call.Arguments[0])) is not { } other || !region.Disjoint(other)
                || Expand(call.Arguments[2]) != other.Sizes[^1] || Expand(call.Arguments[1]) is not Select selected
                || other.Sizes[^1] is not Ir.Convert { Operand: Load { Address: Binary { Left: Symbol { Value: TypeRef otherType } } } }
                || call.Defines.Any(v => v is not null && state.Used(v))) return false;
            var otherFlag = new Load(new Binary(BinOp.Add, new Symbol(SymbolKind.Class, otherType), Expr.C(RuntimeLayout.ClassByvalArg + 8, 64), 64), 32);
            int? Side(uint bits) => DirectionPass.Direction(selected.Condition, e => e == otherFlag ? Expr.C(bits, 32) : null);
            if (Side(0x80000000) is not { } valueSide || Side(0) != 1 - valueSide) return false;
            var value = valueSide == 0 ? selected.True : selected.False;
            var reference = valueSide == 0 ? selected.False : selected.True;
            return OriginalInput(value, otherType) is not null && reference is FrameAddress savedReference
                && savedReference.Offset >= region.Root.Offset
                && (savedReference.Offset + 8 <= argumentAddress.Offset || savedReference.Offset >= argumentAddress.Offset + 8);
        }
        IEnumerable<Expr> Observed(Stmt statement)
        {
            if (statement is not Call call) return ExprMap.Operands(statement);
            if (OtherCopy(call)) return [];
            Expr? Register(int register) => call.ArgumentIndex(Storage.Gpr(register)) is var index && index >= 0 ? Expand(call.Arguments[index]) : null;
            if (call.Kind == CallKind.Indirect && Expand(call.Target) is Load { Address: Binary { Op: BinOp.Add,
                    Left: Symbol { Kind: SymbolKind.Method, Value: MethodRef called } entity, Right: Const { Value: RuntimeLayout.MethodInvoker } } }
                && Register(0) == new Load(entity, 64) && Register(1) == entity && Register(3) == Expand(array)
                && ManagedTypes.IsVoid(called.Method.ReturnType))
            {
                var owner = state.function.Blocks.Single(b => b.Statements.Contains(call));
                // 参数数组可复用；本槽在另一调用前必须已由不同的写入覆盖。
                if (Previous(owner, owner.Statements.IndexOf(call), address) is { } stored && !ReferenceEquals(stored, argument))
                    return Register(2) is { } receiver ? [receiver] : ExprMap.Operands(statement);
            }
            return call.Target is Const target && state.owner.calls.Signature(target.Value) is { } known
                && known.Reads.All(r => r.Bank != Bank.Stack) ? ExprMap.Operands(call with { StackPointer = null }) : ExprMap.Operands(statement);
        }
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
        return new(original, argument, copy, head, referenceArm);
    }

    private sealed record Region(FrameAddress Root, IReadOnlyList<Expr> Sizes)
    {
        public bool Disjoint(Region other) => Root == other.Root && Sizes.Count != other.Sizes.Count
            && Sizes.Take(Math.Min(Sizes.Count, other.Sizes.Count)).SequenceEqual(other.Sizes.Take(Math.Min(Sizes.Count, other.Sizes.Count)));
    }

    /// <summary>按正的 stackslot_size 连续向下分配的区域，各段按 16 字节对齐。</summary>
    private static Region? DynamicRegion(Expr expression)
    {
        var sizes = new List<Expr>();
        while (expression is Binary { Op: BinOp.Sub, Left: var upper, Right: Binary { Op: BinOp.And,
            Left: Binary { Op: BinOp.Add, Left: var size, Right: Const { Value: 15 } }, Right: Const mask } })
        {
            if (sizes.Count >= 16 || mask.Value is not (0x1fffffff0 or 0xfffffffffffffff0)
                || size is not Ir.Convert { Kind: ConvKind.ZeroExtend, Width: 64, Operand: Load { Width: 32,
                    Address: Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Class, Value: TypeRef }, Right: Const { Value: RuntimeLayout.ClassStackSlotSize } } } }) return null;
            sizes.Insert(0, size);
            expression = upper;
        }
        return expression is FrameAddress root && sizes.Count > 0 ? new(root, sizes) : null;
    }
}
