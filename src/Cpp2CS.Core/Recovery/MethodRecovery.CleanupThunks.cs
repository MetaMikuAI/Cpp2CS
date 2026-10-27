using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private readonly Dictionary<(ulong, TypeDef), (MethodRef Method, int Depth)?> cleanupThunks = new();
    private readonly Dictionary<(ulong, TypeDef), StateDispatch?> stateDispatches = new();

    private StateDispatch? Dispatch(ulong address, TypeDef owner)
    {
        if (stateDispatches.TryGetValue((address, owner), out var cached)) return cached;
        StateDispatch? result = null;
        if (facts.Code.At(address) is { } range && range.Start == address && range.Size <= 256
            && lifter.Lift(address) is { Succeeded: true } lifted && rewriter.Run(lifted.Function) is { Errors.Count: 0, Residuals.Count: 0 })
            result = StateDispatch.Read(lifted.Function, call => call is { Op: null, Target: Const target, Kind: CallKind.Direct or CallKind.Tail }
                && facts.EntriesAt(target.Value).Any(e => e.Method is { Method: { IsStatic: false, Parameters.Count: 0 } m }
                    && m.Owner == owner && ManagedTypes.IsVoid(m.ReturnType)) ? WithoutMethodInfo(call) : null);
        return stateDispatches[(address, owner)] = result;
    }

    private (MethodRef Method, int Depth)? CleanupThunk(ulong address, TypeDef type)
    {
        if (cleanupThunks.TryGetValue((address, type), out var cached)) return cached;
        (MethodRef, int)? result = null;
        if (type.GenericParameters.Count == 0 && facts.Helpers.At(address)?.Kind == HelperKind.Unknown && Dispatch(address, type) is { } thunk)
        {
            var receiver = thunk.Receiver;
            var depth = 0;
            while (receiver is Load { Width: 64 } load && depth < 3) { receiver = load.Address; depth++; }
            if (depth > 0 && receiver is Use { Variable.Version: 0 } input && input.Variable.Storage == Storage.Gpr(0))
            {
                var candidates = type.Methods.Where(m => !m.IsStatic && m.Parameters.Count == 0 && ManagedTypes.IsVoid(m.ReturnType)
                    && m.Address != 0 && m.GenericParameters.Count == 0 && Dispatch(m.Address, type) is { } dispatch
                    && dispatch.Receiver == receiver && dispatch.Same(thunk)).ToArray();
                if (candidates is [var only]) result = (new(only, [], []), depth);
            }
        }
        return cleanupThunks[(address, type)] = result;
    }

    private sealed partial class Context
    {
        private readonly HashSet<Call> cleanupCalls = new(ReferenceEqualityComparer.Instance);
        private readonly HashSet<ulong> cleanupSites = [];

        private void NormalizeCleanupThunks()
        {
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Call { Op: null, Target: Const target, Arguments.Length: > 0 } call
                        || owner.CleanupThunk(target.Value, method.Method.Owner) is not { } thunk) continue;
                    Expr receiver = call.Arguments[0];
                    for (var n = 0; n < thunk.Depth; n++) receiver = new Load(receiver, 64);
                    var replacement = call with { Target = Expr.C(thunk.Method.Method.Address, 64),
                        Arguments = [receiver, Expr.C(0, 64)], Sources = [Storage.Gpr(0), Storage.Gpr(1)], Results = [], Defines = [] };
                    block.Statements[i] = replacement;
                    cleanupCalls.Add(replacement);
                    cleanupSites.Add(call.Address);
                }
            if (cleanupCalls.Count == 0) return;
            PromotePrivateFrameSlots();
            Ssa.Propagate.Run(function, Ssa.Dominators.Compute(function));
            cleanupCalls.Clear();
            cleanupCalls.UnionWith(function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => cleanupSites.Contains(c.Address)));
        }

        // 原生闭包拆开后，不再逃逸的单次写入栈槽可以回代；不移动其他访存或调用。
        private void PromotePrivateFrameSlots()
        {
            var all = function.Blocks.SelectMany(b => b.Statements).ToArray();
            var stores = all.OfType<Store>().Where(s => s.Target is FrameAddress)
                .GroupBy(s => ((FrameAddress)s.Target).Offset).Where(g => g.Count() == 1 && g.Single().Value.Width == 64)
                .ToDictionary(g => g.Key, g => g.Single());
            var positions = function.Blocks.SelectMany(b => b.Statements.Select((s, i) => (s, b, i)))
                .ToDictionary(p => p.s, p => (p.b, p.i), (IEqualityComparer<Stmt>)ReferenceEqualityComparer.Instance);
            bool Dominates(Store store, Stmt use)
            {
                var (from, i) = positions[store]; var (to, j) = positions[use];
                if (from == to) return i < j;
                var visited = new HashSet<Block>(); var pending = new Stack<Block>(); pending.Push(function.EntryBlock);
                while (pending.TryPop(out var b))
                {
                    if (b == from || !visited.Add(b)) continue;
                    if (b == to) return false;
                    foreach (var next in b.Successors) pending.Push(next);
                }
                return true;
            }
            bool Safe(Expr e, long offset) => e switch
            {
                Load { Address: FrameAddress f } load when f.Offset < offset + 8 && f.Offset + load.Width / 8 > offset
                    => f.Offset == offset && load.Width == 64,
                FrameAddress f when f.Offset < offset + 8 => false,
                _ => ExprMap.Children(e).All(p => Safe(p, offset))
            };
            int? InvokerExtent(Call call, int index)
            {
                if (call.Op is not { Kind: OpKind.InvokeGeneric, Operand: MethodRef callee } || index == 0) return null;
                var type = index == call.Arguments.Length - 1 ? Concrete(callee, callee.Method.ReturnType)
                    : Concrete(callee, callee.Method.Parameters[index - 1].Type);
                return types.Size(type) is > 0 and var size ? size : null;
            }
            bool Touches(Stmt statement, long offset, int bytes) => FrameUses.Touches(statement, offset, bytes, InvokerExtent);
            var promotable = stores.Where(pair => pair.Value.Value is FrameAddress or Use { Variable.Version: 0 }
                && all.Where(s => !ReferenceEquals(s, pair.Value)).All(s =>
                    !Touches(s, pair.Key, 8)
                    || Dominates(pair.Value, s) && (s is Store { Target: FrameAddress dest, Value: FrameAddress source }
                        && source.Offset == pair.Key && stores.ContainsKey(dest.Offset) || ExprMap.Operands(s).All(e => Safe(e, pair.Key)))))
                .ToDictionary(p => p.Key, p => p.Value);
            Expr Expand(Expr e, int depth = 0)
            {
                if (depth > 8) return e;
                var mapped = ExprMap.Map(e, p => p is Load { Address: FrameAddress f, Width: 64 }
                    && promotable.TryGetValue(f.Offset, out var store) ? store.Value : null);
                return mapped == e ? e : Expand(mapped, depth + 1);
            }
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    var old = block.Statements[i];
                    var mapped = ExprMap.MapOperands(old, e => Expand(e));
                    block.Statements[i] = mapped;
                    if (old is Call call && cleanupCalls.Remove(call)) cleanupCalls.Add((Call)mapped);
                }
            // 仅删除不再被读取或取址的局部写入。
            foreach (var group in function.Blocks.SelectMany(b => b.Statements).OfType<Store>().Where(s => s.Target is FrameAddress)
                .GroupBy(s => ((FrameAddress)s.Target).Offset).ToArray())
            {
                var writes = group.ToHashSet();
                if (group.Select(s => s.Value.Width).Distinct().ToArray() is not [var width]
                    || group.Any(s => ExprMap.Walk(s.Value).Any(e => e is Load or Intrinsic or Unknown))
                    || function.Blocks.SelectMany(b => b.Statements).Where(s => s is not Store store || !writes.Contains(store))
                        .Any(s => Touches(s, group.Key, width / 8))) continue;
                foreach (var block in function.Blocks) block.Statements.RemoveAll(s => s is Store store && writes.Contains(store));
            }
            bool changed;
            do
            {
                changed = false;
                foreach (var block in function.Blocks)
                    foreach (var store in block.Statements.OfType<Store>().Where(s => s.Target is FrameAddress).ToArray())
                    {
                        var frame = (FrameAddress)store.Target;
                        if (ExprMap.Walk(store.Value).Any(e => e is Load or Intrinsic or Unknown)) continue;
                        if (function.Blocks.SelectMany(b => b.Statements).Where(s => !ReferenceEquals(s, store))
                            .Any(s => Touches(s, frame.Offset, store.Value.Width / 8))) continue;
                        block.Statements.Remove(store); changed = true;
                    }
            } while (changed);
        }

        [CallRule(10)]
        private bool LowerCleanupThunk(Call call, List<ManagedStatement> output)
        {
            if (!cleanupCalls.Contains(call)) return false;
            var callee = facts.EntriesAt(((Const)call.Target).Value).Select(e => e.Method).OfType<MethodRef>().Single();
            output.Add(new ManagedCall(call.Address, new ManagedInvocation(callee,
                RecoverAs(call.Arguments[0], callee.DeclaringType, call.Address), [], false), null, false) { Inlined = true });
            return true;
        }
    }
}
