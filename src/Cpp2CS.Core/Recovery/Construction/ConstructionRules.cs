using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Idioms;

namespace Cpp2CS.Recovery;

internal static class ConstructionRules
{
    internal static bool SameBlockBefore(this RecoveryScope ctx, Stmt first, Stmt second) => ctx.blocks.Any(b =>
    {
        var i = b.Statements.IndexOf(first);
        var j = b.Statements.IndexOf(second);
        return i >= 0 && j > i;
    });
    /// <summary>对象分配与直线链上的构造调用合并为 newobj；跨块时另证可观察顺序与异常去向。</summary>
    [Analysis("分配", 70, After = ["运行时引用"])]
    internal static void Allocations(this RecoveryScope ctx)
    {
        foreach (var block in ctx.blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call { Op: { Kind: OpKind.NewObject, Operand: DefinitionRef type } } allocation || allocation.Defines.FirstOrDefault() is not { } created)
                    continue;
                if (DelegateFacts.IsDelegate(type))
                {
                    ctx.DelegateAllocation(block, i, allocation, type, created);
                    continue;
                }

                if (ctx.BranchConstructors(block, i, allocation, type, created))
                    continue;
                Call? constructor = null;
                var inline = false;
                RecoveryHole? failure = null;
                var middle = new List<Stmt>();
                foreach (var (current, statement) in AllocationPairing.Following(block, i))
                {
                    if (!AllocationPairing.Uses(statement, created))
                    {
                        middle.Add(statement);
                        continue;
                    }

                    MethodDef? forwarded = null;
                    if (statement is Call call && ConstructionRules.Receiver(call) is Use { Variable: var receiver } && receiver == created && (call.Op is { Kind: OpKind.CallMethodPointer or OpKind.InvokeGeneric, Operand: MethodRef { Method: { Name: ".ctor", IsStatic: false } pointerCtor } } && pointerCtor.Owner == type.Definition || call is { Op: null, Kind: CallKind.Direct, Target: Const target } && (ctx.facts.EntriesAt(target.Value).Any(e => e.Method is { Method: { Name: ".ctor", IsStatic: false } ctor } && ctor.Owner == type.Definition) || ctx.facts.EntriesAt(target.Value).Any(e => e.Method is { Method: { Name: ".ctor", IsStatic: false, Parameters.Count: 0 } ctor } && ctor.Owner != type.Definition) && (forwarded = ctx.owner.NativeMethods.ForwardingConstructor(type, target.Value)) is not null)))
                    {
                        if (current != block && AllocationPairing.MotionProblem(ctx.function.Range, block, allocation, current, call, middle.Where(s => !ctx.ConstructorArgumentInitializer(s, call)), created) is { } problem)
                        {
                            failure = ctx.Hole(allocation.Address, $"分配 {type} {problem}", rule: "Allocations");
                            break;
                        }

                        constructor = call;
                        if (forwarded is not null)
                            ctx.State.Construction.forwardedConstructors[call] = new MethodRef(forwarded, type.Arguments, []);
                    }
                    else if (ctx.InlineConstructor(block, i, allocation, type, created))
                        inline = true;
                    else
                        failure = ctx.Hole(statement.Address, $"分配 {type} 在构造之前被使用", rule: "Allocations");
                    break;
                }

                if (inline)
                    continue;
                if (constructor is null)
                {
                    failure ??= ctx.Hole(allocation.Address, $"分配 {type} 没有配对的构造调用", rule: "Allocations");
                    ctx.ledger.Block(allocation, failure);
                    continue;
                }

                ctx.State.Lowering.dropped.Add(allocation);
                ctx.State.Construction.constructed[constructor] = created;
            }
    }

    internal static Expr? Receiver(Call call) => call.DelegateReceiver ?? (call.Op?.Kind == OpKind.InvokeGeneric || call.Sources.Length > 0 && call.Sources[0] == Storage.Gpr(0) ? call.Arguments[0] : null);
    internal static bool ConstructorArgumentInitializer(this RecoveryScope ctx, Stmt statement, Call constructor)
    {
        // 栈实参快照保留原求值位置；已吸收的隐藏 MethodInfo 写入不产生托管副作用。
        if (statement is Store argument && ctx.FrameOffset(argument.Target) is < 0
            && !ExprMap.Walk(argument.Value).Any(e => e is Load or Intrinsic or Unknown)
            && (ctx.State.Frames.stackArgumentStores.ContainsKey(argument) || ctx.State.Lowering.dropped.Contains(argument))) return true;
        if (constructor.Op?.Kind != OpKind.InvokeGeneric || statement is not Store { Target: TypedFrame frame } store || frame.Region.Offset >= 0 || store.Value.Width != frame.Region.Size * 8)
            return false;
        return AllocationPairing.PrivateArgumentStore(store, constructor, ctx.blocks.SelectMany(b => b.Statements));
    }
}
