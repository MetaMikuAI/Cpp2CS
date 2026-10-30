using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class AsyncRules
{
    /// <summary>
    /// async 方法的启动桩：<c>sm.&lt; &gt;t__builder.Start(ref sm)</c> 被内联成 <c>InitMethodRgctx(Start&lt;T&gt;)</c> 之后直接调用状态机的 MoveNext。
    /// 二进制中 Start&lt;T&gt; 的实例就是初始化 RGCTX 后尾调用 T.MoveNext(stateMachine)（普查 start-census）；状态机的 MoveNext 是显式接口实现，
    /// 不能直接调用。前面直线路径上紧邻的是这次 Start&lt;T&gt; 的 RGCTX 初始化、T 是状态机、接收者是 T 的帧区域时，写成在 builder 字段上调用 Start&lt;T&gt;。
    /// </summary>
    [CallRule(5)]
    internal static RecoveryResult<bool> StartStateMachine(this LoweringScope ctx, Call call, List<ManagedStatement> output)
    {
        if (call is not { Op: null, Kind: CallKind.Direct, Target: Const target } || ConstructionRules.Receiver(call) is not { } receiver)
            return false;
        var moveNext = ctx.facts.EntriesAt(target.Value).Select(e => e.Method).FirstOrDefault(m => m is { Method: { Name: "MoveNext", IsStatic: false, Parameters.Count: 0 } });
        if (moveNext is not { Method.Owner: { IsValueType: true } machine })
            return false;
        if (ctx.Values.PrecedingStart(call) is not { } start || start.MethodArguments is not [DefinitionRef { } argument] || argument.Definition != machine)
            return false;
        var builderType = start.DeclaringType;
        var builder = ctx.Values.StructPaths(argument).FirstOrDefault(p => p.Path.Length == 1 && p.Type.Equals(builderType));
        if (builder.Path is null)
            return false;
        if (!ctx.Values.StructAddress(receiver, argument).TryGet(out var state, out var failure))
            return failure;
        var stateValue = state is AddressValue { Target: var local } ? local : new IndirectValue(state, argument);
        output.Add(new ManagedCall(call.Address, new ManagedInvocation(start, new AddressValue(ctx.Values.PathValue(stateValue, builder.Path)), [state], false), null, false) { Inlined = true });
        return true;
    }

    internal static MethodRef? PrecedingStart(this RecoveryScope ctx, Call call)
    {
        var block = ctx.blocks.FirstOrDefault(b => b.Statements.Contains(call));
        if (block is null)
            return null;
        var index = block.Statements.IndexOf(call);
        for (var guard = 0; guard < 8; guard++)
        {
            for (var i = index - 1; i >= 0; i--)
                switch (block.Statements[i])
                {
                    case Call { Op: { Kind: OpKind.InitMethodRgctx } } init:
                        return init.Arguments is [var argument] && ctx.Expand(argument) is Symbol { Kind: SymbolKind.Method, Value: MethodRef { Method.Name: "Start" } start } && start.DeclaringType is DefinitionRef { Definition.FullName: "Cysharp.Threading.Tasks.CompilerServices.AsyncUniTaskMethodBuilder" or "Cysharp.Threading.Tasks.CompilerServices.AsyncUniTaskVoidMethodBuilder" } ? start : null;
                    case Call or Store or Branch:
                        return null;
                }

            if (block.Predecessors is not [var previous] || previous.NormalSuccessors.Count() != 1)
                return null;
            block = previous;
            index = block.Statements.Count;
        }

        return null;
    }
}
