using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Lifting;
using Cpp2CS.Model;

namespace Cpp2CS.Tests.Execution;

/// <summary>
/// UniTask 的 AsyncUniTaskMethodBuilder / AsyncUniTaskVoidMethodBuilder.Start&lt;TStateMachine&gt;(ref TStateMachine)：
/// 普查二进制中它的全部 GenericMethod 实例，要求每个都是（RGCTX 初始化之后）唯一一次尾调用 TStateMachine.MoveNext，实参是自己的 stateMachine（x1）。
/// 解释器据此把 Start&lt;T&gt; 当作对 T.MoveNext(ref stateMachine) 的调用（CilInterpreter.Invoke）。
/// </summary>
[ShapeModel("状态机启动", Basis = "start-census：二进制中 AsyncUniTask(Void)MethodBuilder.Start<T> 的全部 GenericMethod 实例都只尾调用 T.MoveNext(x1)")]
internal static class StartCensus
{
    public static bool IsStart(MethodRef method) => method.Method is { Name: "Start", GenericParameters.Count: 1 }
        && method.DeclaringType is DefinitionRef { Definition.FullName: "Cysharp.Threading.Tasks.CompilerServices.AsyncUniTaskMethodBuilder"
            or "Cysharp.Threading.Tasks.CompilerServices.AsyncUniTaskVoidMethodBuilder" };

    [Command("start-census", "普查 UniTask builder 的 Start<T> 实例：都只尾调用 T.MoveNext(stateMachine)", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var lifter = new FunctionLifter(facts);
        var a = new Assertions();
        var instances = 0;
        foreach (var function in facts.Code.Functions)
            // 完全共享实例（__Il2CppFullySharedGenericType）按 RGCTX 动态分派，不在模型范围内；具体类型的实例才用这个模型。
            foreach (var entry in facts.EntriesAt(function.Start).Where(e => e.Kind == EntryKind.GenericMethod && e.Method is { } m && IsStart(m)
                && m.MethodArguments is [DefinitionRef { Definition.FullName: not "Unity.IL2CPP.Metadata.__Il2CppFullySharedGenericType" }]))
            {
                instances++;
                var machine = entry.Method!.MethodArguments[0] as DefinitionRef;
                var moveNext = machine?.Definition.Methods.FirstOrDefault(m => m is { Name: "MoveNext", IsStatic: false, Parameters.Count: 0 });
                var lifted = lifter.Lift(function.Start);
                var calls = lifted.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => c.Target is Const t && facts.Code.RegionOf(t.Value) == CodeRegion.Managed).ToArray();
                var ok = lifted.Succeeded && moveNext is not null && calls is [{ Kind: CallKind.Tail, Target: Const target } call]
                    && facts.EntriesAt(target.Value).Any(e => e.Method?.Method == moveNext)
                    && call.Arguments.FirstOrDefault() is Use { Variable: { Version: 0 } self } && self.Storage == Storage.Gpr(1);
                a.True(ok, $"0x{function.Start:x} {entry.Method} 不是只尾调用 MoveNext(stateMachine)");
            }
        Console.WriteLine($"  Start<T> 实例 {instances} 个");
        a.True(instances > 0, "没有找到 Start<T> 实例");
        return a.Finish("start-census");
    }
}
