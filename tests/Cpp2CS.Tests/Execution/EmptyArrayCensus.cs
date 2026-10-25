using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests.Execution;

/// <summary>
/// System.Array.Empty&lt;T&gt;()：普查二进制中它的全部 GenericMethod 实例，要求每个恢复后都只是（类初始化之后）返回 EmptyArray&lt;T&gt;.Value。
/// 解释器据此把认回的 Array.Empty&lt;T&gt;() 当作对该静态字段的读取（CilInterpreter.InvokeAt）。
/// </summary>
[ShapeModel("空数组", Basis = "empty-census：二进制中 System.Array.Empty<T> 的全部 GenericMethod 实例都只返回 EmptyArray<T>.Value")]
internal static class EmptyArrayCensus
{
    public static bool IsEmpty(MethodRef method) => method.Method is { Name: "Empty", IsStatic: true, GenericParameters.Count: 1, Parameters.Count: 0 }
        && method.DeclaringType is DefinitionRef { Definition.FullName: "System.Array" };

    [Command("empty-census", "普查 Array.Empty<T> 实例：都只返回 EmptyArray<T>.Value", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var recovery = new MethodRecovery(facts, types);
        var a = new Assertions();
        var instances = 0;
        foreach (var function in facts.Code.Functions)
            foreach (var entry in facts.EntriesAt(function.Start).Where(e => e.Kind == EntryKind.GenericMethod && e.Method is { } m && IsEmpty(m)
                && m.MethodArguments is [DefinitionRef { Definition.FullName: not "Unity.IL2CPP.Metadata.__Il2CppFullySharedGenericType" } or ArrayRef]))
            {
                instances++;
                var result = recovery.RecoverInstance(entry.Method!, function.Start);
                var statements = result.Body?.Blocks.SelectMany(b => b.Statements).ToArray() ?? [];
                var returns = statements.OfType<ManagedReturn>().ToArray();
                // 返回的局部变量只有一次赋值时，取它的值。
                var assigned = statements.OfType<ManagedAssignment>().GroupBy(x => x.Target.Variable).Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single().Value);
                ManagedValue? Returned(ManagedReturn r) => r.Value is LocalValue local && assigned.TryGetValue(local.Variable, out var value) ? value : r.Value;
                var ok = result.Body is not null && returns.Length > 0
                    && returns.All(r => Returned(r) is StaticFieldValue { Field: { Field.Name: "Value", DeclaringType: DefinitionRef { Definition.FullName: "System.EmptyArray" } owner } }
                        // 具体类型实例直接读 EmptyArray<具体类型>；共享实例经自身 MethodInfo 的 RGCTX 读 EmptyArray<T>。
                        && (owner.Arguments.SequenceEqual(entry.Method!.MethodArguments) || owner.Arguments is [GenericParameterRef { Position: 0 }]))
                    && statements.All(s => s is ManagedReturn or ManagedJump || s is ManagedAssignment { Value: StaticFieldValue }
                        || s is ManagedCall { Invocation.Method.Method.Name: "RunClassConstructor" });
                a.True(ok, $"0x{function.Start:x} {entry.Method} 不是只返回 EmptyArray<T>.Value（{string.Join("；", result.Holes.Select(h => h.Reason).Take(2))}）");
            }
        Console.WriteLine($"  Array.Empty<T> 实例 {instances} 个");
        a.True(instances > 0, "没有找到 Array.Empty<T> 实例");
        return a.Finish("empty-census");
    }
}
