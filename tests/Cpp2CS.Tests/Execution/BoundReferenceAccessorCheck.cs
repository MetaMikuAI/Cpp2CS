using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests.Execution;

internal static class BoundReferenceAccessorCheck
{
    [Command("bound-reference-accessor", "引用共享访问器保留调用者类型参数并拒绝无布局见证的参数", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var recovery = new MethodRecovery(facts, types);
        var a = new Assertions();
        var samples = 0;
        var owners = new HashSet<TypeDef>();
        foreach (var entry in facts.Registrations.Entries.Where(e => e.Kind == EntryKind.GenericMethod
            && e.Method is { Method: { Parameters.Count: 0, GenericParameters.Count: 0 } } method
            && method.Method.Name.StartsWith("get_", StringComparison.Ordinal) && method.TypeArguments.Any(t => t.Equals(types.Object))
            && facts.Code.At(e.Address) is { Size: <= 16 }).OrderBy(e => e.Address))
        {
            var concrete = entry.Method!;
            if (owners.Contains(concrete.Method.Owner)
                || recovery.RecoverInstance(concrete, entry.Address).Body is not { } original
                || FieldAccessors.Recognize(original, false, types) is not { ValueType: var valueType } || !valueType.Equals(types.Object)) continue;
            owners.Add(concrete.Method.Owner);
            var parameter = new GenericParameterRef("TContext", true, 0) { Binding = new(NativeBindingKind.Reference, types.Object, entry.Address) };
            MethodRef Instance(TypeRef argument) => concrete with { TypeArguments = concrete.TypeArguments.Select(t => t.Equals(types.Object) ? argument : t).ToArray() };
            var bound = recovery.RecoverInstance(Instance(parameter), entry.Address);
            a.True(bound.Body is not null && bound.Holes.Count == 0, "已有引用布局的依赖访问器可恢复");
            a.True(bound.Body is { } body && FieldAccessors.Recognize(body, false, types) is { ValueType: var actual } && actual.Equals(parameter),
                "访问器结果保留调用者的类型参数身份");
            foreach (var invalid in new[] { parameter with { Binding = null }, parameter with { Binding = new(NativeBindingKind.Shared) },
                parameter with { Binding = new(NativeBindingKind.Reference, types.Object, 0) }, parameter with { Binding = new(NativeBindingKind.Scalar, types.Int32, entry.Address) } })
                a.True(recovery.RecoverInstance(Instance(invalid), entry.Address).Body is null, "未证明的参数不沿用引用共享入口");
            if (++samples == 3) break;
        }
        a.Equal(3, samples, "三个独立泛型类型的真实 getter");
        return a.Finish("bound-reference-accessor");
    }
}
