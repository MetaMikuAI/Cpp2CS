namespace Cpp2CS.Facts;

/// <summary>
/// 方法实例到原生入口的索引：非泛型方法取元数据中的地址，泛型实例取注册表中的入口；
/// 实例自身没有入口时取共享实现（引用类型的实参换成 System.Object，枚举换成同底层类型的共享枚举，IL2CPP 的共享规则）。
/// </summary>
public sealed class MethodEntries
{
    private readonly ManagedTypes types;
    private readonly Dictionary<MethodRef, ulong> addresses = [];

    public MethodEntries(ProgramFacts facts, ManagedTypes types)
    {
        this.types = types;
        foreach (var method in facts.Model.Methods.Where(m => m.Address != 0)) addresses.TryAdd(new MethodRef(method, [], []), method.Address);
        foreach (var entry in facts.Registrations.Entries)
            if (entry.Method is { } method && entry.Address != 0) addresses.TryAdd(method, entry.Address);
    }

    /// <summary>方法实例的原生入口；没有时为 0。</summary>
    public ulong Of(MethodRef method) =>
        addresses.TryGetValue(method, out var address) || Shared(method) is { } shared && addresses.TryGetValue(shared, out address) ? address : 0;

    private MethodRef? Shared(MethodRef method)
    {
        TypeRef Canonical(TypeRef type) => ManagedTypes.IsReferenceType(type) ? types.Object
            : type is DefinitionRef { Definition.IsEnum: true } e ? types.Corlib($"System.{ManagedTypes.PrimitiveName(ManagedTypes.Underlying(e))}Enum")
            : type is DefinitionRef { Arguments.Count: > 0 } d ? d with { Arguments = d.Arguments.Select(Canonical).ToArray() } : type;
        var shared = method with { TypeArguments = method.TypeArguments.Select(Canonical).ToArray(), MethodArguments = method.MethodArguments.Select(Canonical).ToArray() };
        return shared.Equals(method) ? null : shared;
    }
}
