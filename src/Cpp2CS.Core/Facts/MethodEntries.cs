namespace Cpp2CS.Facts;

public sealed record NativeMethodEntry(MethodRef Instance, ulong Address);

/// <summary>
/// 方法实例到原生入口的索引：非泛型方法取元数据中的地址，泛型实例取注册表中的入口；
/// 实例自身没有入口时取共享实现（引用类型的实参换成 System.Object，枚举换成同底层类型的共享枚举，IL2CPP 的共享规则）。
/// </summary>
public sealed class MethodEntries
{
    private readonly ManagedTypes types;
    private readonly Dictionary<(MethodRef Method, string Binding), ulong> addresses = [];
    private readonly Dictionary<MethodDef, NativeMethodEntry> definitions;

    public MethodEntries(ProgramFacts facts, ManagedTypes types)
    {
        this.types = types;
        foreach (var method in facts.Model.Methods.Where(m => m.Address != 0)) Add(new MethodRef(method, [], []), method.Address);
        // 调整桩、调用器和反向包装具有不同 ABI，不能用作方法本体的恢复入口。
        var implementations = facts.Registrations.Entries.Where(e => e.Kind is EntryKind.Method or EntryKind.GenericMethod
            && e.Method is not null && e.Address != 0).ToArray();
        foreach (var entry in implementations) Add(entry.Method!, entry.Address);
        var ordinary = facts.Model.Methods.Where(m => m.Address != 0).Select(m => new NativeMethodEntry(new(m, [], []), m.Address));
        var shared = implementations.Where(e => e.Kind == EntryKind.GenericMethod && e.Method!.Method.Address == 0)
            .Select(e => new NativeMethodEntry(e.Method!, e.Address));
        definitions = ordinary.Concat(shared).GroupBy(e => e.Instance.Method).ToDictionary(g => g.Key, SelectDefinition);
    }

    private void Add(MethodRef method, ulong address)
    {
        var key = (method, NativeBindings.Key(method));
        if (!addresses.TryGetValue(key, out var previous) || address < previous) addresses[key] = address;
    }

    /// <summary>写出定义的固定见证。与调用方顺序、请求范围无关；显式方法清单可另行指定入口。</summary>
    public NativeMethodEntry? ForDefinition(MethodDef method) => definitions.GetValueOrDefault(method);

    public IEnumerable<NativeMethodEntry> Definitions => definitions.Values.OrderBy(e => e.Instance.Method.Index);

    internal static NativeMethodEntry SelectDefinition(IEnumerable<NativeMethodEntry> candidates) => candidates
        .OrderBy(e => e.Instance.TypeArguments.Concat(e.Instance.MethodArguments)
            .Any(a => !ManagedTypes.IsReferenceType(a) || FieldLayouts.IsFullyShared(a)))
        .ThenBy(e => e.Address).ThenBy(e => NativeBindings.Key(e.Instance), StringComparer.Ordinal).First();

    /// <summary>方法实例的原生入口；没有时为 0。</summary>
    public ulong Of(MethodRef method) =>
        addresses.TryGetValue((method, NativeBindings.Key(method)), out var address)
        || Shared(method) is { } shared && addresses.TryGetValue((shared, NativeBindings.Key(shared)), out address) ? address : 0;

    private MethodRef? Shared(MethodRef method)
    {
        var shared = method with { TypeArguments = method.TypeArguments.Select(types.SharedGenericArgument).ToArray(), MethodArguments = method.MethodArguments.Select(types.SharedGenericArgument).ToArray() };
        return shared.Equals(method) ? null : shared;
    }
}
