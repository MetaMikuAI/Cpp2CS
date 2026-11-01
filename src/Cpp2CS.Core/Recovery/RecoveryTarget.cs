using Cpp2CS.Facts;

namespace Cpp2CS.Recovery;

/// <summary>恢复入口与元数据身份；共享实例只提供原生入口，输出保留开放泛型参数。</summary>
public sealed record RecoveryTarget(MethodRef Instance, ulong Entry)
{
    public bool Shared => Instance.Method.GenericParameters.Count > 0 || Instance.Method.Owner.GenericParameters.Count > 0;
    public MethodRef Method => Shared ? MethodRef.Open(Instance.Method) : Instance;
    public MethodRecoveryResult Recover(MethodRecovery recovery) => Shared
        ? recovery.RecoverShared(Instance, Entry) : recovery.Recover(Instance, Entry);

    /// <summary>
    /// 范围内的恢复目标（recover 的范围选择、recovery-batches 与 type-scope-inventory 共用这一份）：
    /// 先是有独立托管入口的方法定义，按定义次序；再是只经共享实例取得入口的泛型方法，每个定义取一个实例——
    /// 优先全部实参为引用类型且不是完全共享的实例，其次入口地址最小。
    /// </summary>
    public static IEnumerable<RecoveryTarget> Select(ProgramFacts facts, Func<MethodDef, bool> included)
    {
        var ordinary = facts.Model.Methods.Where(m => m.Address != 0 && included(m)
            && facts.Code.RegionOf(m.Address) == CodeRegion.Managed).Select(m => new RecoveryTarget(new(m, [], []), m.Address));
        var shared = facts.Model.Code.SelectMany(p => p.Value.Where(o => o.IsInstance && included(o.Method.Method))
            .Select(o => new RecoveryTarget(o.Method, p.Key))).Where(t => t.Instance.Method.Address == 0)
            .GroupBy(t => t.Instance.Method).Select(g => g.OrderBy(t => t.Instance.TypeArguments.Concat(t.Instance.MethodArguments)
                .Any(a => !ManagedTypes.IsReferenceType(a) || FieldLayouts.IsFullyShared(a))).ThenBy(t => t.Entry).First());
        return ordinary.Concat(shared);
    }

    public static RecoveryTarget Find(ProgramFacts facts, ulong entry, string name)
    {
        var definitions = entry == 0 ? facts.Model.Methods.Where(m => m.Address == 0)
            : facts.EntriesAt(entry).Where(e => e.Kind == EntryKind.Method && e.Method?.Method.Address == entry).Select(e => e.Method!.Method);
        var ordinary = definitions
            .Select(m => new MethodRef(m, [], [])).Distinct().SingleOrDefault(m => m.ToString() == name);
        if (ordinary is not null) return new(ordinary, entry);
        var instances = facts.EntriesAt(entry).Where(e => e.Kind == EntryKind.GenericMethod && e.Method is not null)
            .Select(e => e.Method!).Distinct().ToArray();
        var selected = instances.SingleOrDefault(m => m.ToString() == name)
            ?? instances.Where(m => MethodRef.Open(m.Method).ToString() == name).DistinctBy(m => m.Method).SingleOrDefault();
        return selected is not null ? new(selected, entry) : throw new InvalidDataException($"0x{entry:x} 处没有方法 {name}");
    }
}
