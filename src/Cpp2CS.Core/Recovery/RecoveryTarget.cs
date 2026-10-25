using Cpp2CS.Facts;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>恢复入口与元数据身份；共享实例只提供原生入口，输出保留开放泛型参数。</summary>
public sealed record RecoveryTarget(MethodRef Instance, ulong Entry)
{
    public bool Shared => Instance.Method.GenericParameters.Count > 0 || Instance.Method.Owner.GenericParameters.Count > 0;
    public MethodRef Method => Shared ? MethodRef.Open(Instance.Method) : Instance;
    public MethodRecoveryResult Recover(MethodRecovery recovery) => Shared
        ? recovery.RecoverShared(Instance, Entry) : recovery.Recover(Instance, Entry);

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
