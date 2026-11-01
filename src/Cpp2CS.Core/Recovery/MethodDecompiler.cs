using Cpp2CS.Facts;

namespace Cpp2CS.Recovery;

/// <summary>
/// 单个托管方法的恢复入口。实例不是线程安全的，并行时每个线程各用一个。
/// </summary>
public sealed class MethodDecompiler(ProgramFacts facts, ManagedTypes types)
{
    public ManagedTypes Types => types;
    public ProgramFacts Facts => facts;

    public MethodRecoveryResult Recover(MethodRef method, ulong entry) => Unrecovered(method, entry);

    /// <summary>恢复泛型类型或泛型方法的封闭实例，方法体以封闭类型表达。</summary>
    public MethodRecoveryResult RecoverInstance(MethodRef method, ulong entry) => Unrecovered(method, entry);

    /// <summary>从已知原生实例恢复开放泛型体。</summary>
    public MethodRecoveryResult RecoverShared(MethodRef instance, ulong entry) => Unrecovered(MethodRef.Open(instance.Method), entry);

    private static MethodRecoveryResult Unrecovered(MethodRef method, ulong entry) => new(method, entry, null, [new(entry, "重写 恢复核心尚未接入")]);
}
