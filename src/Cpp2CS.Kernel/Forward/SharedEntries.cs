using System.Collections.Immutable;
using Cpp2CS.Kernel.Engine;
using Cpp2CS.Kernel.Facts;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Kernel.Forward;

/// <summary>登记的泛型代码入口及其隐含方法指针应指向的实体。多个实体登记同一地址时可证共享。</summary>
public sealed record GenericEntry(ulong Address, EntityRef ExpectedMethod, bool MultipleEntities);

public interface IGenericEntryFacts : INativeFacts
{
    GenericEntry? GenericEntry(EntityRef method);
}

public static class NativeEntryQueries
{
    /// <summary>返回泛型实例的入口与隐含实参要求；事实提供方没有对应登记时为空。</summary>
    public static GenericEntry? GenericEntry(this INativeFacts facts, EntityRef method) =>
        (facts as IGenericEntryFacts)?.GenericEntry(method);

    /// <summary>生成签名末尾的 RuntimeMethod* 占下一个整数槽。向量槽不计入，聚合体按实际占用的槽计数。</summary>
    internal static Slot MethodArgumentSlot(ImmutableArray<ImmutableArray<(Slot Slot, int Bits)>> parameters) =>
        new(SlotKind.Integer, parameters.Sum(p => p.Count(piece => piece.Slot.Kind == SlotKind.Integer)));

    /// <summary>先由登记在共享入口的各个签名确定槽位，以免把另一个签名未使用的寄存器当作隐含实参。</summary>
    public static Slot? SharedMethodSlot(ImmutableArray<MethodShape> candidates, out string reason)
    {
        reason = "共享入口的候选签名不全";
        Slot? common = null;
        foreach (var candidate in candidates)
        {
            if (EngineFacts.Convention(candidate, out _, out reason) is not { } parameters) return null;
            var slot = MethodArgumentSlot(parameters);
            if (common is { } other && other != slot)
            {
                reason = $"共享入口的隐含实参槽不唯一：{other}、{slot}";
                return null;
            }
            common = slot;
        }
        return common;
    }

    /// <summary>按登记入口和调用点的实参给原生调用命名。</summary>
    internal static MethodShape? MethodAtCall(this Callee callee, ulong entry, Func<ulong, MethodSnapshot?>? snapshots,
        Func<Slot, Term?> argument, out string reason)
    {
        if (callee.SharedSignatures is not { } candidates)
        {
            reason = callee.Signature is null ? $"被调方法 {callee.Name} 的签名未知" : "";
            return callee.Signature;
        }
        const string unread = "共享入口的被调方法不读隐含实参：身份没有依据";
        if (snapshots?.Invoke(entry) is not { } snapshot)
        {
            reason = unread;
            return null;
        }
        if (SharedMethodSlot(candidates, out reason) is not { } hidden) return null;
        if (!ParameterSummary.ReadsHidden(snapshot, hidden))
        {
            reason = unread;
            return null;
        }
        if (argument(hidden) is not { Kind: TermKind.Entity } value)
        {
            reason = $"共享入口的隐含实参 {hidden} 未解析为实体";
            return null;
        }
        var method = candidates.FirstOrDefault(candidate => candidate.Entity == value.Entity);
        reason = method is null ? $"隐含实参 {value.Entity} 没有登记在该入口" : "";
        return method;
    }
}
