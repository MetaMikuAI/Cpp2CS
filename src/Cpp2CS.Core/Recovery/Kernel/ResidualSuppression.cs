namespace Cpp2CS.Recovery;

/// <summary>内核的残余压制：这些地址上的 L2 残余诊断不转成洞（例如共享泛型站点已由 L3 消费）。记录首次压制的原因 Id。</summary>
internal sealed class ResidualSuppression
{
    private readonly Dictionary<ulong, string> addresses = [];

    public void Suppress(ulong address, string reason) => addresses.TryAdd(address, reason);

    public bool Contains(ulong address) => addresses.ContainsKey(address);
}
