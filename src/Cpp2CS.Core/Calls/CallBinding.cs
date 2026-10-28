using Cpp2CS.Model;

namespace Cpp2CS.Calls;

public sealed record CallCandidate(MethodRef Method, string Evidence, string? Rejection = null);
public sealed record CallResolution(ulong Site, ulong? NativeEntry, int TypeVersion, IReadOnlyList<CallCandidate> Candidates,
    MethodRef? Selected, string Status);

/// <summary>语义方法身份与入口处的类型状态分别保存；提交到帧布局后的绑定不能静默更换。</summary>
internal sealed record CallBinding(MethodRef? Method, int Version, bool Committed = false, int IrVersion = 0);
