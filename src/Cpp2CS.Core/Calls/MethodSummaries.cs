using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Calls;

public enum RecoveryMode { Definition, Instance, Shared }

/// <summary>方法身份、原生入口与恢复方式共同确定一次分析，不能仅按显示名称缓存。</summary>
public sealed record MethodRequest(MethodRef Method, ulong Entry, RecoveryMode Mode = RecoveryMode.Definition)
{
    public string NativeIdentity { get; } = NativeBindings.Key(Method);
}

/// <summary>只读方法摘要。缺失时登记依赖，由会话补齐后重新运行使用方。</summary>
public interface IMethodSummaries
{
    MethodRecoveryResult? Find(MethodRequest request);
}
