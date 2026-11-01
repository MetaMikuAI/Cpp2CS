
namespace Cpp2CS.Managed;

/// <summary>会话内按需恢复依赖；调用方不持有恢复器内部状态。</summary>
public interface IMethodResults
{
    MethodRecoveryResult Recover(MethodRef method, ulong entry);
    MethodRecoveryResult RecoverInstance(MethodRef method, ulong entry);
}
