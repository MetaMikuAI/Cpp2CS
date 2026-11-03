
namespace Cpp2CS.Managed;

/// <summary>会话内按需恢复依赖；调用方不持有恢复器内部状态。</summary>
public interface IMethodResults
{
    MethodRecoveryResult Recover(MethodRef method, ulong entry);
    MethodRecoveryResult RecoverInstance(MethodRef method, ulong entry);
    /// <summary>写出所需的定义体，原生见证由统一索引选择，不使用调用方碰巧遇到的实例。</summary>
    MethodRecoveryResult RecoverDefinition(MethodDef method);
}
