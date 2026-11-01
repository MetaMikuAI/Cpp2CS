
namespace Cpp2CS.Managed;

/// <summary>会话内按需恢复依赖；调用方不持有恢复器内部状态。</summary>
public interface IMethodResults
{
    MethodRecoveryResult Recover(MethodRef method, ulong entry);
    MethodRecoveryResult RecoverInstance(MethodRef method, ulong entry);
    /// <summary>写出所需的依赖方法：按方法实例的原生入口恢复；泛型实例恢复为开放的共享体。</summary>
    MethodRecoveryResult RecoverDependency(MethodRef method);
}
