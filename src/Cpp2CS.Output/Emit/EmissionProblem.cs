
namespace Cpp2CS.Output;

public enum EmissionProblemKind { Unsupported, AccessDenied, ReadonlyInstanceField, ReadonlyStaticField, Constructor, Dependency }

/// <summary>写出检查的稳定分类；消息只供展示，不参与依赖选择。</summary>
public sealed record EmissionProblem(EmissionProblemKind Kind, string Message, MethodRef? Method = null, ulong? Address = null)
{
    public bool CanRecoverAccess => Kind is EmissionProblemKind.AccessDenied or EmissionProblemKind.ReadonlyInstanceField;
    public override string ToString() => Message;
}
