using Mono.Cecil;

namespace Cpp2CS.Output;

/// <summary>校验后的恢复视图改写及源码视图写出选择。</summary>
public interface IEmissionTransforms
{
    ManagedBody Rewrite(ManagedBody body, ManagedTypes types);
    IReadOnlySet<ManagedStatement> SkippedStatements(ManagedBody body, EmissionPolicy policy);
    string? DependencyProblem(TypeDefinition type);
}
