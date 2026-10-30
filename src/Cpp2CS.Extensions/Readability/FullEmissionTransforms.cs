using Mono.Cecil;

namespace Cpp2CS.Extensions.Readability;

public sealed class FullEmissionTransforms(ReadabilityRules rules = ReadabilityRules.Int | ReadabilityRules.Null) : IEmissionTransforms
{
    public ManagedBody Rewrite(ManagedBody body, ManagedTypes types) =>
        ReadabilityRewriter.Rewrite(body, types, rules);

    public IReadOnlySet<ManagedStatement> SkippedStatements(ManagedBody body, EmissionPolicy policy) =>
        policy == EmissionPolicy.Source && Cpp2CS.Extensions.SourceView.EnumerationProtocol.IteratorMoveNext(body.Method.Method)
            ? SourceEntryDefaults.Find(body) : new HashSet<ManagedStatement>();

    public string? DependencyProblem(TypeDefinition type) => AccessorDependencyEligibility.Problem(type);
}

/// <summary>完整 profile 的写出配置；核心写出器的默认配置不加载外围。</summary>
public sealed class FullBodyEmitter(Skeleton skeleton, ManagedTypes types, DiagnosticOptions? diagnostics = null, ReadabilityRules? rules = null)
    : BodyEmitter(skeleton, types, new FullEmissionTransforms(rules ?? ReadabilityRewriter.FromEnvironment()), diagnostics);
