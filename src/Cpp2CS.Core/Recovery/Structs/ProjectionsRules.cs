namespace Cpp2CS.Recovery;

/// <summary>Prepare 中的三个投影：向量 φ、调用实参与标量 φ。</summary>
internal static class ProjectionsRules
{
    [Step("structs.vector-phi-projection", StepPhase.Prepare, StepKind.Rewrite)]
    internal static void ProjectVectorPhis(RewriteScope scope) => VectorPhiProjection.Run(scope.function.Blocks);

    [Step("structs.call-argument-projection", StepPhase.Prepare, StepKind.Rewrite)]
    internal static void ProjectCallArguments(RewriteScope scope) => CallArgumentProjection.Run(scope.function.Blocks, scope.StructArgumentWidths);

    [Step("structs.scalar-phi-projection", StepPhase.Prepare, StepKind.Rewrite)]
    internal static void ProjectScalarPhis(RewriteScope scope) => ScalarPhiProjection.Run(scope.function);
}
