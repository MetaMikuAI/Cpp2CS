using Cpp2CS.Model;
using Mono.Cecil;

namespace Cpp2CS.Tests.Execution;

internal static partial class CilComparison
{
    internal static bool IsGenericEntry(MethodDefinition method) => method.HasGenericParameters || method.DeclaringType.HasGenericParameters;

    internal static bool Applicable(MethodDefinition method, bool valueInstance) =>
        method.DeclaringType.GenericParameters.Concat(method.GenericParameters).All(p =>
            !(valueInstance ? p.HasReferenceTypeConstraint : p.HasNotNullableValueTypeConstraint)
            // struct 的元数据包含隐含的 System.ValueType 约束，不是额外的基类要求。
            && p.Constraints.All(c => p.HasNotNullableValueTypeConstraint && c.ConstraintType.FullName == "System.ValueType"));

    private static MethodRef Close(MethodRef method, TypeRef argument) => new(method.Method,
        Enumerable.Repeat(argument, method.Method.Owner.GenericParameters.Count).ToArray(),
        Enumerable.Repeat(argument, method.Method.GenericParameters.Count).ToArray());

    private static CilComparisonResult CompareGeneric(MethodDefinition left, MethodDefinition right, int cases, int firstSeed, int stepLimit, Func<CecilModel>? modelFactory)
    {
        modelFactory ??= CecilModel.Factory(left.Module, right.Module);
        var instances = new Dictionary<string, CilComparisonInstance>();
        foreach (var (name, value) in new[] { ("ref", false), ("value", true) })
            instances.Add(name, new(Applicable(left, value) && Applicable(right, value),
                CompareInstance(left, right, cases, firstSeed, stepLimit, modelFactory, value)));
        // 两轮都完成后再归并；一致不能遮住另一轮的差异。
        var selected = instances.FirstOrDefault(p => p.Value.Result.Status == CilComparisonStatus.Mismatch);
        if (selected.Value is null) selected = instances.FirstOrDefault(p => p.Value.Result.Status == CilComparisonStatus.Match);
        if (selected.Value is null) selected = instances.FirstOrDefault(p => p.Value.Result.ReasonKind != ComparisonReason.GenericDefinition);
        if (selected.Value is null) selected = instances.First();
        var result = selected.Value.Result;
        return result with
        {
            Reason = result.Reason is null ? null : $"{selected.Key} 轮：{result.Reason}",
            CompletedCases = instances.Values.Sum(i => i.Result.CompletedCases),
            NaNSkippedCases = instances.Values.Sum(i => i.Result.NaNSkippedCases),
            Coverage = CombinedCoverage(instances.Values.Select(i => i.Result.Coverage)),
            AttemptedCoverage = CombinedCoverage(instances.Values.Select(i => i.Result.AttemptedCoverage)),
            Instances = instances
        };
    }

    private static CoverageResult? CombinedCoverage(IEnumerable<CoverageResult?> results)
    {
        var all = results.OfType<CoverageResult>().ToArray();
        if (all.Length == 0) return null;
        var first = all[0];
        var unvisited = all.Skip(1).Aggregate(first.Unvisited.AsEnumerable(), (missing, c) => missing.Intersect(c.Unvisited)).ToArray();
        var visited = first.Instructions - unvisited.Length;
        return new(first.Instructions, visited, first.Instructions == 0 ? 0 : (double)visited / first.Instructions, unvisited,
            first.Branches.Select((b, i) => new BranchCoverage(b.Offset,
                b.Directions.Select((_, d) => all.Any(c => c.Branches[i].Directions[d])).ToArray())).ToArray());
    }
}
