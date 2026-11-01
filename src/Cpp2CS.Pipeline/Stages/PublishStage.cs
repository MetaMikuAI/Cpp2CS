
namespace Cpp2CS.Pipeline;

internal sealed record PublishedMethods(List<MethodRecoveryResult> Emitted, MethodRecoveryResult[] Partials,
    HashSet<MethodRecoveryResult> PartialEmitted, Dictionary<MethodRecoveryResult, string> Problems);

/// <summary>完整体与部分体分别校验，每个视图只提交一次发布体。</summary>
internal static class PublishStage
{
    public static PublishedMethods Run(MethodRecoveryResult[] results, IReadOnlySet<MethodDef> dependencies,
        BodyEmitter emitter, IReadOnlyDictionary<ManagedBody, EmissionProblem> problems)
    {
        var emitProblems = new Dictionary<MethodRecoveryResult, string>();
        var emitted = new List<MethodRecoveryResult>();
        foreach (var result in results.Where(r => r.Body is not null))
        {
            if (problems.TryGetValue(result.Body!, out var problem)) emitProblems[result] = problem.Message;
            else emitted.Add(result);
        }
        var publication = new BodyPublication(emitter);
        publication.Publish(emitted.Select(r => r.Body!), EmissionPolicy.Recovered);
        var partials = results.Where(r => r.Body is null && r.Partial is not null && !dependencies.Contains(r.Method.Method)).ToArray();
        var partialProblems = emitter.Check(partials.Select(r => r.Partial!), EmissionPolicy.Partial);
        var partialEmitted = partials.Where(r => !partialProblems.ContainsKey(r.Partial!)).ToHashSet();
        publication.Publish(partialEmitted.Select(r => r.Partial!), EmissionPolicy.Partial);
        return new(emitted, partials, partialEmitted, emitProblems);
    }
}
