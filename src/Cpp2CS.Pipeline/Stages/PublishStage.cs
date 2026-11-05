
namespace Cpp2CS.Pipeline;

internal sealed record PublishedMethods(List<MethodRecoveryResult> Emitted, MethodRecoveryResult[] Partials,
    HashSet<MethodRecoveryResult> PartialEmitted, Dictionary<MethodRecoveryResult, string> Problems);

/// <summary>完整体与部分体分别校验，每个视图只提交一次发布体。</summary>
internal static class PublishStage
{
    public static PublishedMethods Run(MethodRecoveryResult[] results, IReadOnlySet<MethodDef> dependencies,
        BodyEmitter emitter, IReadOnlyDictionary<ManagedBody, EmissionProblem> problems, bool keepGoing = false)
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
        var partialProblems = keepGoing ? emitter.CheckEach(partials.Select(r => r.Partial!), EmissionPolicy.Partial) : emitter.Check(partials.Select(r => r.Partial!), EmissionPolicy.Partial);
        var partialEmitted = partials.Where(r => !partialProblems.ContainsKey(r.Partial!)).ToHashSet();
        publication.Publish(partialEmitted.Select(r => r.Partial!), EmissionPolicy.Partial);
        return new(emitted, partials, partialEmitted, emitProblems);
    }

    /// <summary>--keep-going：既没有写出方法体、也没有部分体的方法标成 Unrecovered。运行时声明本来就没有托管体。</summary>
    public static int MarkUnrecovered(MethodRecoveryResult[] results, PublishedMethods published, BodyEmitter emitter)
    {
        var written = published.Emitted.Concat(published.PartialEmitted).Select(r => r.Method.Method).ToHashSet();
        var marked = 0;
        foreach (var result in results.Where(r => r.Declaration is null && !written.Contains(r.Method.Method)).DistinctBy(r => r.Method.Method))
        {
            emitter.MarkUnrecovered(result.Method.Method, result.Entry);
            marked++;
        }
        return marked;
    }
}
