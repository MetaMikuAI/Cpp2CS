
namespace Cpp2CS.Output;

/// <summary>一个视图中每个方法只发布一个最终方法体。</summary>
public sealed class BodyPublication(BodyEmitter emitter)
{
    private readonly HashSet<MethodDef> published = [];

    public void Publish(IEnumerable<ManagedBody> bodies, EmissionPolicy policy)
    {
        var selected = bodies.ToArray();
        foreach (var body in selected)
            if (!published.Add(body.Method.Method)) throw new InvalidOperationException($"方法重复发布：{body.Method}");
        var problems = emitter.Emit(selected, policy);
        if (problems.Count != 0) throw new InvalidOperationException($"最终发布体未通过校验：{problems.First().Value}");
    }
}
