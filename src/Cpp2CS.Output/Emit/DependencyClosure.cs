
namespace Cpp2CS.Output;

/// <summary>仅补齐透明构造与内联调用；不扩张普通调用。</summary>
public static class DependencyClosure
{
    public static void Complete(IEnumerable<MethodRecoveryResult> roots, List<MethodRecoveryResult> dependencies,
        Dictionary<MethodDef, MethodRecoveryResult> recovered, IMethodResults recovery)
    {
        var selected = roots.ToArray();
        var scheduled = selected.Select(r => r.Method.Method).ToHashSet();
        var pending = new Queue<MethodRecoveryResult>(selected);
        while (pending.TryDequeue(out var current))
        {
            if (current.Body is not { } body) continue;
            foreach (var method in Required(body).Distinct().OrderBy(m => m.Index))
            {
                if (!scheduled.Add(method)) continue;
                if (!recovered.TryGetValue(method, out var dependency))
                    recovered[method] = dependency = recovery.Recover(new MethodRef(method, [], []), method.Address);
                dependencies.Add(dependency);
                pending.Enqueue(dependency);
            }
        }
    }

    public static IEnumerable<MethodDef> Required(ManagedBody body) => body.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Of)
        .SelectMany(ManagedValues.Walk).OfType<NewObjectValue>().Where(n => n.Transparent).Select(n => n.Constructor.Method)
        .Concat(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Where(c => c.Inlined && c.Invocation.Method.MethodArguments.Count == 0
            && c.Invocation.Method.TypeArguments.Count == 0).Select(c => c.Invocation.Method.Method));

    public static void Validate(IEnumerable<MethodRecoveryResult> results, Dictionary<ManagedBody, EmissionProblem> problems)
    {
        var written = results.Where(r => r.Body is not null && !problems.ContainsKey(r.Body)).ToDictionary(r => r.Method.Method);
        bool changed;
        do
        {
            changed = false;
            foreach (var result in written.Values.ToArray())
                foreach (var dependency in Required(result.Body!))
                    if (!written.ContainsKey(dependency))
                    {
                        problems[result.Body!] = new(EmissionProblemKind.Dependency, $"构造函数 内联的 {dependency} 没有写出", result.Method);
                        written.Remove(result.Method.Method);
                        changed = true;
                        break;
                    }
        } while (changed);
    }
}
