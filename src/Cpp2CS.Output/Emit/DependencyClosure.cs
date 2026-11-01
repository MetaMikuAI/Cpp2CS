
namespace Cpp2CS.Output;

/// <summary>仅补齐透明构造、内联调用与被内联的访问器；不扩张普通调用。</summary>
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
            foreach (var method in Instances(body).DistinctBy(m => m.Method).OrderBy(m => m.Method.Index))
            {
                if (!scheduled.Add(method.Method)) continue;
                if (!recovered.TryGetValue(method.Method, out var dependency))
                    recovered[method.Method] = dependency = recovery.RecoverDependency(method);
                dependencies.Add(dependency);
                pending.Enqueue(dependency);
            }
        }
    }

    /// <summary>方法体透明依赖的方法实例：透明构造、内联调用与被内联的访问器。</summary>
    public static IEnumerable<MethodRef> Instances(ManagedBody body)
    {
        var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
        var values = statements.SelectMany(ManagedValues.Of).Concat(statements.OfType<ManagedStore>().Select(s => s.Target)).SelectMany(ManagedValues.Walk).ToArray();
        return values.OfType<NewObjectValue>().Where(n => n.Transparent).Select(n => n.Constructor)
            .Concat(statements.OfType<ManagedCall>().Where(c => c.Inlined).Select(c => c.Invocation.Method))
            .Concat(values.Select(v => v switch { FieldValue f => f.Accessor, StaticFieldValue f => f.Accessor, _ => null }).OfType<FieldAccessor>().Select(a => a.Method));
    }

    public static IEnumerable<MethodDef> Required(ManagedBody body) => Instances(body).Select(m => m.Method);

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
