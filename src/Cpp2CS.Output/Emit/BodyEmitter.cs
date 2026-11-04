using Mono.Cecil.Cil;

namespace Cpp2CS.Output;

/// <summary>完整检查、部分阅读体、源码视图与恢复体分别选择写出策略。</summary>
public enum EmissionPolicy { Checked, Partial, Source, Recovered }

/// <summary>批量检查与 CIL 写出入口；策略按调用传入，方法间只共享程序集符号与写出证据。</summary>
public class BodyEmitter(Skeleton skeleton, ManagedTypes types, IEmissionTransforms? transforms = null, DiagnosticOptions? diagnostics = null)
{
    private readonly EmissionSymbols symbols = new();
    private readonly Dictionary<(ManagedBody, EmissionPolicy), MethodBody> built = new(new BuiltKey());
    public HashSet<Instruction> ExplicitInitializations => symbols.ExplicitInitializations;
    public Dictionary<Instruction, FieldAccessor> AccessorCalls => symbols.AccessorCalls;
    public Dictionary<Instruction, MethodRef> InlineCalls => symbols.InlineCalls;

    public byte[] Fingerprint(ManagedBody recovered, EmissionPolicy policy = EmissionPolicy.Checked)
    {
        var method = skeleton.Method(recovered.Method.Method);
        var body = new CilBodyWriter(skeleton, types, policy, new EmissionSymbols(), transforms)
            .Build(transforms?.Rewrite(recovered, types) ?? recovered, method);
        return CilBodyFingerprint.Describe(method, body);
    }

    public EmissionProblem? AccessorDependencyProblem(MethodDef method) =>
        transforms?.DependencyProblem(skeleton.Type(method.Owner)) is { } problem
            ? new(EmissionProblemKind.Dependency, problem, MethodRef.Open(method)) : null;

    /// <summary>
    /// 只读检查：恢复体的写出条件，以及写成的 CIL 的求值栈类型（<see cref="CilStackTypes"/>）。
    /// Source 策略另外按整批核对源码表达形式。
    /// 检查时建成的 CIL 体留到写出时使用，不改动骨架上的方法。
    /// </summary>
    public Dictionary<ManagedBody, EmissionProblem> Check(IEnumerable<ManagedBody> bodies, EmissionPolicy policy = EmissionPolicy.Checked)
    {
        var problems = new Dictionary<ManagedBody, EmissionProblem>(ReferenceEqualityComparer.Instance);
        var sourceBodies = new List<ManagedBody>();
        foreach (var recovered in bodies)
        {
            var check = new BodyValidation(types, policy, recovered.Method, diagnostics);
            var method = skeleton.Method(recovered.Method.Method);
            if (check.Check(recovered, method.HasBody) is { } problem)
            {
                problems.Add(recovered, problem);
                continue;
            }
            if (Build(recovered, policy, method) is var body && CilStackTypes.Check(method, body) is { } stack)
            {
                problems.Add(recovered, new(EmissionProblemKind.StackType, stack, recovered.Method));
                continue;
            }
            if (policy == EmissionPolicy.Source) sourceBodies.Add(recovered);
        }
        if (policy == EmissionPolicy.Source)
            foreach (var (body, problem) in SourceSuitability.Check(sourceBodies)) problems.Add(body, problem);
        return problems;
    }

    /// <summary>检查通过的方法逐个写出；失败的方法保留原骨架或此前写出的体。</summary>
    public Dictionary<ManagedBody, EmissionProblem> Emit(IEnumerable<ManagedBody> bodies, EmissionPolicy policy = EmissionPolicy.Checked)
    {
        var selected = bodies.ToArray();
        var problems = Check(selected, policy);
        foreach (var recovered in selected)
            if (!problems.ContainsKey(recovered))
            {
                var method = skeleton.Method(recovered.Method.Method);
                method.Body = Build(recovered, policy, method);
                built.Remove((recovered, policy));
            }
        return problems;
    }

    /// <summary>写成 CIL 但不放到骨架上：同一泛型定义的其他实例有自己的原生代码时，供执行对照使用。</summary>
    public MethodBody BuildInstance(ManagedBody recovered) =>
        new CilBodyWriter(skeleton, types, EmissionPolicy.Recovered, symbols, transforms).Build(recovered, skeleton.Method(recovered.Method.Method));

    private MethodBody Build(ManagedBody recovered, EmissionPolicy policy, Mono.Cecil.MethodDefinition method)
    {
        if (built.TryGetValue((recovered, policy), out var body)) return body;
        body = new CilBodyWriter(skeleton, types, policy, symbols, transforms).Build(transforms?.Rewrite(recovered, types) ?? recovered, method);
        built.Add((recovered, policy), body);
        return body;
    }

    private sealed class BuiltKey : IEqualityComparer<(ManagedBody Body, EmissionPolicy Policy)>
    {
        public bool Equals((ManagedBody Body, EmissionPolicy Policy) x, (ManagedBody Body, EmissionPolicy Policy) y) =>
            ReferenceEquals(x.Body, y.Body) && x.Policy == y.Policy;
        public int GetHashCode((ManagedBody Body, EmissionPolicy Policy) key) =>
            HashCode.Combine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(key.Body), key.Policy);
    }
}
