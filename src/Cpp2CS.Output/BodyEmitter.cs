using Cpp2CS.Model;
using Cpp2CS.Recovery;
using Mono.Cecil.Cil;

namespace Cpp2CS.Output;

/// <summary>完整检查、部分阅读体、源码视图与恢复体分别选择写出策略。</summary>
public enum EmissionPolicy { Checked, Partial, Source, Recovered }

/// <summary>批量检查与 CIL 写出入口；策略按调用传入，方法间只共享程序集符号与写出证据。</summary>
public sealed class BodyEmitter(Skeleton skeleton, ManagedTypes types)
{
    private readonly EmissionSymbols symbols = new();
    public HashSet<Instruction> ExplicitInitializations => symbols.ExplicitInitializations;
    public Dictionary<Instruction, FieldAccessor> AccessorCalls => symbols.AccessorCalls;
    public Dictionary<Instruction, MethodRef> InlineCalls => symbols.InlineCalls;

    public EmissionProblem? AccessorDependencyProblem(MethodDef method) =>
        AccessorDependencyEligibility.Problem(skeleton.Type(method.Owner)) is { } problem
            ? new(EmissionProblemKind.Dependency, problem, MethodRef.Open(method)) : null;

    /// <summary>只读检查；同一类型的构造函数仍按整批核对字段初始化器。</summary>
    public Dictionary<ManagedBody, EmissionProblem> Check(IEnumerable<ManagedBody> bodies, EmissionPolicy policy = EmissionPolicy.Checked)
    {
        var problems = new Dictionary<ManagedBody, EmissionProblem>(ReferenceEqualityComparer.Instance);
        var constructors = new List<(ManagedBody, ConstructorInitialization.Shape)>();
        foreach (var recovered in bodies)
        {
            var check = new BodyValidation(types, policy, recovered.Method);
            if (check.Check(recovered, skeleton.Method(recovered.Method.Method).HasBody, out var shape) is { } problem)
                problems.Add(recovered, problem);
            else if (shape is not null) constructors.Add((recovered, shape));
        }
        foreach (var constructor in ConstructorInitialization.Inconsistent(constructors))
            problems.Add(constructor, new(EmissionProblemKind.Constructor,
                "构造函数 有字段初始化器，要求本类所有构造函数都已写出且初始化器相同", constructor.Method));
        return problems;
    }

    /// <summary>检查通过的方法逐个写出；失败的方法保留原骨架或此前写出的体。</summary>
    public Dictionary<ManagedBody, EmissionProblem> Emit(IEnumerable<ManagedBody> bodies, EmissionPolicy policy = EmissionPolicy.Checked)
    {
        var selected = bodies.ToArray();
        var problems = Check(selected, policy);
        var readability = ReadabilityRewriter.FromEnvironment();
        foreach (var recovered in selected)
            if (!problems.ContainsKey(recovered))
                new CilBodyWriter(skeleton, types, policy, symbols).Write(
                    ReadabilityRewriter.Rewrite(recovered, types, readability), skeleton.Method(recovered.Method.Method));
        return problems;
    }
}
