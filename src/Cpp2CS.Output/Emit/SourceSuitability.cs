namespace Cpp2CS.Output;

/// <summary>源码形式的已知限制，独立于 CIL 写出；通过不等于源码已编译。</summary>
public static class SourceSuitability
{
    public static Dictionary<ManagedBody, EmissionProblem> Check(IEnumerable<ManagedBody> bodies)
    {
        var problems = new Dictionary<ManagedBody, EmissionProblem>(ReferenceEqualityComparer.Instance);
        var constructors = new List<(ManagedBody, ConstructorSourceForm.Shape)>();
        foreach (var body in bodies.Where(b => b.Method.Method is { Name: ".ctor", IsStatic: false, Owner.IsValueType: false }))
        {
            if (ConstructorInitialization.Check(body, out var flow) is { } initialization)
                problems.Add(body, new(EmissionProblemKind.Constructor, initialization, body.Method));
            else if (ConstructorSourceForm.Check(body, flow!, out var shape) is { } source)
                problems.Add(body, new(EmissionProblemKind.SourceForm, source, body.Method));
            else constructors.Add((body, shape));
        }
        foreach (var body in ConstructorSourceForm.Inconsistent(constructors))
            problems.Add(body, new(EmissionProblemKind.SourceForm,
                "构造函数 有字段初始化器，要求本类所有构造函数都已写出且初始化器相同", body.Method));
        return problems;
    }
}
