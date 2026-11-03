using System.Reflection;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>
/// 内联逆的共同依据：字段权限、候选方法的来源与调用的合法性。访问器与多语句模板使用同一组候选和同一套合法性，
/// 各自只按自身形态筛选和证明；下降只查询可访问性，不做内联证明。
/// </summary>
internal sealed class InlineEvidence(ManagedTypes types, MethodRef caller, Func<MethodRef, MethodRecoveryResult?> summaries,
    IReadOnlyList<MethodRef>? referenced = null)
{
    private readonly Dictionary<DefinitionRef, MethodRef[]> parameterReaders = [];

    public ManagedTypes Types => types;
    public MethodRef Caller => caller;
    public MethodRecoveryResult? Summary(MethodRef method) => summaries(method);

    public bool Accessible(FieldRef field, TypeRef? receiver) => ManagedAccess.Field(types, caller, field, receiver);

    /// <summary>
    /// 调用方以 receiver 调用 method 的 IL 合法，且不引入原生代码中没有的效果；不成立时为原因。
    /// initialized 是原生访问本身已触发初始化的类型（静态字段访问的所在类型）：方法体不含进入静态方法前的隐式类初始化，
    /// 因此不能额外触发其他类型的精确静态构造。
    /// </summary>
    public string? CallFailure(MethodRef method, TypeRef? receiver, TypeRef? initialized)
    {
        var definition = method.Method;
        if (!ManagedAccess.Method(types, caller.Method.Owner, method, definition.IsStatic ? null : receiver))
            return $"{definition.Name} 对调用方不可访问";
        if (definition.IsStatic && !method.DeclaringType.Equals(initialized)
            && (definition.Owner.Attributes & TypeAttributes.BeforeFieldInit) == 0
            && definition.Owner.Methods.Any(m => m.Name == ".cctor"))
            return $"{definition.Name} 会额外触发访问器所属类型的静态初始化";
        return null;
    }

    /// <summary>
    /// 访问 field 的候选方法（已代入类型实参），依次来自：字段所在类型及其嵌套类型；接收者到所在类型的基类链上的类型及其嵌套类型
    /// （派生类可公开受保护成员）；同程序集中以所在引用类型为唯一参数的静态方法；调用点引用的方法元数据（保留内联时的泛型实参）。
    /// 构造与类构造不是候选；是否真的访问该字段由各证明以完整方法体判定。
    /// </summary>
    public IEnumerable<MethodRef> Candidates(FieldRef field, TypeRef? receiver)
    {
        var owner = (DefinitionRef)field.DeclaringType;
        var scopes = new List<DefinitionRef> { owner };
        for (TypeRef? current = receiver is ByRefRef byRef ? byRef.Element : receiver; current is DefinitionRef type && !type.Equals(owner);
            current = type.Definition.BaseType?.Substitute(type.Arguments, []))
            scopes.Add(type);
        var seen = new HashSet<MethodRef>();
        foreach (var scope in scopes)
        {
            var nested = new List<TypeDef> { scope.Definition };
            for (var i = 0; i < nested.Count && nested.Count < 64; i++) nested.AddRange(nested[i].NestedTypes);
            foreach (var definition in nested.SelectMany(t => t.Methods))
                if (definition.GenericParameters.Count == 0 && definition.Name is not (".ctor" or ".cctor")
                    && definition.Owner.GenericParameters.Count == scope.Arguments.Count
                    && new MethodRef(definition, scope.Arguments, []) is var method && seen.Add(method))
                    yield return method;
        }
        if ((field.Field.Attributes & FieldAttributes.Static) == 0 && ManagedTypes.IsReferenceType(owner))
            foreach (var method in ParameterReaders(owner))
                if (seen.Add(method)) yield return method;
        foreach (var method in referenced ?? [])
            if (method.Method.Name is not (".ctor" or ".cctor") && seen.Add(method))
                yield return method;
    }

    /// <summary>同程序集中只有一个参数且其类型恰为 owner 的非泛型静态方法。</summary>
    private MethodRef[] ParameterReaders(DefinitionRef owner)
    {
        if (parameterReaders.TryGetValue(owner, out var known)) return known;
        return parameterReaders[owner] = types.Model.Types.Where(t => t.Assembly == owner.Definition.Assembly && t.GenericParameters.Count == 0)
            .SelectMany(t => t.Methods).Where(m => m.IsStatic && m.GenericParameters.Count == 0 && m.Parameters.Count == 1 && m.Parameters[0].Type.Equals(owner))
            .Select(m => new MethodRef(m, [], [])).ToArray();
    }
}
