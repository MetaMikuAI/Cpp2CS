using System.Reflection;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>
/// 内联访问器的逆。原生代码内联了访问器时，调用方直接读写访问器所在类型的字段；字段对调用方不可访问时，
/// 这次访问必然来自被内联的访问器。以访问器自身原生代码的恢复体为证据——getter 恰为 return this.F（或静态的 return T.F），
/// setter 恰为 this.F = value——把访问写成对它的调用（<see cref="FieldAccessor"/>，Output 在原位置写出调用）。
/// 外部静态入口可来自调用点的方法元数据引用，按实际泛型实例证明读取同一字段。
/// 字段可访问时保持字段访问；不可访问又没有可证明的访问器时记为洞。
/// </summary>
internal sealed class FieldAccessModel(ManagedTypes types, MethodRef caller, Func<MethodRef, MethodRecoveryResult?> summaries,
    IReadOnlyList<MethodRef>? referenced = null)
{
    private readonly Dictionary<(FieldRef, TypeRef, bool, TypeRef?), FieldAccessor?> accessors = [];
    private readonly Dictionary<(FieldRef, TypeRef, bool, TypeRef?), string> accessorFailures = [];

    public bool Accessible(FieldRef field, TypeRef? receiver) => ManagedAccess.Field(types, caller.Method.Owner, field, receiver);

    public string? Failure(FieldRef field, TypeRef valueType, bool write, TypeRef? receiver) =>
        accessorFailures.GetValueOrDefault((field, valueType, write, receiver));

    /// <summary>候选方法体恰为该字段的单一读取（getter）或写入（setter），且调用方有权限调用。</summary>
    public FieldAccessor? Accessor(FieldRef field, TypeRef valueType, bool write, TypeRef? receiver)
    {
        var key = (field, valueType, write, receiver);
        if (accessors.TryGetValue(key, out var known)) return known;
        accessors[key] = null;
        var owner = (DefinitionRef)field.DeclaringType;
        var isStatic = (field.Field.Attributes & FieldAttributes.Static) != 0;
        FieldAccessor? found = null;
        var reasons = new List<string>();
        var candidates = owner.Definition.Methods.Where(m => m.IsStatic == isStatic && m.GenericParameters.Count == 0 && m.Name != ".ctor" && m.Name != ".cctor"
            && (write ? m.Parameters.Count == 1 && ManagedTypes.IsVoid(m.ReturnType) : m.Parameters.Count == 0 && !ManagedTypes.IsVoid(m.ReturnType)))
            .Select(m => new MethodRef(m, owner.Arguments, []));
        // 静态方法也可以只读取其第一个实参的字段；签名筛选之后仍以完整方法体证明。
        if (!write && !isStatic && ManagedTypes.IsReferenceType(owner))
            candidates = candidates.Concat(types.Model.Types.Where(t => t.Assembly == owner.Definition.Assembly && t.GenericParameters.Count == 0)
                .SelectMany(t => t.Methods).Where(m => m.IsStatic && m.GenericParameters.Count == 0 && m.Parameters.Count == 1
                    && m.Parameters[0].Type.Equals(owner) && m.ReturnType.Equals(valueType)).Select(m => new MethodRef(m, [], [])));
        // 原生代码引用的方法元数据保留了内联泛型实参；外部静态入口仍须以完整方法体证明读取同一字段。
        if (!write && isStatic && referenced is not null)
            candidates = candidates.Concat(referenced.Where(m => m.Method.IsStatic && m.Method.Parameters.Count == 0
                && !ManagedTypes.IsVoid(m.Method.ReturnType) && m.Method.Name is not (".ctor" or ".cctor")));
        foreach (var method in candidates.Distinct())
        {
            var definition = method.Method;
            var receiverParameter = definition.IsStatic && !isStatic;
            var declared = method.Concrete(write ? definition.Parameters[0].Type : definition.ReturnType);
            if (!declared.Equals(valueType) && (write || !ManagedTypes.IsReferenceType(valueType)
                || !ManagedTypes.IsReferenceType(declared) || !types.IsAssignable(valueType, declared))) continue;
            if (!ManagedAccess.Method(types, caller.Method.Owner, method, definition.IsStatic ? null : receiver))
            { reasons.Add($"{definition.Name} 对调用方不可访问"); continue; }
            if (summaries(method) is not { } summary) { reasons.Add($"{definition.Name} 没有原生入口"); continue; }
            if (summary.Body is not { } body) { reasons.Add($"{definition.Name} 未恢复：{summary.Holes.FirstOrDefault()?.Reason}"); continue; }
            // 单次赋值的局部代回其值：读取被落成局部时仍是同一次读取。
            var statements = body.Blocks.SelectMany(b => b.Statements).Where(s => s is not ManagedJump).ToArray();
            var assigned = statements.OfType<ManagedAssignment>().GroupBy(a => a.Target).Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single().Value);
            var effects = statements.Where(s => s is not ManagedAssignment a || !assigned.ContainsKey(a.Target)).ToArray();
            var used = new HashSet<LocalValue>();
            ManagedValue Through(ManagedValue value)
            {
                if (value is not LocalValue local || !assigned.TryGetValue(local, out var source)) return value;
                used.Add(local);
                return Through(source);
            }
            // 字段链 F.g…：值为 this（或其地址）上的 F，或静态的 F，之后依次进入值类型字段。
            bool Chain(ManagedValue value, IReadOnlyList<FieldRef> path)
            {
                var fields = new List<FieldRef>();
                value = Through(value);
                while (true)
                {
                    if (value is FieldValue f) { fields.Insert(0, f.Field); value = Through(f.Receiver); }
                    else if (value is IndirectValue indirect) value = Through(indirect.Address);
                    else if (value is AddressValue address) value = Through(address.Target);
                    else break;
                }
                if (value is StaticFieldValue stat) fields.Insert(0, stat.Field);
                return (value is ArgumentValue argument && argument.Index == (receiverParameter ? 0 : -1) || value is StaticFieldValue)
                    && fields.SequenceEqual(new[] { field }.Concat(path));
            }
            // 整个字段：直接的字段值，或按该值类型全部叶子组成的结构体值（拆成叶子搬运的同一个字段）。
            bool Same(ManagedValue value) => Chain(value, [])
                || Through(value) is ComposedValue { Leaves.Count: > 0 } composed && composed.Leaves.All(l => Chain(l.Value, l.Path));
            var proven = write
                ? effects is [ManagedStore { Target: var target, Value: var stored }, ManagedReturn { Value: null }] && Same(target) && Through(stored) is ArgumentValue { Index: 0 }
                : effects is [ManagedReturn { Value: { } returned }] && Same(returned);
            if (!proven || assigned.Keys.Any(local => !used.Contains(local))) { reasons.Add($"{definition.Name} 不是单一字段访问"); continue; }
            found = new FieldAccessor(method, field, valueType, types.ValueWidth(valueType), write);
            break;
        }
        accessorFailures[key] = reasons.Count == 0 ? "没有签名匹配的方法" : string.Join("；", reasons.Distinct().Take(3));
        return accessors[key] = found;
    }

}
