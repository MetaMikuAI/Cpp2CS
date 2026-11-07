using System.Reflection;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>
/// 访问器的逆。字段对调用方不可访问时，这次访问来自被内联的方法；候选（<see cref="InlineEvidence.Candidates"/>）的恢复体
/// 沿唯一路径求值后恰为 return this.F（或静态的 return T.F、静态方法读取第一个实参的字段），或恰为 this.F = value，
/// 即为被内联的访问器，访问写成对它的调用（<see cref="FieldAccessor"/>，Output 在原位置写出调用）。
/// 访问器不改变语句结构，先于多语句模板证明；不成立的访问留给多语句模板。
/// </summary>
internal sealed partial class TemplateRecovery
{
    private readonly Dictionary<(FieldRef, TypeRef, bool, TypeRef?), FieldAccessor?> accessors = [];
    private readonly Dictionary<(FieldRef, TypeRef, bool, TypeRef?), string> accessorFailures = [];

    /// <summary>候选方法体恰为该字段的单一读取（getter）或写入（setter），且调用合法。</summary>
    public FieldAccessor? Accessor(FieldRef field, TypeRef valueType, bool write, TypeRef? receiver)
    {
        var key = (field, valueType, write, receiver);
        if (accessors.TryGetValue(key, out var known)) return known;
        accessors[key] = null;
        var owner = (DefinitionRef)field.DeclaringType;
        var isStatic = (field.Field.Attributes & FieldAttributes.Static) != 0;
        FieldAccessor? found = null;
        var reasons = new List<string>();
        foreach (var method in fields.Candidates(field, receiver))
        {
            var definition = method.Method;
            // 静态方法也可以只读取其第一个实参的字段。
            var receiverParameter = definition.IsStatic && !isStatic;
            var shape = write
                ? definition.Parameters.Count == 1 && ManagedTypes.IsVoid(definition.ReturnType) && definition.IsStatic == isStatic
                : !ManagedTypes.IsVoid(definition.ReturnType) && (receiverParameter
                    ? ManagedTypes.IsReferenceType(owner) && definition.Parameters.Count == 1 && method.Concrete(definition.Parameters[0].Type).Equals(owner)
                    : definition.Parameters.Count == 0 && definition.IsStatic == isStatic);
            if (!shape) continue;
            var declared = method.Concrete(write ? definition.Parameters[0].Type : definition.ReturnType);
            if (!declared.Equals(valueType) && (write || !ManagedTypes.IsReferenceType(valueType)
                || !ManagedTypes.IsReferenceType(declared) || !types.IsAssignable(valueType, declared))) continue;
            if (fields.CallFailure(method, receiver, isStatic ? field.DeclaringType : null) is { } illegal) { reasons.Add(illegal); continue; }
            if (Template(method) is not { } summary)
            {
                reasons.Add(method.Method == caller.Method ? $"{definition.Name} 是调用方自身"
                    : summaries(method) is null ? $"{definition.Name} 没有原生入口" : $"{definition.Name} 是同程序集未证明的方法体，不作模板");
                continue;
            }
            if (summary.Body is not { } body) { reasons.Add($"{definition.Name} 未恢复：{summary.Holes.FirstOrDefault()?.Reason}"); continue; }
            if (!AccessorBody(body, field, write, receiverParameter)) { reasons.Add($"{definition.Name} 不是单一字段访问"); continue; }
            found = new FieldAccessor(method, field, valueType, types.ValueWidth(valueType), write);
            break;
        }
        accessorFailures[key] = reasons.Count == 0 ? "没有签名匹配的方法" : string.Join("；", reasons.Distinct().Take(3));
        return accessors[key] = found;
    }

    private string? AccessorFailure(FieldRef field, TypeRef valueType, bool write, TypeRef? receiver) =>
        accessorFailures.GetValueOrDefault((field, valueType, write, receiver));

    /// <summary>
    /// 方法体沿唯一路径求值后只访问该字段一次：getter 返回该字段（或按其值类型全部叶子组成的值），读入局部的值都要用到；
    /// setter 把第一个形参写入该字段后返回。
    /// </summary>
    private bool AccessorBody(ManagedBody body, FieldRef field, bool write, bool receiverParameter)
    {
        if (body.Regions.Count > 0 || UnusedAssignment(body)) return false;
        var walker = new Walker { Blocks = body.Blocks.ToDictionary(b => b.Address), Caller = false, Block = body.Blocks[0].Address, Index = 0 };
        walker.Visited.Add(walker.Block);
        var stores = new List<(ManagedValue Location, ManagedValue Value)>();
        for (var steps = 0; steps < 64; steps++)
        {
            if (!Advance(walker, null)) return false;
            switch (walker.Current)
            {
                case ManagedStore store when Location(walker, store.Target) is { } location && Term(walker, store.Value) is { } value:
                    stores.Add((location, value));
                    walker.Stores.Add((location, value));
                    walker.Index++;
                    continue;
                case ManagedReturn { Value: null }:
                    return write && stores is [var (target, stored)] && Same(target) && stored is ArgumentValue { Index: 0 };
                case ManagedReturn { Value: { } returned }:
                    return !write && stores.Count == 0 && Term(walker, returned) is { } result && Same(result);
                default:
                    return false;
            }
        }
        return false;

        // 字段链 F.g…：根为 this（或承接接收者的第一个实参）上的 F，或静态的 F，之后依次进入值类型字段。
        bool Chain(ManagedValue value, IReadOnlyList<FieldRef> path)
        {
            var chain = new List<FieldRef>();
            while (true)
            {
                if (value is Observed observed) value = observed.Read;
                else if (value is FieldValue f) { chain.Insert(0, f.Field); value = f.Receiver; }
                else if (value is IndirectValue indirect) value = indirect.Address;
                else if (value is AddressValue address) value = address.Target;
                else break;
            }
            if (value is StaticFieldValue stat) chain.Insert(0, stat.Field);
            return (value is ArgumentValue argument && argument.Index == (receiverParameter ? 0 : -1) || value is StaticFieldValue)
                && chain.SequenceEqual(new[] { field }.Concat(path));
        }
        // 整个字段：直接的字段值，或按该值类型全部叶子组成的结构体值（拆成叶子搬运的同一个字段）。
        bool Same(ManagedValue value) => Chain(value, [])
            || value is ComposedValue { Leaves.Count: > 0 } composed && composed.Leaves.All(l => Chain(l.Value, l.Path));
    }

    /// <summary>赋值的局部在方法体中没有使用：被省略的额外求值不能视为访问器的一部分。</summary>
    private static bool UnusedAssignment(ManagedBody body)
    {
        var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
        var used = statements.SelectMany(s => (s is ManagedAssignment a ? [a.Value] : ManagedValues.Of(s)).Concat(ManagedValues.CopiedValues(s)))
            .SelectMany(ManagedValues.Walk).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
        return statements.OfType<ManagedAssignment>().Any(a => !used.Contains(a.Target.Variable));
    }

    /// <summary>
    /// 待证访问中有可证明访问器的，换成对访问器的调用；其余保持待证，并记下访问器失败的原因。
    /// 存储的目标按 setter 证明，其余位置按 getter 证明；写入意图与位置不符的访问（如取址）保持待证。
    /// </summary>
    private ManagedBody ResolveAccessors(ManagedBody body)
    {
        ManagedValue Resolve(ManagedValue value, bool target)
        {
            value = ManagedValues.Map(value, child => Resolve(child, false));
            return value switch
            {
                FieldValue { Pending: { } pending } field when pending.Write == target =>
                    Accessor(field.Field, field.Type, pending.Write, field.Receiver.Type) is { } accessor ? field with { Accessor = accessor, Pending = null }
                        : field with { Pending = WithAccessorFailure(pending, field.Field, field.Type, field.Receiver.Type) },
                StaticFieldValue { Pending: { } pending } field when pending.Write == target =>
                    Accessor(field.Field, field.Type, pending.Write, null) is { } accessor ? field with { Accessor = accessor, Pending = null }
                        : field with { Pending = WithAccessorFailure(pending, field.Field, field.Type, null) },
                _ => value,
            };
        }
        return ManagedValues.Map(body, v => Resolve(v, false), t => Resolve(t, true));
    }

    private PendingAccess WithAccessorFailure(PendingAccess pending, FieldRef field, TypeRef type, TypeRef? receiver) =>
        pending with { Reason = $"{pending.Reason}，没有可证明的访问器（{AccessorFailure(field, type, pending.Write, receiver)}）" };
}
