using System.Reflection;
using Cpp2CS.Recovery.Typing;

namespace Cpp2CS.Recovery.Lowering;

/// <summary>
/// 内联访问器的逆。原生代码内联了访问器时，调用方直接读写访问器所在类型的字段；字段对调用方不可访问时，
/// 这次访问必然来自被内联的访问器。以访问器自身原生代码的恢复体为证据——getter 恰为 return this.F（或静态的 return T.F），
/// setter 恰为 this.F = value——把访问写成对它的调用（<see cref="FieldAccessor"/>，Output 在原位置写出调用）。
/// 字段可访问时保持字段访问；不可访问又没有可证明的访问器时记为洞。
/// </summary>
internal sealed partial class BodyBuilder
{
    private readonly Dictionary<(FieldDef, bool), FieldAccessor?> accessors = [];
    private readonly Dictionary<(FieldDef, bool), string> accessorFailures = [];

    /// <summary>字段对当前方法所在类型可访问（ECMA-335 II.10.3 与 I.8.5.3.2）。</summary>
    private bool Accessible(FieldDef field)
    {
        var from = analysis.Method.Method.Owner;
        var owner = field.Owner;
        bool Within(TypeDef type, TypeDef outer)
        {
            for (TypeDef? t = type; t is not null; t = t.DeclaringType)
                if (t == outer) return true;
            return false;
        }
        bool Derived()
        {
            for (TypeDef? t = from; t is not null; t = t.DeclaringType)
                for (var current = t.BaseType; current is DefinitionRef d; current = d.Definition.BaseType)
                    if (d.Definition == owner) return true;
            return Within(from, owner);
        }
        var assembly = from.Assembly == owner.Assembly;
        return (field.Attributes & FieldAttributes.FieldAccessMask) switch
        {
            FieldAttributes.Public => true,
            FieldAttributes.Private => Within(from, owner),
            FieldAttributes.Family => Derived(),
            FieldAttributes.Assembly => assembly,
            FieldAttributes.FamANDAssem => assembly && Derived(),
            FieldAttributes.FamORAssem => assembly || Derived(),
            _ => false,
        };
    }

    /// <summary>字段所在类型中，方法体恰为该字段单一读取（getter）或写入（setter）的方法。</summary>
    private FieldAccessor? Accessor(FieldRef field, TypeRef valueType, bool write)
    {
        if (accessors.TryGetValue((field.Field, write), out var known)) return known;
        accessors[(field.Field, write)] = null;
        var owner = (DefinitionRef)field.DeclaringType;
        var isStatic = (field.Field.Attributes & FieldAttributes.Static) != 0;
        FieldAccessor? found = null;
        var reasons = new List<string>();
        foreach (var definition in owner.Definition.Methods.Where(m => m.IsStatic == isStatic && m.GenericParameters.Count == 0 && m.Name != ".ctor" && m.Name != ".cctor"
            && (write ? m.Parameters.Count == 1 && ManagedTypes.IsVoid(m.ReturnType) : m.Parameters.Count == 0 && !ManagedTypes.IsVoid(m.ReturnType))))
        {
            var method = new MethodRef(definition, owner.Arguments, []);
            var declared = write ? TypeOracle.Concrete(method, definition.Parameters[0].Type) : TypeOracle.Concrete(method, definition.ReturnType);
            if (!declared.Equals(valueType)) continue;
            if (summaries(method) is not { } summary) { reasons.Add($"{definition.Name} 没有原生入口"); continue; }
            if (summary.Body is not { } body) { reasons.Add($"{definition.Name} 未恢复：{summary.Holes.FirstOrDefault()?.Reason}"); continue; }
            // 单次赋值的局部代回其值：读取被落成局部时仍是同一次读取。
            var statements = body.Blocks.SelectMany(b => b.Statements).Where(s => s is not ManagedJump).ToArray();
            var assigned = statements.OfType<ManagedAssignment>().GroupBy(a => a.Target).Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single().Value);
            var effects = statements.Where(s => s is not ManagedAssignment a || !assigned.ContainsKey(a.Target)).ToArray();
            ManagedValue Through(ManagedValue value) => value is LocalValue local && assigned.TryGetValue(local, out var source) ? Through(source) : value;
            // 字段链 F.g…：值为 this（或其地址）上的 F，或静态的 F，之后依次进入值类型字段。
            bool Chain(ManagedValue value, IReadOnlyList<FieldRef> path)
            {
                var fields = new List<FieldDef>();
                value = Through(value);
                while (value is FieldValue f && !(f.Field.Field == field.Field && f.Receiver is ArgumentValue { Index: -1 } or AddressValue { Target: ArgumentValue { Index: -1 } }))
                {
                    fields.Insert(0, f.Field.Field);
                    value = Through(f.Receiver);
                }
                var rooted = value is FieldValue { Field: var own } && own.Field == field.Field || value is StaticFieldValue { Field: var stat } && stat.Field == field.Field;
                return rooted && fields.SequenceEqual(path.Select(p => p.Field));
            }
            // 整个字段：直接的字段值，或按该值类型全部叶子组成的结构体值（拆成叶子搬运的同一个字段）。
            bool Same(ManagedValue value) => Chain(value, [])
                || Through(value) is ComposedValue { Leaves.Count: > 0 } composed && composed.Leaves.All(l => Chain(l.Value, l.Path));
            var proven = write
                ? effects is [ManagedStore { Target: var target, Value: var stored }, ManagedReturn { Value: null }] && Same(target) && Through(stored) is ArgumentValue { Index: 0 }
                : effects is [ManagedReturn { Value: { } returned }] && Same(returned);
            if (!proven) { reasons.Add($"{definition.Name} 不是单一字段访问"); continue; }
            found = new FieldAccessor(method, field, valueType, Width(valueType), write);
            break;
        }
        accessorFailures[(field.Field, write)] = reasons.Count == 0 ? "没有签名匹配的方法" : string.Join("；", reasons.Distinct().Take(3));
        return accessors[(field.Field, write)] = found;
    }

    /// <summary>字段访问：可访问时为字段本身，否则为被内联的访问器；都不成立时记为洞。</summary>
    private ManagedValue FieldAccess(ManagedValue receiver, FieldRef field, TypeRef type, bool write, ulong address)
    {
        var value = new FieldValue(receiver, field, type, Width(type));
        if (Accessible(field.Field)) return value;
        return Accessor(field, type, write) is { } accessor ? value with { Accessor = accessor }
            : Hole(address, $"内存 字段 {field.Field.Owner.FullName}.{field.Field.Name} 对调用方不可访问，没有可证明的访问器（{accessorFailures.GetValueOrDefault((field.Field, write))}）", type);
    }

    private ManagedValue StaticFieldAccess(FieldRef field, TypeRef type, bool write, ulong address)
    {
        var value = new StaticFieldValue(field, type, Width(type));
        if (Accessible(field.Field)) return value;
        return Accessor(field, type, write) is { } accessor ? value with { Accessor = accessor }
            : Hole(address, $"内存 静态字段 {field.Field.Owner.FullName}.{field.Field.Name} 对调用方不可访问，没有可证明的访问器（{accessorFailures.GetValueOrDefault((field.Field, write))}）", type);
    }
}
