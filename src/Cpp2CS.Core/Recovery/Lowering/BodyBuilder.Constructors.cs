using Cpp2CS.Ir;
using Cpp2CS.Recovery.Typing;

namespace Cpp2CS.Recovery.Lowering;

internal sealed partial class BodyBuilder
{
    /// <summary>
    /// 值类型构造函数被内联为字段值的逆。以构造函数自身的恢复体为模板，用内联的逆的求值
    /// 沿唯一路径执行，得到它对 this 各字段写入的值；与要构造的字段值逐项合一，形参在首次出现时绑定、之后须一致。
    /// 新值在构造完成前不可见，只比较最终写入；模板中的调用、分支、检查或对 this 的读取使证明不成立。
    /// 全部叶子都被写入且每个形参都已绑定时，值写成对该构造函数的 newobj（透明）。
    /// </summary>
    private ManagedValue? ValueConstructor(DefinitionRef structure, IReadOnlyList<(IReadOnlyList<FieldRef> Path, ManagedValue Value)> fields)
    {
        static bool Prefix(IReadOnlyList<FieldRef> prefix, IReadOnlyList<FieldRef> path) => path.Count >= prefix.Count && path.Take(prefix.Count).SequenceEqual(prefix);
        foreach (var definition in structure.Definition.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic && m.GenericParameters.Count == 0))
        {
            var method = new MethodRef(definition, structure.Arguments, []);
            if (templates.ConstructorWrites(method) is not { } writes) continue;
            var binding = new Dictionary<int, ManagedValue>();
            var valid = writes.Count > 0;
            foreach (var (path, written) in writes)
            {
                var desired = fields.FirstOrDefault(f => f.Path.SequenceEqual(path)).Value;
                if (desired is null)
                {
                    if (fields.Any(f => Prefix(path, f.Path))) { valid = false; break; }
                    var type = FieldType(path[^1], null);
                    desired = types.Kind(type) == TypeKind.Struct ? new ComposedValue(type, []) : new ConstantValue(0, type, Width(type));
                }
                valid = written switch
                {
                    ConstantValue constant => Coerce(desired, constant.Type).Equals(constant),
                    // 经 ref 形参读取：形参绑定到该值所在位置的地址。
                    IndirectValue { Address: ArgumentValue { Index: >= 0, Type: ByRefRef reference } argument } => desired.Type.Equals(reference.Element)
                        && desired is LocalValue or ArgumentValue or FieldValue or StaticFieldValue or ArrayElementValue
                        && templates.Unify(argument, new AddressValue(desired), binding),
                    ArgumentValue { Index: >= 0 } => templates.Unify(written, desired, binding),
                    _ => false,
                };
                if (!valid) break;
            }
            if (!valid || Enumerable.Range(0, definition.Parameters.Count).Any(i => !binding.ContainsKey(i))
                || !fields.All(f => writes.Any(w => Prefix(w.Path, f.Path))) || !types.Leaves(structure).All(l => writes.Any(w => Prefix(w.Path, l.Path)))) continue;
            var arguments = Enumerable.Range(0, definition.Parameters.Count)
                .Select(i => binding[i] is AddressValue address ? address : Coerce(binding[i], method.Concrete(definition.Parameters[i].Type))).ToArray();
            return new NewObjectValue(method, arguments) { Transparent = true };
        }
        return null;
    }

    private readonly Dictionary<DefinitionRef, bool> constructible = [];

    /// <summary>
    /// 值类型有构造函数可能证明按叶子组成的值：最终写入覆盖全部叶子，写入的都是形参、经 ref 形参的读取或常量。
    /// 只看构造函数自身，与要构造的值无关。
    /// </summary>
    private bool Constructible(DefinitionRef structure)
    {
        if (constructible.TryGetValue(structure, out var known)) return known;
        static bool Prefix(IReadOnlyList<FieldRef> prefix, IReadOnlyList<FieldRef> path) => path.Count >= prefix.Count && path.Take(prefix.Count).SequenceEqual(prefix);
        var found = false;
        foreach (var definition in structure.Definition.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic && m.GenericParameters.Count == 0))
        {
            var method = new MethodRef(definition, structure.Arguments, []);
            if (templates.ConstructorWrites(method) is not { Count: > 0 } writes) continue;
            if (writes.All(w => w.Value is ConstantValue or ArgumentValue { Index: >= 0 } or IndirectValue { Address: ArgumentValue { Index: >= 0 } })
                && types.Leaves(structure).All(l => writes.Any(w => Prefix(w.Path, l.Path)))) { found = true; break; }
        }
        return constructible[structure] = found;
    }

}
