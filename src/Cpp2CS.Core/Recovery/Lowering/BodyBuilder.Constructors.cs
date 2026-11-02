using Cpp2CS.Ir;
using Cpp2CS.Recovery.Typing;

namespace Cpp2CS.Recovery.Lowering;

internal sealed partial class BodyBuilder
{
    /// <summary>
    /// 值类型构造函数被内联为字段值的逆。以构造函数自身的恢复体为模板，用内联的逆的求值（<see cref="Walker"/>、<see cref="Term"/>）
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
            if (summaries(method) is not { Body: { Regions.Count: 0 } template } || ConstructorWrites(template, structure) is not { } writes) continue;
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
                        && Unify(argument, new AddressValue(desired), binding),
                    ArgumentValue { Index: >= 0 } => Unify(written, desired, binding),
                    _ => false,
                };
                if (!valid) break;
            }
            if (!valid || Enumerable.Range(0, definition.Parameters.Count).Any(i => !binding.ContainsKey(i))
                || !fields.All(f => writes.Any(w => Prefix(w.Path, f.Path))) || !oracle.Leaves(structure).All(l => writes.Any(w => Prefix(w.Path, l.Path)))) continue;
            var arguments = Enumerable.Range(0, definition.Parameters.Count)
                .Select(i => binding[i] is AddressValue address ? address : Coerce(binding[i], TypeOracle.Concrete(method, definition.Parameters[i].Type))).ToArray();
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
            if (summaries(method) is not { Body: { Regions.Count: 0 } template } || ConstructorWrites(template, structure) is not { Count: > 0 } writes) continue;
            if (writes.All(w => w.Value is ConstantValue or ArgumentValue { Index: >= 0 } or IndirectValue { Address: ArgumentValue { Index: >= 0 } })
                && oracle.Leaves(structure).All(l => writes.Any(w => Prefix(w.Path, l.Path)))) { found = true; break; }
        }
        return constructible[structure] = found;
    }

    /// <summary>
    /// 值类型构造函数沿唯一路径对 this 的写入：字段链与写入的值（模板的项）。整体写入的组合值按叶子展开，缺省叶子为零；
    /// 同一字段的后一次写入代替前一次，写入已整体写过的字段的内部不成立。不能求值时为 null。
    /// </summary>
    private List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>? ConstructorWrites(ManagedBody template, DefinitionRef structure)
    {
        var walker = new Walker { Blocks = template.Blocks.ToDictionary(b => b.Address), Caller = false, Block = template.Blocks[0].Address, Index = 0 };
        walker.Visited.Add(walker.Block);
        var writes = new List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>();
        bool Write(IReadOnlyList<FieldRef> path, ManagedValue value)
        {
            if (writes.Any(w => w.Path.Count < path.Count && path.Take(w.Path.Count).SequenceEqual(w.Path))) return false;
            writes.RemoveAll(w => w.Path.Count >= path.Count && w.Path.Take(path.Count).SequenceEqual(path));
            writes.Add((path, value));
            return true;
        }
        for (var steps = 0; steps < 256; steps++)
        {
            if (!Advance(walker, null)) return null;
            switch (walker.Current)
            {
                case ManagedReturn { Value: null }:
                    return writes;
                case ManagedStore store:
                    {
                        if (Term(walker, store.Value) is not { } value || !Plain(value)) return null;
                        if (store.Target is IndirectValue { Address: ArgumentValue { Index: -1 } } && value is ComposedValue composed)
                        {
                            foreach (var (path, type, _) in oracle.Leaves(structure))
                                if (!Write(path, composed.Leaves.FirstOrDefault(l => l.Path.SequenceEqual(path)).Value ?? new ConstantValue(0, type, Width(type)))) return null;
                        }
                        else if (ThisPath(walker, store.Target) is not { Count: > 0 } path || !Write(path, value)) return null;
                        walker.Index++;
                        break;
                    }
                default:
                    return null;
            }
        }
        return null;
    }

    /// <summary>项中没有路径上的读取或调用结果。</summary>
    private static bool Plain(ManagedValue value) => value is not (Observed or Returned) && ManagedValues.Children(value).All(Plain);

    /// <summary>写入目标相对 this 的字段链：字段、取地址、读取与模板局部按其项展开；根须为 this。</summary>
    private static IReadOnlyList<FieldRef>? ThisPath(Walker walker, ManagedValue target)
    {
        var path = new List<FieldRef>();
        for (var steps = 0; steps < 32; steps++)
            switch (target)
            {
                case FieldValue field: path.Insert(0, field.Field); target = field.Receiver; break;
                case AddressValue address: target = address.Target; break;
                case Observed observed: target = observed.Read; break;
                case LocalValue local when walker.Env.TryGetValue(local.Variable, out var bound): target = bound; break;
                case ArgumentValue { Index: -1 }: return path;
                default: return null;
            }
        return null;
    }
}
