using System.Diagnostics.CodeAnalysis;
using Cpp2CS.Managed;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery.Inlining;

public sealed partial class StructConstructorTemplates
{
    private static bool SamePath(IReadOnlyList<FieldRef> a, IReadOnlyList<FieldRef> b) =>
        a.Count == b.Count && a.Select(f => f.Field).SequenceEqual(b.Select(f => f.Field));
    private static bool Prefix(IReadOnlyList<FieldRef> a, IReadOnlyList<FieldRef> b) =>
        a.Count <= b.Count && SamePath(a, b.Take(a.Count).ToArray());

    // 只代入签名和字段定义，不从封闭方法体反推开放方法体。
    private static (TypeRef Type, IReadOnlyList<FieldRef> Tail) OpenPath(TypeRef type, IReadOnlyList<FieldRef> path)
    {
        if (type is ByRefRef reference) type = reference.Element;
        for (int i = 0; i < path.Count; i++)
        {
            if (type is not DefinitionRef owner || owner.Definition != path[i].Field.Owner) return (type, path.Skip(i).ToArray());
            type = path[i].Field.Type.Substitute(owner.Arguments, []);
        }
        return (type, []);
    }
    private static TypeRef OpenPathType(TypeRef type, IReadOnlyList<FieldRef> path) => OpenPath(type, path).Type;
    private static bool Copy(ManagedValue value, [NotNullWhen(true)] out ArgumentValue? argument, out IReadOnlyList<FieldRef> path)
    {
        path = Path(value, out var root);
        argument = root as ArgumentValue;
        return value is ArgumentValue or FieldValue or IndirectValue && argument is { Index: >= 0 }
            && (value is not ArgumentValue || argument.Type is not ByRefRef);
    }
    private static TypeRef CopyType(MethodRef method, ArgumentValue argument, IReadOnlyList<FieldRef> path) =>
        OpenPathType(MethodRef.Open(method.Method).Concrete(method.Method.Parameters[argument.Index].Type), path);
    private bool SafeBorrow(MethodRef method, ManagedValue value, IReadOnlyList<FieldRef> outputPath)
    {
        // 存储所需的同类型扩展/掩码使用已有有效位恒等证明；改变类型或有效值的转换仍保留。
        value = ConstructorTemplates.Normalize(value, types);
        var open = MethodRef.Open(method.Method);
        var output = OpenPath(open.DeclaringType, outputPath);
        if (Copy(value, out var argument, out var path))
        {
            var input = OpenPath(open.Concrete(method.Method.Parameters[argument.Index].Type), path);
            return !ContainsParameter(input.Type) && !ContainsParameter(output.Type)
                || input.Type.Equals(output.Type) && SamePath(input.Tail, output.Tail);
        }
        if (ContainsParameter(output.Type)) return false;
        return !ManagedValues.Walk(value).Any(v => Copy(v, out var a, out var p) && ContainsParameter(CopyType(method, a, p)));
    }
    private StructConstructorTemplateResult Reproject(StructConstructorTemplate template, MethodRef site, bool borrowed)
    {
        if (template.RepresentationDependent.Count != 0)
            return No("Representation", "见证的叶子值依赖类型实参的大小或表示，不能跨实例采用。");
        // 常量也可能是 sizeof(T) 等已经折叠的结果；没有类型来源时不把它当成固定字面量。
        if (borrowed && template.Leaves.Any(l => !Copy(l.Value, out _, out _)))
            return No("Representation", "借用见证含非原样形参叶子，不能排除类型相关运算已经折叠。");
        if (site.DeclaringType is not DefinitionRef target || target.Definition != template.Type.Definition)
            return No("Generic", "见证与现场不是同一个结构体定义。");
        var targetLeaves = types.Projections(target).OrderBy(p => p.Bit).ToArray();
        if (targetLeaves.Zip(targetLeaves.Skip(1)).Any(p => p.First.Bit + p.First.Width > p.Second.Bit))
            return No("Incomplete", "现场构造布局含重叠叶子。");
        var leaves = new List<(ValueProjection Projection, ManagedValue Value)>();
        bool invalid = false;
        ManagedValue? RetypeCopy(ArgumentValue argument, IReadOnlyList<FieldRef> path)
        {
            var type = site.Concrete(site.Method.Parameters[argument.Index].Type);
            ManagedValue root = new ArgumentValue(argument.Index, type, types.ValueWidth(type));
            if (type is ByRefRef byref) { type = byref.Element; root = new IndirectValue(root, type); }
            if (path.Count == 0) return root;
            if (type is not DefinitionRef structure || types.Kind(type) != TypeKind.Struct) return null;
            var typed = types.Projections(structure).FirstOrDefault(p => Prefix(path, p.Path))?.Path.Take(path.Count).ToArray();
            return typed is not null && types.Project(structure, typed) is { } projection
                ? ManagedProjections.Project(types, root, projection, f => f)?.Value : null;
        }
        ManagedValue Remap(ManagedValue value)
        {
            if (Copy(value, out var argument, out var path))
            {
                var copy = RetypeCopy(argument, path);
                if (copy is not null) return copy;
                invalid = true; return value;
            }
            return ManagedValues.Map(value, Remap);
        }
        foreach (var projection in targetLeaves)
        {
            ManagedValue? value = null;
            var parent = template.Leaves.FirstOrDefault(l => Prefix(l.Projection.Path, projection.Path));
            if (parent.Value is not null)
            {
                value = Remap(parent.Value);
                if (parent.Projection.Path.Count < projection.Path.Count)
                    value = value.Type is DefinitionRef structure
                        && types.Project(structure, projection.Path.Skip(parent.Projection.Path.Count).ToArray()) is { } inner
                        ? ManagedProjections.Project(types, value, inner, f => f)?.Value : null;
            }
            else
            {
                // 见证的 T 是结构体、现场的 T 是标量时，只折叠完整的原样形参复制。
                var children = template.Leaves.Where(l => Prefix(projection.Path, l.Projection.Path)).ToArray();
                ArgumentValue? root = null; IReadOnlyList<FieldRef>? basePath = null;
                foreach (var child in children)
                {
                    var suffix = child.Projection.Path.Skip(projection.Path.Count).ToArray();
                    if (!Copy(child.Value, out var argument, out var path) || path.Count < suffix.Length
                        || !SamePath(suffix, path.Skip(path.Count - suffix.Length).ToArray())) { invalid = true; break; }
                    var prefix = path.Take(path.Count - suffix.Length).ToArray();
                    if (root is not null && (root.Index != argument.Index || !SamePath(basePath!, prefix))) { invalid = true; break; }
                    root = argument; basePath = prefix;
                }
                if (!invalid && root is not null)
                {
                    var witnessPath = children[0].Projection.Path.Take(projection.Path.Count).ToArray();
                    if (types.Project(template.Type, witnessPath) is { Type: DefinitionRef structure }
                        && types.Projections(structure).Count() == children.Length) value = RetypeCopy(root, basePath!);
                }
            }
            if (invalid || value is null || !Pure(site, value))
                return No("Projection", "见证的字段路径不能作为现场实例的同一叶子写入。");
            leaves.Add((projection, value));
        }
        // 不允许借用时丢掉见证独有的字段路径。
        if (template.Leaves.Any(l => !targetLeaves.Any(p => Prefix(l.Projection.Path, p.Path) || Prefix(p.Path, l.Projection.Path))))
            return No("Projection", "见证与现场的字段表不能按定义对应。");
        return new(new(target, leaves), null);
    }
}
