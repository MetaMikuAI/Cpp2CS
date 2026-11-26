using Cpp2CS.Model;

namespace Cpp2CS.Facts;

/// <summary>原表保留最小行号。登记、签名和字段推导出的其余结构按序排在原表之后。</summary>
internal sealed class ModelTypeIndex
{
    private readonly IReadOnlyList<TypeReference> registered;
    private readonly TypeReference[] additional;
    private readonly Dictionary<string, int> keys = new(StringComparer.Ordinal);

    public ModelTypeIndex(MetadataModel model)
    {
        registered = model.RuntimeTypes;
        for (int i = 0; i < registered.Count; i++)
            keys.TryAdd(EntityKeys.Structure(registered[i]), i);

        var structures = new Dictionary<string, TypeReference>(StringComparer.Ordinal);
        void Include(TypeReference type)
        {
            type = EntityKeys.Element(type);
            if (!structures.TryAdd(EntityKeys.Structure(type), type)) return;
            switch (type)
            {
                case NamedType named:
                    foreach (var argument in named.Arguments) Include(argument);
                    break;
                case ArrayType array: Include(array.Element); break;
                case PointerType pointer: Include(pointer.Element); break;
            }
        }

        foreach (var type in registered) Include(type);
        for (int i = 0; i < model.Types.Count; i++) Include(new NamedType(i, []));
        foreach (var type in model.GenericClasses.OfType<NamedType>()) Include(type);
        // metadata/GenericMethod.cpp::GetMethod：所属类、形参与返回类型均使用方法规格的上下文。
        foreach (var instance in model.MethodInstances)
        {
            var method = model.Methods[instance.Definition];
            var owner = new NamedType(method.Owner, instance.TypeArguments);
            Include(owner);
            foreach (var argument in instance.MethodArguments) Include(argument);
            TypeReference Inflate(TypeReference t) => EntityKeys.Inflate(t, owner, instance.Definition, instance.MethodArguments);
            Include(Inflate(method.ReturnType));
            foreach (var parameter in method.Parameters) Include(Inflate(parameter.Type));
        }

        // vm/GenericClass.cpp：基类和字段在所属类的上下文中代入。
        // 引用字段可以指向自身的更深泛型实例。重复展开这种路径没有有限的登记依据；
        // 独立出现在登记或方法签名里的实例各自作为起点。
        var expanded = new HashSet<string>(StringComparer.Ordinal);
        var active = new Dictionary<int, int>();
        void IncludeMembers(TypeReference type)
        {
            Include(type);
            switch (EntityKeys.Element(type))
            {
                case ArrayType array: IncludeMembers(array.Element); break;
                case PointerType pointer: IncludeMembers(pointer.Element); break;
                case NamedType { Arguments.Count: > 0 } owner:
                    string key = EntityKeys.Structure(owner);
                    if (expanded.Contains(key)) return;
                    int depth = Depth(owner);
                    bool nested = active.TryGetValue(owner.Definition, out int previous);
                    if (nested && depth > previous) return;
                    expanded.Add(key);
                    active[owner.Definition] = depth;
                    foreach (var argument in owner.Arguments) IncludeMembers(argument);
                    var definition = model.Types[owner.Definition];
                    if (definition.Parent is NamedType parent) IncludeMembers(EntityKeys.Inflate(parent, owner));
                    for (int i = definition.FirstField; i < definition.FirstField + definition.FieldCount; i++)
                        IncludeMembers(EntityKeys.Inflate(model.Fields[i].Type, owner));
                    if (nested) active[owner.Definition] = previous;
                    else active.Remove(owner.Definition);
                    break;
            }
        }
        foreach (var owner in structures.Values.OfType<NamedType>().ToArray()) IncludeMembers(owner);

        var missing = structures.Keys.Where(s => !keys.ContainsKey(s)).Order(StringComparer.Ordinal).ToArray();
        _ = checked(registered.Count + missing.Length);
        additional = new TypeReference[missing.Length];
        for (int i = 0; i < missing.Length; i++)
        {
            keys.Add(missing[i], registered.Count + i);
            additional[i] = structures[missing[i]];
        }
    }

    private static int Depth(TypeReference type) => type switch
    {
        NamedType { Arguments.Count: > 0 } n => 1 + n.Arguments.Max(Depth),
        ArrayType a => 1 + Depth(a.Element),
        PointerType p => 1 + Depth(p.Element),
        ReferenceType r => Depth(r.Element),
        _ => 0,
    };

    public int? Key(TypeReference type) => keys.TryGetValue(EntityKeys.Structure(type), out int key) ? key : null;

    public TypeReference? Describe(long key)
    {
        if (key < 0) return null;
        if (key < registered.Count)
        {
            var type = EntityKeys.Element(registered[(int)key]);
            return Key(type) == key ? type : null;
        }
        long index = key - registered.Count;
        return index < additional.Length ? additional[(int)index] : null;
    }
}
