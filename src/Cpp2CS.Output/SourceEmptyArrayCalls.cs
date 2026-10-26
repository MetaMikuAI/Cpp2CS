using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

public sealed partial class SourceLibraryCalls
{
    private readonly Dictionary<FieldRef, MethodRef?> emptyArrays = [];

    // Array.Empty<T> 必须在匹配二进制中返回同一静态字段，不能用新建数组代替共享实例。
    private MethodRef? EmptyArrayGetter(StaticFieldValue field)
    {
        if (field.Field.DeclaringType is not DefinitionRef
            { Definition: { Assembly: "mscorlib.dll", FullName: "System.EmptyArray" }, Arguments: [var element] }
            || field.Type is not ArrayRef { Rank: 1 }) return null;
        if (emptyArrays.TryGetValue(field.Field, out var known)) return known;
        emptyArrays[field.Field] = null;
        var definition = types.CorlibDefinition("System.Array")?.Methods.FirstOrDefault(m => m.Name == "Empty"
            && m.IsStatic && m.GenericParameters.Count == 1 && m.Parameters.Count == 0);
        if (definition is null) return null;
        var method = new MethodRef(definition, [], [element]);
        var entry = facts.Model.Code.FirstOrDefault(p => p.Value.Any(o => o.Method.Equals(method))).Key;
        if (entry == 0 || recovery.RecoverInstance(method, entry).Body is not { Regions.Count: 0 } original) return null;
        var body = SourceRewriter.Rewrite(original, types);
        var values = new Dictionary<Variable, ManagedValue>();
        ManagedValue? returned = null;
        foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
            switch (statement)
            {
                case ManagedAssignment a: values[a.Target.Variable] = Expand(a.Value, values); break;
                case ManagedReturn { Value: { } value }: returned = Expand(value, values); break;
                case ManagedJump { Edge.Copies.Count: 0 }: break;
                default: return null;
            }
        if (returned is StaticFieldValue read && read.Field.Equals(field.Field)) emptyArrays[field.Field] = method;
        return emptyArrays[field.Field];
    }
}
