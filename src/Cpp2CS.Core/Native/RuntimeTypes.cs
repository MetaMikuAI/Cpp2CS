using System.Text.RegularExpressions;

namespace Cpp2CS.Native;

// 泛型槽声明来自 Dumper，实例实参来自当前 MethodInfo；未绑定的槽保留为普通读取。
public sealed class RuntimeTypes(HeaderLayout layouts, ManagedNames managed, RuntimeProfile runtime)
{
    public SemanticTerm? Load(SemanticTerm root, long offset, int width)
    {
        if (width != 64) return null;
        if (root is { Kind: "metadata" } && root.Name.StartsWith("Method$") &&
            runtime.Fields.Any(f => f.Record == "MethodInfo" && f.Field == "klass" && f.Offset == offset))
        {
            var name = root.Name[7..];
            var end = name.IndexOf('('); if (end >= 0) name = name[..end];
            var dot = ManagedNames.LastTopLevelDot(name);
            if (dot > 0) return SsaSemantics.Term("runtime-class", 64, name[..dot], type: "Il2CppClass*", inputs: [root]);
        }
        if (root.Kind == "runtime-class")
        {
            var (name, arguments) = ManagedNames.SplitGeneric(root.Name);
            var parameters = managed.GenericParameterNames(root.Name);
            if (arguments.Length != parameters.Length || arguments.Length == 0) return null;
            var definition = name + "<" + string.Join(", ", parameters) + ">";
            var native = Regex.Replace(definition, @"[^a-zA-Z0-9_]", "_") + "_c";
            var field = layouts.Members(native).SingleOrDefault(f => f.Name == "rgctx_data" && f.Offset == offset);
            if (field is not null) return SsaSemantics.Term("runtime-context", 64, root.Name, type: field.Type, inputs: [root]);
        }
        if (root is { Kind: "runtime-context", Type: { } contextType })
        {
            var field = layouts.Members(contextType).SingleOrDefault(f => f.Offset == offset && f.Size == 8);
            if (field?.Type != "Il2CppClass*") return null;
            var encoded = Regex.Replace(field.Name, @"^_\d+_", "");
            if (managed.BindEncodedContextType(encoded, root.Name) is { } bound)
                return SsaSemantics.Term("runtime-class", 64, bound, type: "Il2CppClass*", inputs: [root]);
        }
        return null;
    }
}
