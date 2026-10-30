
namespace Cpp2CS.Model;

public static class SharedTypes
{
    public static bool IsFullyShared(TypeRef type) => type switch
    {
        DefinitionRef d => d.Definition.Namespace == "Unity.IL2CPP.Metadata" && d.Definition.Name.StartsWith("__Il2CppFullyShared", StringComparison.Ordinal)
            || d.Arguments.Any(IsFullyShared),
        ArrayRef a => IsFullyShared(a.Element),
        PointerRef p => IsFullyShared(p.Element),
        ByRefRef r => IsFullyShared(r.Element),
        _ => false,
    };
}
