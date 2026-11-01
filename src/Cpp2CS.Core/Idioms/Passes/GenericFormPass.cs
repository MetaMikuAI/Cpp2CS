
namespace Cpp2CS.Idioms;

internal static class GenericFormPass
{
    internal static DefinitionRef GenericForm(TypeDef type) => new(type, type.GenericParameters.Select(p => (TypeRef)new GenericParameterRef(p.Name, false, p.Position) { Parameter = p }).ToArray());
}
