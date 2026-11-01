using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class EntryPass
{
    internal static Symbol? Entry(this IdiomState state, RgctxTable table, int index)
    {
        if (!state.facts.Registrations.Rgctx.TryGetValue((table.Image, table.Token), out var entries) || index < 0 || index >= entries.Length)
            return null;
        TypeRef Type(TypeRef t) => table.TypeArguments is null && table.MethodArguments is null ? t : t.Substitute(table.TypeArguments ?? [], table.MethodArguments ?? []);
        MethodRef Method(MethodRef m) => table.TypeArguments is null && table.MethodArguments is null ? m : m with
        {
            TypeArguments = m.TypeArguments.Select(Type).ToArray(),
            MethodArguments = m.MethodArguments.Select(Type).ToArray()
        };
        static TypeRef Element(TypeRef t) => t is ByRefRef r ? r.Element : t;
        var entry = entries[index];
        return entry switch
        {
            { Kind: RgctxKind.Type, Value: TypeRef t } => new Symbol(SymbolKind.Type, Type(t)),
            { Kind: RgctxKind.Class, Value: TypeRef t } => new Symbol(SymbolKind.Class, Type(Element(t))),
            { Kind: RgctxKind.Array, Value: TypeRef t } => new Symbol(SymbolKind.Class, new ArrayRef(Type(Element(t)), 1)),
            { Kind: RgctxKind.Method, Value: MethodRef m } => new Symbol(SymbolKind.Method, Method(m)),
            { Kind: RgctxKind.Constrained, Value: ValueTuple<TypeRef, MethodRef> c } => new Symbol(SymbolKind.Constrained, (Type(c.Item1), Method(c.Item2))),
            _ => null,
        };
    }
}
