using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class SymbolOfPass
{
    // ---------- 槽位与静态字段块 ----------
    internal static SymbolKind SymbolOf(UsageKind kind) => kind switch
    {
        UsageKind.TypeInfo => SymbolKind.Class,
        UsageKind.Il2CppType => SymbolKind.Type,
        UsageKind.MethodDef or UsageKind.MethodRef => SymbolKind.Method,
        UsageKind.FieldInfo => SymbolKind.Field,
        _ => SymbolKind.String,
    };
}
