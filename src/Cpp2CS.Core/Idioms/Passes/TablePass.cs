using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class TablePass
{
    internal static RgctxTable Table(MethodRef method) => new(method.Method.Owner.Assembly, method.Method.Token, method.ToString(), method.TypeArguments, method.MethodArguments);
    internal static RgctxTable Table(DefinitionRef type) => new(type.Definition.Assembly, type.Definition.Token, type.ToString(), type.Arguments, []);
}
