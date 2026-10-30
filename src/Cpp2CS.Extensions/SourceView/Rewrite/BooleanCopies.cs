using Cpp2CS.Ir;

namespace Cpp2CS.Extensions.SourceView;

/// <summary>ARM64 的 AND 1、扩展和截断只有追到 bool 参数时才可认回恒等复制。</summary>
internal static class BooleanCopies
{
    internal static ArgumentValue? Argument(ManagedValue value, IReadOnlyDictionary<Variable, ManagedValue>? copies = null)
    {
        var seen = new HashSet<Variable>();
        while (true)
        {
            switch (value)
            {
                case LocalValue l when seen.Add(l.Variable) && copies is not null && copies.TryGetValue(l.Variable, out var copy): value = copy; break;
                case ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.Truncate, Width: > 0, Operand: var operand }: value = operand; break;
                case BinaryValue { Op: BinOp.And, Left: var left, Right: ConstantValue { Bits: 1 } }: value = left; break;
                case ArgumentValue { Type: DefinitionRef { Definition.Keyword: "bool" } } argument: return argument;
                default: return null;
            }
        }
    }
}
