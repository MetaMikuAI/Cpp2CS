using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private readonly Dictionary<TypeRef, MethodDef[]> conversionCopies = [];
    private readonly Dictionary<ulong, MethodRef?> nativeConversions = [];
    private ILookup<ulong, MethodDef>? nativeConversionCandidates;

    private MethodRef? NativeConversion(ulong target)
    {
        if (nativeConversions.TryGetValue(target, out var known)) return known;
        MethodRef? result = null;
        if (facts.EntriesAt(target).Length == 0 && facts.Unregistered.At(target) is null
            && facts.Code.At(target) is { Region: CodeRegion.Managed } copy && copy.Start == target)
        {
            // 静态运算符的实参可由向量计算生成，未必完整转传入口参数；用完整机器码确定唯一身份。
            nativeConversionCandidates ??= facts.Model.Methods.Where(m => m.IsStatic && m.Address != 0
                && m.Owner.GenericParameters.Count == 0 && m.GenericParameters.Count == 0
                && m.Name is "op_Implicit" or "op_Explicit" && m.Parameters.Count == 1
                && facts.Code.At(m.Address) is { Region: CodeRegion.Managed } original && original.Start == m.Address
                && facts.EntriesAt(m.Address).Select(e => e.Method?.Method).Distinct().Count() == 1)
                .ToLookup(m => facts.Code.At(m.Address)!.Size);
            var matches = nativeConversionCandidates[copy.Size]
                .Where(m => NativeCopy.Equal(copy, facts.Code.At(m.Address)!, facts.Code.Word)).Take(2).ToArray();
            if (matches is [var only]) result = new(only, [], []);
        }
        return nativeConversions[target] = result;
    }

    private MethodDef[] ConversionCandidates(TypeRef input)
    {
        if (!conversionCopies.TryGetValue(input, out var candidates))
            conversionCopies[input] = candidates = facts.Model.Methods.Where(m => m.IsStatic && m.Address != 0
                && m.Owner.GenericParameters.Count == 0 && m.GenericParameters.Count == 0
                && m.Name is "op_Implicit" or "op_Explicit" && m.Parameters is [{ Type: var parameter }] && parameter.Equals(input)).ToArray();
        return candidates;
    }

    private sealed partial class Context
    {
        // 静态转换没有接收者；完整转传的结构体实参提供候选类型，方法身份仍由原生副本形状证明。
        private MethodRef? ConversionCopy(Call call, ulong target)
        {
            if (owner.NativeConversion(target) is { } native) return native;
            (ArgumentValue Root, AbiPiece Piece)? Input(Expr expression)
            {
                var seen = new HashSet<Variable>();
                while (expression is Use use && seen.Add(use.Variable))
                {
                    if (use.Variable.Version == 0 && structArguments.TryGetValue(use.Variable.Storage, out var argument)
                        && use.Width >= argument.Piece.Width) return argument;
                    if (!values.TryGetValue(use.Variable, out var value) || use.Width != value.Width) break;
                    expression = value;
                }
                return null;
            }
            var registers = ArgumentsOf(call);
            var candidates = registers.Values.Select(Input).Where(v => v is not null).Select(v => v!.Value.Root.Type).Distinct()
                .SelectMany(owner.ConversionCandidates).Distinct().Select(m => new MethodRef(m, [], []));
            var matches = candidates.Where(m => owner.abi.Classify(m, out _)?.Parameters is [var parameter]
                && ForwardedStructArgument.Whole(parameter, registers, Input)
                && owner.CopyOf(target, m.Method.Owner) == m.Method).Take(2).ToArray();
            return matches is [var only] ? only : null;
        }
    }
}

internal static class ForwardedStructArgument
{
    internal static bool Whole(AbiValue parameter, IReadOnlyDictionary<Storage, Expr> registers,
        Func<Expr, (ArgumentValue Root, AbiPiece Piece)?> input)
    {
        if (parameter.Passing != Passing.Registers || parameter.Pieces.Length == 0) return false;
        ArgumentValue? root = null;
        foreach (var piece in parameter.Pieces)
        {
            if (!registers.TryGetValue(piece.Register, out var value) || input(value) is not { } part
                || part.Piece.Offset != piece.Offset || part.Piece.Width != piece.Width || !part.Root.Type.Equals(parameter.Type)
                || root is not null && !root.Equals(part.Root)) return false;
            root = part.Root;
        }
        return true;
    }
}
