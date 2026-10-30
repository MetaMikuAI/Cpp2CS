using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal static class ConversionCopiesRules
{
    internal static MethodRef? ConversionCopy(this RecoveryScope ctx, Call call, ulong target)
    {
        if (ctx.owner.NativeMethods.NativeConversion(target) is { } native)
            return native;
        (ArgumentValue Root, AbiPiece Piece)? Input(Expr expression)
        {
            var seen = new HashSet<Variable>();
            while (expression is Use use && seen.Add(use.Variable))
            {
                if (use.Variable.Version == 0 && ctx.State.Signature.structArguments.TryGetValue(use.Variable.Storage, out var argument) && use.Width >= argument.Piece.Width)
                    return argument;
                if (!ctx.values.TryGetValue(use.Variable, out var value) || use.Width != value.Width)
                    break;
                expression = value;
            }

            return null;
        }

        var registers = CallResolution.ArgumentsOf(call);
        var candidates = registers.Values.Select(Input).Where(v => v is not null).Select(v => v!.Value.Root.Type).Distinct().SelectMany(ctx.owner.NativeMethods.ConversionCandidates).Distinct().Select(m => new MethodRef(m, [], []));
        var matches = candidates.Where(m => ctx.owner.abi.Classify(m, out _)?.Parameters is [var parameter] && ForwardedStructArgument.Whole(parameter, registers, Input) && ctx.owner.NativeMethods.CopyOf(target, m.Method.Owner) == m.Method).Take(2).ToArray();
        return matches is [var only] ? only : null;
    }
}
