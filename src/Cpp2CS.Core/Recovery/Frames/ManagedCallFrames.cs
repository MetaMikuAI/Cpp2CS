using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>调用的托管 ABI 及传址范围，供栈槽提升与捕获指针回代共享。</summary>
internal sealed class ManagedCallFrames(ProgramFacts facts, ManagedAbi abi)
{
    private readonly Dictionary<Call, AbiSignature?> signatures = new(ReferenceEqualityComparer.Instance);

    internal AbiSignature? Signature(Call call)
    {
        if (!signatures.TryGetValue(call, out var signature))
        {
            var candidates = call.Op?.Operand is MethodRef method ? [method]
                : call.Op is null && call.Target is Const target
                    ? facts.EntriesAt(target.Value).Select(e => e.Method).OfType<MethodRef>().Distinct().ToArray() : [];
            var exact = call.Arguments.OfType<Symbol>().Where(s => s.Kind == SymbolKind.Method).Select(s => (MethodRef)s.Value)
                .Where(m => candidates.Any(c => c.Method == m.Method)).Distinct().ToArray();
            var callee = call.Op is null && call.Target is Const address && facts.Unregistered.At(address.Value) is { } identity
                ? UnregisteredMethods.Resolve(identity, call, e => e, abi, out _)
                : exact is [var known] ? known : candidates is [var only] ? only : null;
            signature = callee is null ? null : abi.Classify(callee, out _);
            signatures[call] = signature;
        }
        return signature;
    }

    internal int? ArgumentSize(Call call, int index)
    {
        if (call.Op?.Kind == OpKind.WriteBarrier && index == 0) return 8;
        if (index >= call.Sources.Length || Signature(call) is not { } signature) return null;
        var register = call.Sources[index];
        var argument = signature.Arguments.Concat(signature.Return is { Passing: Passing.Indirect } result ? [result] : [])
            .FirstOrDefault(a => a.Pieces is [var piece] && piece.Register == register);
        var type = argument?.Passing == Passing.Indirect ? argument.Type : (argument?.Type as ByRefRef)?.Element;
        return type is not null && abi.Size(type) is > 0 and var size ? size : null;
    }
}
