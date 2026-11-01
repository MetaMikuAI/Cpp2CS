using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Calls;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery;

/// <summary>
/// 方法的 ABI 边界：入口寄存器按本方法的机器签名对应到 IL 参数的片，调用定义的寄存器按被调用者的签名对应到返回值的片。
/// </summary>
internal sealed class MethodEnvironment(MethodRef method, MachineSignature signature, CallShapes shapes) : IValueEnvironment
{
    private readonly Dictionary<Call, CallShape> calls = new(ReferenceEqualityComparer.Instance);

    public MachineSignature Signature => signature;

    public CallShape Shape(Call call)
    {
        if (!calls.TryGetValue(call, out var shape)) calls[call] = shape = shapes.Of(call);
        return shape;
    }

    public Sym? Entry(SymTable syms, Storage storage)
    {
        foreach (var value in signature.Arguments)
            foreach (var piece in value.Pieces)
            {
                if (piece.Register != storage) continue;
                return value.Transfer switch
                {
                    Transfer.Value => syms.Slice(syms.Arg(value.Index, ValueWidth(value)), piece.Offset * 8, piece.Width),
                    Transfer.Reference => syms.Arg(value.Index, 64),
                    _ => null,
                };
            }
        if (signature.MethodInfo is { } info && info.Register == storage)
            return syms.Entity(new Symbol(SymbolKind.Method, method));
        return null;
    }

    public Sym? CallResult(SymTable syms, Call call, int index, IReadOnlyList<Sym> arguments)
    {
        var storage = call.Results[index];
        if (call.Op is not null)
            return storage == Storage.Gpr(0) ? syms.Result(call, 0, 64) : null;
        if (Shape(call).Signature?.Return is not { Transfer: Transfer.Value } result) return null;
        foreach (var piece in result.Pieces)
            if (piece.Register == storage)
                return syms.Slice(syms.Result(call, 0, ValueWidth(result)), piece.Offset * 8, piece.Width);
        return null;
    }

    /// <summary>IL 值的位宽：已知大小时为整个值，否则为各片之和。</summary>
    internal static int ValueWidth(MachineValue value) => value.Size > 0 ? value.Size * 8 : value.Pieces.Max(p => p.Offset * 8 + p.Width);
}
