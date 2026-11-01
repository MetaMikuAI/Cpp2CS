using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Calls;
using Cpp2CS.Recovery.Memory;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery;

/// <summary>
/// 方法的 ABI 边界：入口寄存器按本方法的机器签名对应到 IL 参数的片，调用定义的寄存器按被调用者的签名对应到返回值的片；
/// 局部内存单元的入口内容来自栈传入的实参或实参副本，调用写出的单元按 <see cref="CellAccess"/> 拼入写出的值。
/// </summary>
internal sealed class MethodEnvironment(MethodRef method, MachineSignature signature, CallShapes shapes) : IValueEnvironment
{
    private readonly Dictionary<Call, CallShape> calls = new(ReferenceEqualityComparer.Instance);

    public MachineSignature Signature => signature;
    public MemoryLayout Layout { get; set; } = new([]);

    public CallShape Shape(Call call)
    {
        if (!calls.TryGetValue(call, out var shape)) calls[call] = shape = shapes.Of(call);
        return shape;
    }

    public Sym? Entry(SymTable syms, Storage storage)
    {
        if (Layout.Of(storage) is { } cell) return Initial(syms, cell);
        if (signature.Return is { Transfer: Transfer.ResultBuffer } result && result.Pieces[0].Register == storage)
            return syms.Local(LocalSpace.Result, 0);
        foreach (var value in signature.Arguments)
            foreach (var piece in value.Pieces)
            {
                if (piece.Register != storage) continue;
                return value.Transfer switch
                {
                    Transfer.Value => syms.Slice(syms.Arg(value.Index, ValueWidth(value)), piece.Offset * 8, piece.Width),
                    Transfer.Reference => syms.Arg(value.Index, 64),
                    Transfer.Copy => syms.Local(LocalSpace.Copy(value.Index), 0),
                    Transfer.ResultBuffer => syms.Local(LocalSpace.Result, 0),
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
        if (Layout.Of(storage) is { } cell) return Written(syms, call, cell, arguments);
        if (call.Op is not null && !Shape(call).IsDispatch)
            return storage == Storage.Gpr(0) || call.Results.Length == 1 ? syms.Result(call, 0, 64) : null;
        if (Shape(call).Signature?.Return is not { Transfer: Transfer.Value } result) return null;
        foreach (var piece in result.Pieces)
            if (piece.Register == storage)
                return syms.Slice(syms.Result(call, 0, ValueWidth(result)), piece.Offset * 8, piece.Width);
        return null;
    }

    /// <summary>单元的入口内容：栈传入的实参、实参副本的对应字节，其余未定义。</summary>
    private Sym Initial(SymTable syms, Cell cell)
    {
        var bytes = new Sym?[cell.Size];
        if (cell.Space.Kind == LocalKind.Argument && signature.Arguments.FirstOrDefault(a => a.Index == cell.Space.Argument) is { Size: > 0 } copy)
            return Bytes(syms, cell, syms.Arg(copy.Index, copy.Size * 8), 0);
        if (cell.Space == LocalSpace.Frame)
            foreach (var value in signature.Arguments)
                foreach (var piece in value.Pieces.Where(p => p.Register.Bank == Bank.Stack))
                {
                    Sym content = value.Transfer == Transfer.Value
                        ? syms.Slice(syms.Arg(value.Index, ValueWidth(value)), piece.Offset * 8, piece.Width)
                        : syms.Local(LocalSpace.Copy(value.Index), 0);
                    for (var b = 0; b < content.Width / 8; b++)
                    {
                        var at = piece.Register.Index + b - cell.Start;
                        if (at >= 0 && at < cell.Size) bytes[at] = syms.Slice(content, b * 8, 8);
                    }
                }
        return syms.Concat(bytes.Select(b => b ?? syms.Undef(8)));
    }

    /// <summary>值 value 从 valueByte 字节起覆盖单元的部分。</summary>
    private static Sym Bytes(SymTable syms, Cell cell, Sym value, long valueByte)
    {
        var parts = new List<Sym>();
        for (var b = 0; b < cell.Size; b++)
        {
            var at = cell.Start - valueByte + b;
            parts.Add(at >= 0 && (at + 1) * 8 <= value.Width ? syms.Slice(value, (int)at * 8, 8) : syms.Undef(8));
        }
        return syms.Concat(parts);
    }

    /// <summary>调用之后的单元内容：调用读取的原内容（没有时未定义）拼入各次写出的值。</summary>
    private static Sym Written(SymTable syms, Call call, Cell cell, IReadOnlyList<Sym> arguments)
    {
        var position = Array.IndexOf(call.Sources, cell.Storage);
        var content = position >= 0 ? arguments[position] : syms.Undef(cell.Size * 8);
        foreach (var access in call.Memory.Where(m => m.Write && m.Cell == cell.Storage).OrderBy(m => m.CellBit))
        {
            var written = syms.Slice(syms.Out(call, access.Value, access.ValueWidth), access.ValueBit, access.Width);
            var parts = new List<Sym>();
            if (access.CellBit > 0) parts.Add(syms.Slice(content, 0, access.CellBit));
            parts.Add(written);
            var end = access.CellBit + access.Width;
            if (end < content.Width) parts.Add(syms.Slice(content, end, content.Width - end));
            content = syms.Concat(parts);
        }
        return content;
    }

    /// <summary>IL 值的位宽：已知大小时为整个值，否则为各片之和。</summary>
    internal static int ValueWidth(MachineValue value) => value.Size > 0 ? value.Size * 8 : value.Pieces.Max(p => p.Offset * 8 + p.Width);
}
