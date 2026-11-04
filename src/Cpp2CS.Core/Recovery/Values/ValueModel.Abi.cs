using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Values;

public sealed partial class ValueModel
{
    /// <summary>调用实参的完整位来源；经指针传递时返回指针，按值传递时合并寄存器与栈单元。</summary>
    public Sym ArgumentContent(Call call, MachineValue value, IReadOnlyList<Sym> arguments)
    {
        var width = value.Transfer == Transfer.Value ? MethodEnvironment.ValueWidth(value) : 64;
        var pieces = new List<(int Bit, Sym Value)>();
        if (value.Transfer == Transfer.Value)
        {
            foreach (var piece in value.Pieces)
                if (call.ArgumentIndex(piece.Register) is var position and >= 0)
                    pieces.Add((piece.Offset * 8, Syms.Slice(arguments[position], 0, Math.Min(piece.Width, arguments[position].Width))));
            foreach (var access in call.Memory.Where(m => !m.Write && m.Value == value.Index))
                if (call.ArgumentIndex(access.Cell) is var cell and >= 0)
                    pieces.Add((access.ValueBit, Syms.Slice(arguments[cell], access.CellBit, access.Width)));
        }
        else if (call.ArgumentIndex(value.Pieces[0].Register) is var pointer and >= 0) return arguments[pointer];
        return pieces.Count == 0 ? Syms.Unknown("实参缺失", width) : Syms.Assemble(width, pieces);
    }

    /// <summary>调用读取的单元中属于一个逻辑值的内容；缺失单元不提供来源。</summary>
    public Sym? CellContent(Call call, MachineValue value, IReadOnlyList<Sym> arguments, bool write)
    {
        var accesses = call.Memory.Where(m => m.Write == write && m.Value == value.Index).ToArray();
        if (accesses.Length == 0) return null;
        var pieces = new List<(int Bit, Sym Value)>();
        foreach (var access in accesses)
        {
            var position = call.ArgumentIndex(access.Cell);
            if (position < 0) return null;
            if (access.ValueWidth != accesses[0].ValueWidth) return Syms.Unknown("位片 单元的逻辑值宽度不一致", accesses[0].ValueWidth);
            pieces.Add((access.ValueBit, Syms.Slice(arguments[position], access.CellBit, access.Width)));
        }
        return Syms.Assemble(accesses[0].ValueWidth, pieces);
    }

    /// <summary>返回位置按 ABI 对应到同一个逻辑值，不把寄存器间的空隙补成零。</summary>
    public Sym ReturnContent(Return ret, IReadOnlyList<Sym> operands, int width) => Syms.Assemble(width,
        ret.Pieces.Zip(operands.Skip(ret.Value is null ? 0 : 1)).Select(p => (p.First.Offset * 8, p.Second)));
}
