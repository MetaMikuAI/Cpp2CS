namespace Cpp2CS.Tests.Execution;

internal sealed partial class NativeMachine
{
    private readonly List<(ulong Address, int Size)> pendingWrites = [];

    /// <summary>Unicorn 的写钩子发生在写入前，value 只容纳 64 位；到块边界从内存读回全部字节，避免截断 q 写入。</summary>
    private void FlushWrites()
    {
        foreach (var (address, size) in pendingWrites)
        {
            var bytes = new byte[size];
            uc.Read(address, bytes);
            side.Logged(address, bytes);
        }
        pendingWrites.Clear();
    }

    private byte[] ReadLocation(Aapcs64Classifier.Location location, ulong? indirectAddress = null)
    {
        if (location.Indirect)
        {
            var pointer = indirectAddress ?? (location.StackOffset is { } slot
                ? side.Read64(uc.Reg(Unicorn.RegSp) + (ulong)slot) : GetPiece(location.Pieces[0]));
            var value = new byte[location.Shape.Size];
            side.Read(pointer, value);
            return value;
        }
        var bytes = new byte[location.Shape.Size];
        if (location.StackOffset is { } offset) side.Read(uc.Reg(Unicorn.RegSp) + (ulong)offset, bytes);
        else foreach (var piece in location.Pieces)
            StructAbi.Bytes(GetPiece(piece), piece.Width / 8).CopyTo(bytes, piece.Offset);
        return bytes;
    }

    private void PutLocation(Aapcs64Classifier.Location location, byte[] bytes, bool pointer = false)
    {
        if (location.Indirect && !pointer) throw new InvalidOperationException("间接值需要显式副本地址");
        if (location.StackOffset is { } offset) uc.Write(uc.Reg(Unicorn.RegSp) + (ulong)offset, bytes);
        else foreach (var piece in location.Pieces)
            SetPiece(piece, StructAbi.Bits(bytes.AsSpan(piece.Offset, piece.Width / 8)));
    }
}
