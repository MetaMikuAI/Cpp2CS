using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class SplitPass
{
    /// <summary>地址拆成（基址, 常量偏移）。</summary>
    internal static (Expr Basis, ulong Offset) Split(Expr address) => address is Binary { Op: BinOp.Add, Right: Const offset } b ? (b.Left, offset.Value) : (address, 0);
}
