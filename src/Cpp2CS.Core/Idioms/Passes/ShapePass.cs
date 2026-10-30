using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class ShapePass
{
    /// <summary>表达式的形状：变量与符号以类别代替，只保留结构与常量偏移。</summary>
    internal static string Shape(Expr e, int depth = 0) => depth > 6 ? "…" : e switch
    {
        Const c => $"0x{c.Value:x}",
        Use or Ir.Entry => "v",
        Symbol s => s.Kind.ToString(),
        Load l => $"[{ShapePass.Shape(l.Address, depth + 1)}]",
        Binary b => $"({ShapePass.Shape(b.Left, depth + 1)} {b.Op} {ShapePass.Shape(b.Right, depth + 1)})",
        Ir.Convert c => ShapePass.Shape(c.Operand, depth + 1),
        _ => e.GetType().Name,
    };
}
