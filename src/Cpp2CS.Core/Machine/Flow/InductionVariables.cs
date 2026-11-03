using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Flow;

/// <summary>双入边合流上的同宽递推：初值来自 Seed 边，另一条边每次增加 Step，运算按 Width 取模。</summary>
internal sealed record InductionVariable(Phi Phi, int Seed, Expr Initial, ulong Step, int Width);

internal static class InductionVariables
{
    /// <summary>只读取机器 SSA 的递推事实；初值的不变性与用途由使用方检查。</summary>
    public static InductionVariable? Read(Block block, Phi phi, int seed, Func<Expr, Expr?> definition)
    {
        var width = phi.Target.Width;
        if (block.Predecessors.Count != 2 || phi.Sources.Length != 2 || seed is not (0 or 1)
            || width is not (32 or 64) || phi.Sources.Any(s => s is null || s.Width != width)) return null;
        var input = new Use(phi.Sources[seed], width);
        var initial = definition(input) ?? input;
        if (initial.Width != width || definition(new Use(phi.Sources[1 - seed], width)) is not Binary
            { Op: BinOp.Add, Left: Use previous, Right: Const step } update
            || update.Width != width || previous.Width != width || previous.Variable != phi.Target || step.Width != width) return null;
        return new(phi, seed, initial, step.Value & Expr.Mask(width), width);
    }

    public static Phi? UnitCounter(Block block, int seed, int width, Func<Expr, Expr?> definition) =>
        block.Statements.OfType<Phi>().FirstOrDefault(phi => Read(block, phi, seed, definition) is
            { Initial: Const { Value: 0 }, Step: 1 } induction && induction.Width == width);
}
