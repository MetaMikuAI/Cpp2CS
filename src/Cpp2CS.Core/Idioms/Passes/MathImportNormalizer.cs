using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>libm 的有界栈出参调用；显式保留输出值及写入顺序。</summary>
internal static class MathImportNormalizer
{
    // C11 / POSIX modf：https://man7.org/linux/man-pages/man3/modf.3.html
    internal static Expr Fraction(Expr input, Expr integral)
    {
        var signedZero = new Select(new Compare(Cond.FEq, input, Expr.C(0, 64)), input,
            new Select(new Compare(Cond.FLt, input, Expr.C(0, 64)), Expr.C(1UL << 63, 64), Expr.C(0, 64), 64), 64);
        // 无穷也等于其截断结果；NaN 走相减，整数部分与小数部分都仍为 NaN。
        return new Select(new Compare(Cond.FEq, input, integral), signedZero, new Binary(BinOp.FSub, input, integral, 64), 64);
    }

    internal static bool Run(MachineFunction function, Func<Variable> fresh)
    {
        var changed = false;
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                // Bionic math.h：void sincosf(float, float* sin, float* cos)。原导入保留，不拆成近似表达式。
                if (block.Statements[i] is Call
                    {
                        Kind: CallKind.Direct, Op: { Kind: OpKind.Import, Operand: "sincosf" },
                        Arguments: [FrameAddress { Offset: <= -4 } sine, FrameAddress { Offset: <= -4 } cosine, var angle],
                        Results.Length: 0, Defines.Length: 0
                    } pair && angle.Width >= 32
                    && Math.Abs(sine.Offset - cosine.Offset) >= 4)
                {
                    var sin = fresh(); var cos = fresh();
                    block.Statements[i] = pair with
                    {
                        Op = new(OpKind.ImportOutPair, "sincosf"),
                        Arguments = [Fold.Convert(ConvKind.Truncate, angle, 32)],
                        Sources = [Storage.Vec(0)],
                        Results = [sin.Storage, cos.Storage],
                        Defines = [sin, cos]
                    };
                    block.Statements.InsertRange(i + 1, [new Store(pair.Address, sine, new Use(sin, 32)),
                        new Store(pair.Address, cosine, new Use(cos, 32))]);
                    i += 2;
                    changed = true;
                    continue;
                }
                if (block.Statements[i] is not Call
                    {
                        Kind: CallKind.Direct, Op: { Kind: OpKind.Import, Operand: "modf" },
                        Arguments: [FrameAddress { Offset: < 0 } frame, var operand],
                        Results: [var register], Defines: [{ } result]
                    } call || register != Storage.Vec(0)
                    || frame.Offset + 8 > 0 || operand.Width < 64) continue;
                var input = fresh(); var integral = fresh();
                var value = new Use(input, 64); var integer = new Use(integral, 64);
                block.Statements.RemoveAt(i);
                block.Statements.InsertRange(i, [
                    new Define(call.Address, input, Fold.Convert(ConvKind.Truncate, operand, 64)),
                    new Define(call.Address, integral, new Unary(UnOp.FTrunc, value, 64)),
                    new Store(call.Address, frame, integer),
                    new Define(call.Address, result, Fraction(value, integer)),
                ]);
                i += 3;
                changed = true;
            }
        return changed;
    }
}
