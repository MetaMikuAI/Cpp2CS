using Cpp2CS.Ir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class CallArgumentProjectionCheck
{
    [Command("call-argument-projection", "结构体调用片的填充位及内存快照边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var input = new Variable(Storage.Gpr(0), 0);
        var masked = new Variable(Storage.Gpr(1), 1);
        var copied = new Variable(Storage.Gpr(2), 1);
        var read = new Variable(Storage.Gpr(3), 1);
        var definitions = new Dictionary<Variable, Expr>
        {
            [masked] = new Binary(BinOp.And, new Use(input, 64), Expr.C(0xffffffff00000000, 64), 64),
            [copied] = new Use(masked, 64),
            [read] = new Load(new Use(input, 64), 64),
        };
        var a = new Assertions();
        a.Equal<Expr>(Expr.C(0, 32), CallArgumentProjection.Low(new Use(copied, 64), 32, definitions), "仅含填充位的副本恢复零值");
        a.Equal<Expr>(new Use(read, 32), CallArgumentProjection.Low(new Use(read, 64), 32, definitions), "内存读取保持原位置和快照");
        a.Equal<Expr>(new Use(masked, 64), CallArgumentProjection.Low(new Use(masked, 64), 64, definitions), "有效高位不丢弃");
        definitions[masked] = new Binary(BinOp.Or, Expr.C(0x123400000007, 64), Expr.C(0, 64), 64);
        a.Equal<Expr>(Expr.C(7, 32), CallArgumentProjection.Low(new Use(copied, 64), 32, definitions), "有效低位常量保留");
        definitions[masked] = new Use(copied, 64);
        a.True(CallArgumentProjection.Low(new Use(copied, 64), 32, definitions) is Use { Width: 32 }, "循环副本终止且不伪造常量");
        return a.Finish("call-argument-projection");
    }
}
