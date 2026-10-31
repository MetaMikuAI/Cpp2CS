using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Tests;

internal static class MaskedJumpIndexCheck
{
    [Command("masked-jump-index", "窄枚举跳转表索引与同值范围检查", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var convention = new CallingConvention { StackPointer = Storage.Gpr(31), IntegerArguments = [], FloatArguments = [],
            IntegerResults = [], FloatResults = [], Clobbered = [] };
        foreach (var mode in new[] { "same", "register", "mask", "signed", "reverse" })
        {
            Expr Index(int register, ulong mask, int width) => new Binary(BinOp.And, new Read(Storage.Gpr(register), width), Expr.C(mask, width), width);
            var guard = new Block(0) { Statements = [new Assign(0, Storage.Gpr(8), Index(2, 255, 32)),
                new Branch(4, new Compare(mode == "signed" ? Cond.Sgt : mode == "reverse" ? Cond.Ule : Cond.Ugt,
                    new Read(Storage.Gpr(8), 32), Expr.C(3, 32)), mode == "reverse" ? 16UL : 32UL, mode == "reverse" ? 32UL : 16UL)] };
            var table = new Block(16);
            var count = JumpTables.Bound(convention, guard, table, Index(mode == "register" ? 3 : 2, mode == "mask" ? 127UL : 255UL, 64));
            a.Equal(mode is "same" or "reverse" ? 4 : (int?)null, count,
                "仅同寄存器同掩码的无符号上界证明查表范围");
        }
        return a.Finish("masked-jump-index");
    }
}
