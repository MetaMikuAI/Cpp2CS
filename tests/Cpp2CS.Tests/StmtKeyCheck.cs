using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Tests;

internal static class StmtKeyCheck
{
    [Command("stmt-keys", "语句稳定键：同起点同址同种类按次序编号，尾复制的同址语句可区分", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var x = new Variable(Storage.Gpr(8), 1);
        var entry = new Block(0x100);
        var copy = new Block(0x100);
        var tail = new Block(0x200);
        entry.Statements.Add(new Define(0x100, x, Expr.C(1, 64)));
        entry.Statements.Add(new Define(0x100, new Variable(Storage.Gpr(9), 1), Expr.C(2, 64)));
        entry.Statements.Add(new Jump(0x104, tail.Start));
        // 尾复制得到的副本与原块同起点、同地址
        copy.Statements.Add(new Define(0x100, new Variable(Storage.Gpr(8), 2), Expr.C(1, 64)));
        tail.Statements.Add(new Return(0x200));
        var function = new MachineFunction { Entry = entry.Start, Range = new(entry.Start, 0x204, CodeRegion.Managed, default), Blocks = [entry, copy, tail] };
        var keys = StmtKey.Of(function);
        a.Equal(3, keys.Length, "每个块一组键");
        a.Equal(new StmtKey(0x100, 0x100, "Define", 0), keys[0][0], "同块同址同种类的第一条");
        a.Equal(new StmtKey(0x100, 0x100, "Define", 1), keys[0][1], "同块同址同种类的第二条");
        a.Equal(new StmtKey(0x100, 0x104, "Jump", 0), keys[0][2], "不同种类独立编号");
        a.Equal(new StmtKey(0x100, 0x100, "Define", 2), keys[1][0], "同起点的副本块接着编号");
        a.Equal(new StmtKey(0x200, 0x200, "Return", 0), keys[2][0], "其他块");
        a.True(keys.SelectMany(k => k).Distinct().Count() == keys.Sum(k => k.Length), "同一快照内键唯一");
        a.Equal("0x100/0x100/Define#1", keys[0][1].ToString(), "文本形式");
        return a.Finish("stmt-keys");
    }
}
