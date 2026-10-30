using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Image;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Lifting;

namespace Cpp2CS.Tests;

internal static class InterfaceTailProofCheck
{
    [Command("interface-tail-proof", "接口尾调用的快慢路径、接收者、槽位和输入保留", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var receiver = new Use(new(Storage.Gpr(0), 0), 64);
        var other = new Use(new(Storage.Gpr(2), 0), 64);
        var slow = new Variable(Storage.Gpr(0), 1);
        var fast = new Variable(Storage.Gpr(0), 2);
        var merged = new Variable(Storage.Gpr(0), 3);
        var data = new Use(merged, 64);
        var lookup = new Call(0x1010, CallKind.Direct, Expr.C(0x2000, 64))
        {
            Arguments = [receiver, Expr.C(0x3000, 64), Expr.C(1, 32)],
            Results = [Storage.Gpr(0)], Defines = [slow],
        };
        var offset = new Load(new Use(new(Storage.Gpr(10), 1), 64), 32);
        Expr Address(Expr self, Expr index, int shift, int baseOffset) => new Binary(BinOp.Add,
            new Binary(BinOp.Add, new Load(self, 64), new Binary(BinOp.Shl,
                new Cpp2CS.Ir.Convert(ConvKind.SignExtend, index, 64), Expr.C((ulong)shift, 64), 64), 64), Expr.C((ulong)baseOffset, 64), 64);
        var plusSlot = new Binary(BinOp.Add, offset, Expr.C(1, 32), 32);
        var fastAddress = Address(receiver, plusSlot, 4, RuntimeLayout.ClassVtable);
        var info = new Load(new Binary(BinOp.Add, data, Expr.C(8, 64), 64), 64);
        var tail = new Call(0x1030, CallKind.TailIndirect, new Load(data, 64)) { Arguments = [receiver, info, other] };
        var block = new Block(0x1000);
        var function = new MachineFunction { Entry = 0x1000, Range = new(0x1000, 0x1040, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [block], UnresolvedIndirectJumps = 1 };
        HashSet<Call> Prove(Expr? address = null, Call? invoke = null, Call? helper = null, Variable[]? sources = null, bool recognized = true)
        {
            block.Statements = [helper ?? lookup, new Define(0x1020, fast, address ?? fastAddress),
                new Phi(0x1028, merged, sources ?? [slow, fast]), invoke ?? tail];
            return InterfaceTailProof.Find(function, c => recognized && ReferenceEquals(c, helper ?? lookup));
        }
        a.True(Prove().Contains(tail), "接口槽位先加到 offset 再缩放的快慢路径可证明");
        var indexRegister = new Variable(Storage.Gpr(9), 1);
        var summedRegister = new Variable(Storage.Gpr(9), 2);
        Prove(Address(receiver, new Use(summedRegister, 32), 4, RuntimeLayout.ClassVtable));
        block.Statements.InsertRange(0, [new Define(0x1000, indexRegister, new Cpp2CS.Ir.Convert(ConvKind.ZeroExtend, offset, 64)),
            new Define(0x1004, summedRegister, new Cpp2CS.Ir.Convert(ConvKind.ZeroExtend,
                new Binary(BinOp.Add, new Use(indexRegister, 32), Expr.C(1, 32), 32), 64))]);
        a.True(InterfaceTailProof.Find(function, c => ReferenceEquals(c, lookup)).Contains(tail),
            "SSA 的 32 位读取先截断零扩展快照，再按有符号 offset 形成地址");
        var proof = Prove(Address(receiver, offset, 4, RuntimeLayout.VtableMethodPointer(1)));
        a.True(proof.Contains(tail), "接口槽位合入常量偏移也可证明");
        a.True(NativeInputs.Reads(new(function, []), knownTail: proof.Contains) is { } reads
            && reads.Contains(receiver.Variable.Storage) && reads.Contains(other.Variable.Storage), "证明尾调用仍保留全部原生输入读取");
        a.True(NativeInputs.Reads(new(function, [])) is null, "缺少接口证明仍拒绝未知尾跳转");
        a.True(Prove(recognized: false).Count == 0, "任意函数返回不能冒充接口查找");
        a.True(Prove(helper: lookup with { Arguments = [other, lookup.Arguments[1], lookup.Arguments[2]] }).Count == 0, "慢路径接收者必须一致");
        a.True(Prove(Address(other, plusSlot, 4, RuntimeLayout.ClassVtable)).Count == 0, "快路径接收者必须一致");
        a.True(Prove(Address(receiver, new Binary(BinOp.Add, offset, Expr.C(2, 32), 32), 4, RuntimeLayout.ClassVtable)).Count == 0, "快慢路径槽位必须相同");
        a.True(Prove(Address(receiver, plusSlot, 3, RuntimeLayout.ClassVtable)).Count == 0, "错误的 vtable 步长不能证明");
        a.True(Prove(invoke: tail with { Arguments = [receiver, other] }).Count == 0, "必须同时传递同一条目的 MethodInfo");
        a.True(Prove(sources: [slow, fast, fast]).Count == 0, "额外入边不能借用两个来源的证明");
        a.True(Prove(Address(receiver, Expr.C(1, 32), 4, RuntimeLayout.ClassVtable)).Count == 0, "任意常量不能冒充接口偏移加载");
        return a.Finish("interface-tail-proof");
    }
}
