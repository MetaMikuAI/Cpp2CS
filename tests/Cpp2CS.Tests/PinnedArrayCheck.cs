using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class PinnedArrayCheck
{
    [Command("pinned-array", "固定数组取址的分支证明与拒绝边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var root = new Use(new Variable(Storage.Gpr(0), 0), 64);
        var array = new ArrayRef(new PrimitiveRef("byte"), 1) { IsVector = true };
        MachineFunction Function(Cond nullTest = Cond.Eq, Cond emptyTest = Cond.Eq, ulong offset = RuntimeLayout.ArrayData, ulong zeroValue = 0)
        {
            var zero = new Variable(Storage.Gpr(8), 1);
            var selected = new Variable(Storage.Gpr(8), 2);
            var pointer = new Variable(Storage.Gpr(8), 3);
            var length = new Variable(Storage.Gpr(9), 1);
            var entry = new Block(0x100);
            var nonnull = new Block(0x110);
            var join = new Block(0x120);
            entry.Statements = [new Define(entry.Start, zero, Expr.C(zeroValue, 64)),
                new Branch(entry.Start, new Compare(nullTest, root, Expr.C(0, 64)), join.Start, nonnull.Start)];
            nonnull.Statements = [new Define(nonnull.Start, length, new Load(new Binary(BinOp.Add, root, Expr.C(RuntimeLayout.ArrayMaxLength, 64), 64), 32)),
                new Define(nonnull.Start, selected, new Select(new Compare(emptyTest, new Use(length, 32), Expr.C(0, 32)), Expr.C(0, 64),
                    new Binary(BinOp.Add, root, Expr.C(offset, 64), 64), 64)), new Jump(nonnull.Start, join.Start)];
            join.Statements = [new Phi(join.Start, pointer, [zero, selected]), new Return(join.Start) { Value = new Use(pointer, 64) }];
            MachineFunction.AddEdge(entry, join); MachineFunction.AddEdge(entry, nonnull); MachineFunction.AddEdge(nonnull, join);
            return new() { Entry = entry.Start, Range = new(entry.Start, 0x130, CodeRegion.Managed, default), Blocks = [entry, nonnull, join] };
        }
        int Match(MachineFunction function) => PinnedArrayRecognition.Run(function, e => e == root ? array : null);
        var a = new Assertions();
        a.Equal(1, Match(Function()), "空引用与空数组路径均已证明");
        a.Equal(0, Match(Function(nullTest: Cond.Ne)), "不能翻转空引用分支");
        a.Equal(0, Match(Function(emptyTest: Cond.Ne)), "不能翻转空数组分支");
        a.Equal(0, Match(Function(offset: RuntimeLayout.ArrayData + 1)), "首地址必须精确匹配数组数据偏移");
        a.Equal(0, Match(Function(zeroValue: 1)), "无效分支必须返回零指针");
        a.Equal(0, PinnedArrayRecognition.Run(Function(), _ => null), "缺少数组类型证据不识别");
        var effect = Function();
        var store = new Store(0x114, Expr.C(0x2000, 64), Expr.C(7, 32));
        effect.Blocks[1].Statements.Insert(0, store);
        a.Equal(1, Match(effect), "取址识别不要求移走原有分支效果");
        a.True(effect.Blocks[1].Statements.Contains(store), "原分支写入保留原位");
        return a.Finish("pinned-array");
    }
}
