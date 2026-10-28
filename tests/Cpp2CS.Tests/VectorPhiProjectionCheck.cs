using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class VectorPhiProjectionCheck
{
    [Command("vector-phi", "向量汇合的分量位型、快照与拒绝边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var first = new Variable(Storage.Vec(0), 1);
        var second = new Variable(Storage.Vec(0), 2);
        var merged = new Variable(Storage.Vec(0), 3);
        Block[] Blocks(Expr left, Expr right) => [
            new(0x1000) { Statements = [new Define(0x1000, first, left)] },
            new(0x1010) { Statements = [new Define(0x1010, second, right)] },
            new(0x1020) { Statements = [new Phi(0x1020, merged, [first, second]), new Return(0x1024) { Value = new Use(merged, 128) }] },
        ];
        Expr Widen(Expr value) => new Ir.Convert(ConvKind.ZeroExtend, value, 128);
        foreach (var bits in new ulong[] { 0, ulong.MaxValue, 0x8000000000000000, 0x7f800000ff800000, 0x7fc012347f800001, 0x3f99999a3fc00000 })
        {
            var blocks = Blocks(Widen(Expr.C(bits, 64)), Expr.C(0, 128));
            a.Equal(1, VectorPhiProjection.Run(blocks), "两个分量各自汇合");
            for (var edge = 0; edge < 2; edge++)
            {
                var values = new Dictionary<Variable, UInt128>();
                var evaluator = new Evaluator();
                Expr? Resolve(Expr expression)
                {
                    if (expression is not Use use || !values.TryGetValue(use.Variable, out var value)) return null;
                    if (use.Width <= 64) return Expr.C((ulong)value, use.Width);
                    return new Insert(new Insert(Expr.C(0, 128), Expr.C((ulong)value, 64), 0), Expr.C((ulong)(value >> 64), 64), 64);
                }
                UInt128 Eval(Expr e) => evaluator.Eval(ExprMap.Map(e, Resolve));
                foreach (var definition in blocks[edge].Statements.OfType<Define>()) values[definition.Target] = Eval(definition.Value);
                foreach (var statement in blocks[2].Statements)
                    if (statement is Phi phi) values[phi.Target] = values[phi.Sources[edge]];
                    else if (statement is Define definition) values[definition.Target] = Eval(definition.Value);
                a.Equal(edge == 0 ? (UInt128)bits : 0, values[merged], "两条入边的全部 128 位保持一致，包含负零、无穷和 NaN 位型");
                a.True(evaluator.Failure is null, "分量求值无未知项");
            }
            a.Equal(0, VectorPhiProjection.Run(blocks), "已投影的汇合不重复拆分");
        }
        var load = new Define(0x1000, first, Widen(new Load(Expr.C(0x8000, 64), 64)));
        var snapshot = Blocks(load.Value, Expr.C(0, 128));
        snapshot[0].Statements[0] = load;
        snapshot[0].Statements.Add(new Store(0x1004, Expr.C(0x8000, 64), Expr.C(7, 64)));
        VectorPhiProjection.Run(snapshot);
        a.True(ReferenceEquals(load, snapshot[0].Statements[0]) && snapshot[0].Statements[^1] is Store,
            "原加载与后续写入位置不变，分量读取位于两者之间");
        a.Equal(1, snapshot.SelectMany(b => b.Statements).SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).OfType<Load>().Count(), "不会将一次加载拆成两次内存读取");
        foreach (var unsupported in new Expr[]
        {
            new Load(Expr.C(0x8000, 64), 128), new Use(new(Storage.Vec(1), 0), 128),
            new Unknown("被调用破坏", 128), new Ir.Convert(ConvKind.SignExtend, Expr.C(0, 64), 128),
            Widen(Expr.C(0, 32)), new Insert(Expr.C(0, 128), Expr.C(1, 64), 64),
        })
        {
            var blocks = Blocks(Widen(Expr.C(7, 64)), unsupported);
            var original = blocks.SelectMany(b => b.Statements).ToArray();
            a.Equal(0, VectorPhiProjection.Run(blocks), "未知高位、输入、破坏值和不同宽度不参与投影");
            a.True(original.SequenceEqual(blocks.SelectMany(b => b.Statements)), "拒绝的汇合完整保留");
        }
        var loop = Blocks(Widen(Expr.C(9, 64)), Expr.C(0, 128));
        loop[2].Statements[0] = new Phi(0x1020, merged, [first, merged]);
        a.Equal(1, VectorPhiProjection.Run(loop), "有已证初始值的循环汇合可按分量保留回边");
        var cycle = new Block(0x1000) { Statements = [new Phi(0x1000, first, [second]), new Phi(0x1000, second, [first])] };
        a.Equal(0, VectorPhiProjection.Run([cycle]), "无初始定义的环不提供高位证据");
        return a.Finish("vector-phi");
    }
}
