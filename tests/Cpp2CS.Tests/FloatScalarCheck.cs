using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Input;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class FloatScalarCheck
{
    [Command("float-unit", "标量清高位的使用闭包与拒绝边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var v = new Variable(Storage.Vec(0), 1);
        var address = new Use(new Variable(Storage.Gpr(0), 0), 64);
        IReadOnlyDictionary<Storage, int> Unknown(Call _) => new Dictionary<Storage, int>();
        foreach (var width in new[] { 32, 64 })
        {
            var load = new Load(address, width);
            var definition = new Define(0x1000, v, new Ir.Convert(ConvKind.ZeroExtend, load, 128));
            var read = new Use(v, width);
            var block = new Block(0x1000) { Statements = [definition, new Store(0x1004, address, read), new Return(0x1008) { Value = read }] };
            a.Equal(1, ScalarVectorNarrowing.Run([block], Unknown), $"{width} 位同宽低位使用可消除清高位");
            a.True(block.Statements[0] is Define d && ReferenceEquals(d.Value, load) && d.Address == definition.Address,
                "加载保留在原定义位置，不复制、不搬过后续内存写入");
            a.True(block.Statements[1] is Store { Value: Use } && block.Statements[2] is Return { Value: Use }, "使用继续读取 SSA 局部值");
            foreach (var useWidth in new[] { 16, 32, 64, 128 }.Where(w => w != width))
            {
                var rejected = new Block(0x1000) { Statements = [definition, new Return(0x1004) { Value = read with { Width = useWidth } }] };
                a.Equal(0, ScalarVectorNarrowing.Run([rejected], Unknown), $"{width} 位定义被以 {useWidth} 位读取时保留");
                a.True(ReferenceEquals(definition, rejected.Statements[0]), "拒绝时保留全部位型");
            }
            var phi = new Block(0x1010) { Statements = [new Phi(0x1010, new(Storage.Vec(0), 2), [v, new(Storage.Vec(0), 0)])] };
            var predecessor = new Block(0x1000) { Statements = [definition, new Store(0x1004, address, read)] };
            a.Equal(0, ScalarVectorNarrowing.Run([predecessor, phi], Unknown), "即使另有低位使用，φ 的隐含全宽使用仍阻止收窄");
            var escaping = new Block(0x1010) { Statements = [new Store(0x1010, address, new Use(v, 128))] };
            a.Equal(0, ScalarVectorNarrowing.Run([predecessor, escaping], Unknown), "其他块的 128 位写入阻止收窄");
            var call = new Call(0x1004, CallKind.Direct, Expr.C(0x2000, 64)) { Sources = [Storage.Vec(0)], Arguments = [new Use(v, 128)] };
            var caller = new Block(0x1000) { Statements = [definition, call] };
            a.Equal(0, ScalarVectorNarrowing.Run([caller], Unknown), "未知调用、HFA 及签名不一致不提供标量宽度");
            a.Equal(1, ScalarVectorNarrowing.Run([caller], _ => new Dictionary<Storage, int> { [Storage.Vec(0)] = width }), "已证签名仅观察低位");
            a.True(caller.Statements[1] is Call { Arguments: [Use u] } && u.Width == width, "调用实参带实际标量位宽");
            foreach (var bits in new ulong[] { 0, 1, 0x80000000, 0x7f800000, 0x7fc00001, 0x8000000000000000, 0x7ff0000000000000, 0x7ff8000000000001 })
            {
                var operand = Expr.C(bits, width);
                var projected = ScalarVectorNarrowing.Low(new Ir.Convert(ConvKind.ZeroExtend, operand, 128), width);
                a.True(projected is Const c && c.Width == width && c.Value == operand.Value, "低位投影保留零、负零、无穷和 NaN 的位型，不做数值转换");
            }
        }
        foreach (var original in new Expr[]
        {
            new Load(address, 128), new Insert(Expr.C(0, 128), Expr.C(1, 32), 64),
            new Ir.Convert(ConvKind.SignExtend, Expr.C(1, 32), 128),
            new Ir.Convert(ConvKind.ZeroExtend, Expr.C(1, 16), 128),
            new Intrinsic("dup", [Expr.C(1, 32)], 128),
            new Ir.Convert(ConvKind.ZeroExtend, new Intrinsic("vdup.32", [Expr.C(1, 32)], 64), 128),
        })
        {
            var block = new Block(0x1000) { Statements = [new Define(0x1000, v, original), new Return(0x1004) { Value = new Use(v, 32) }] };
            a.Equal(0, ScalarVectorNarrowing.Run([block], Unknown), "不处理真正 128 位值、插入、dup、符号扩展或半精度");
            a.True(block.Statements[0] is Define d && ReferenceEquals(original, d.Value), "范围外定义保持原样");
        }
        var source = new Variable(Storage.Gpr(2), 1);
        var widened = new Variable(Storage.Gpr(3), 1);
        var narrowed = new Variable(Storage.Gpr(4), 1);
        foreach (var width in new[] { 16, 32, 64 })
        {
            var copy = new Block(0x2000) { Statements = [
                new Define(0x2000, source, new Load(address, 32)),
                new Define(0x2004, widened, new Ir.Convert(ConvKind.ZeroExtend, new Use(source, 32), 64)),
                new Define(0x2008, narrowed, new Ir.Convert(ConvKind.Truncate, new Use(widened, 64), 32)),
                new Return(0x200c) { Value = new Use(narrowed, width) }] };
            ScalarVectorNarrowing.Run([copy], Unknown);
            a.True(copy.Statements[0] is Define { Value: Load }, "低位投影保留原加载及位置");
            a.True(copy.Statements[^1] is Return { Value: Use u } && u.Variable == (width <= 32 ? source : narrowed), "只穿透完全保留所读取低位的扩展与截断");
        }
        return a.Finish("float-unit");
    }
}
