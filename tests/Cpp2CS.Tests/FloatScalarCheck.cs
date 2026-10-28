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
            var other = new Variable(Storage.Vec(0), 2);
            var joined = new Variable(Storage.Vec(0), 3);
            var initial = new Block(0x2000) { Statements = [definition] };
            var alternate = new Block(0x2010) { Statements = [new Define(0x2010, other,
                new Ir.Convert(ConvKind.ZeroExtend, Expr.C(0, width), 128))] };
            var merging = new Phi(0x2020, joined, [v, other]);
            var indirect = call with { Arguments = [new Use(joined, 128)] };
            var merge = new Block(0x2020) { Statements = [merging, indirect] };
            a.Equal(0, ScalarVectorNarrowing.Run([initial, alternate, merge], Unknown), "晚确认的调用签名前不收窄 φ 网");
            var projectedCall = indirect with { Arguments = [new Use(joined, width)] };
            merge.Statements[1] = projectedCall;
            var replacements = new List<(Define Previous, Define Replacement)>();
            a.Equal(2, ScalarVectorNarrowing.NarrowDefinitions([initial, alternate, merge], Unknown,
                replaced: (previous, replacement) => replacements.Add((previous, replacement))), "实参按签名投影后复用相同收窄证明");
            a.True(ReferenceEquals(merge.Statements[0], merging) && ReferenceEquals(merge.Statements[1], projectedCall), "定义收窄不再替换已分析的调用和 φ");
            a.True(replacements.Count == 2 && replacements.All(p => p.Previous.Target == p.Replacement.Target
                && p.Previous.Address == p.Replacement.Address && p.Replacement.Value.Width == width), "替换回调保留定义身份供诊断与帧证据迁移");
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
            new Ir.Convert(ConvKind.ZeroExtend, new Intrinsic("vdup.32", [new Use(v, 32)], 64), 128),
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
        int ReturnedPhi(int resultWidth, int readWidth = 32)
        {
            var result = new Variable(Storage.Vec(0), 2);
            var joined = new Variable(Storage.Vec(1), 2);
            var first = new Block(0x3000) { Statements = [new Define(0x3000, v,
                new Ir.Convert(ConvKind.ZeroExtend, Expr.C(0, 32), 128))] };
            var called = new Block(0x3010) { Statements = [new Call(0x3010, CallKind.Indirect, Expr.C(0x4000, 64))
                { Results = [Storage.Vec(0)], Defines = [result] }] };
            var merge = new Block(0x3020) { Statements = [new Phi(0x3020, joined, [v, result]),
                new Return(0x3024) { Value = new Use(joined, readWidth) }] };
            return ScalarVectorNarrowing.Run([first, called, merge], Unknown,
                _ => resultWidth > 0 ? new Dictionary<Storage, int> { [Storage.Vec(0)] = resultWidth } : []);
        }
        a.Equal(1, ReturnedPhi(32), "已知调用返回位宽可与常量分支汇合");
        a.Equal(0, ReturnedPhi(0), "未知调用返回值不提供宽度证明");
        a.Equal(0, ReturnedPhi(64), "分支返回位宽不一致时拒绝");
        a.Equal(0, ReturnedPhi(32, 128), "汇合后仍读取高位时拒绝");
        foreach (var laneWidth in new[] { 8, 16, 32, 64 })
            foreach (var totalWidth in new[] { 64, 128 })
                foreach (var bits in new ulong[] { 0, 1, ulong.MaxValue, 0x80000000, 0x7f800000, 0x7fc00123, 0x8000000000000000, 0x7ff0000000000000, 0x7ff8000000000123 })
                {
                    var duplicate = new Intrinsic($"vdup.{laneWidth}", [Expr.C(bits, laneWidth)], totalWidth);
                    var expanded = ScalarVectorNarrowing.RepeatedConstant(duplicate)!;
                    var evaluator = new Evaluator();
                    a.Equal(evaluator.Eval(duplicate), evaluator.Eval(expanded), "常量复制的所有道逐位相同，包含负零、无穷和 NaN");
                    a.True(evaluator.Failure is null && expanded.Width == totalWidth, "向量宽度与求值保持完整");
                }
        foreach (var rejected in new[]
        {
            new Intrinsic("vdup.32", [new Load(address, 32)], 128),
            new Intrinsic("vdup.32", [new Use(v, 32)], 128),
            new Intrinsic("vdup.32", [Expr.C(1, 64)], 128),
            new Intrinsic("vdup.32", [Expr.C(1, 32)], 256),
            new Intrinsic("vdup.24", [Expr.C(1, 24)], 128),
        }) a.True(ScalarVectorNarrowing.RepeatedConstant(rejected) is null, "拒绝非恒定值、未知道宽与不匹配位宽");
        return a.Finish("float-unit");
    }
}
