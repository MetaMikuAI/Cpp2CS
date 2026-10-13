using Cpp2CS.IR;
using Cpp2CS.Native;

public static class IntegerProjectionChecks
{
    public static void Run(Action<bool, string> check)
    {
        var word = new NativeValue(new InputBits("word", 32), "int32_t", new NameExpression("word"));
        var abi = word with { Bits = BitOps.Concat([word.Bits, new UnknownBits("upper", "ABI", 32)]) };
        check(IntegerProjection.Bits(abi) is null, "整数投影不把 ABI 未定义高位当成符号或零扩展");
        var zero = word with { Bits = BitOps.Concat([word.Bits, BitOps.Constant(0, 32)]) };
        check(IntegerProjection.Bits(zero) is OperationExpression { Operation: ValueOperation.IntegerCast, Type: "uint32_t" },
            "W 写入后的 64 位使用保留零扩展，即使原表达式为负 int");
        check(IntegerProjection.Bits(word with { Type = "Example_o*" }) is null && IntegerProjection.Bits(word with { Type = "float" }) is null,
            "引用和浮点值不能直接参与整数位运算");
        var wide = new NativeValue(new InputBits("wide", 64), "int64_t", new NameExpression("wide"));
        check(NativeValues.Slice(wide, 0, 32) is { Type: "int32_t", Expression: OperationExpression { Operation: ValueOperation.IntegerCast } },
            "整数低位切片在参数、返回及寄存器路径共用明确截断");
        check(NativeValues.Slice(new(BitOps.Constant(1, 64), "int64_t", new ConstantExpression(1)), 0, 8).Expression is ConstantExpression { Value: 1 },
            "窄常量保留常量身份及合法隐式转换，不提前变成有符号字节变量");
    }
}
