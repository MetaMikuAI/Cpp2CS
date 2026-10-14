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
        check(IntegerProjection.Bits(NativeValues.Slice(word, 7, 5)) is OperationExpression { Operation: ValueOperation.ExtractBits },
            "任意宽度的整数切片保留明确的掩码与位移");
        check(IntegerProjection.Extract(abi, 24, 16) is null && IntegerProjection.Extract(zero, 24, 16) is not null,
            "跨字边界的切片区分 ABI 未定义高位与已证明的高位零");
        var byteArgument = new NativeValue(BitOps.Concat([new InputBits("byte", 8), new UnknownBits("byte-upper", "ABI", 56)]), "uint8_t", new NameExpression("value"));
        check(NativeValues.Slice(NativeValues.Slice(byteArgument, 0, 32, byteArgument.Type), 0, 8) is { Type: "uint8_t", Expression: NameExpression },
            "经过较宽寄存器读取后仍可提取窄参数的已定义部分");
        var lowConstant = NativeValues.Slice(new(BitOps.Constant(-1, 64), "int64_t", new ConstantExpression(-1)), 0, 8);
        check(lowConstant.Type == "int8_t" && IntegerProjection.Bits(lowConstant with { Bits = BitOps.Concat([lowConstant.Bits, BitOps.Constant(0, 56)]) }) is
            OperationExpression { Operation: ValueOperation.IntegerCast, Type: "uint8_t" }, "窄负常量再次零扩展时按低位无符号值解释");
    }
}
