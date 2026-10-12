using System.Numerics;

namespace Cpp2CS.Ir;

public sealed class MirBuilder(Architecture architecture, InstructionOrigin origin, string rule)
{
    private readonly List<Operation> operations = [];
    private readonly List<string> limitations = [];
    private int nextValue;
    private int world;

    private Value Emit(OpCode code, int width, Value[] inputs, BigInteger immediate = default, string? slot = null, string? detail = null)
    {
        var value = new Value(nextValue++, width);
        operations.Add(new(code, value, inputs, immediate, slot, detail));
        return value;
    }

    public Value Const(int width, ulong value) => Const(width, new BigInteger(value));
    public Value Const(int width, BigInteger value) => Emit(OpCode.Constant, width, [], value & ((BigInteger.One << width) - 1));
    public Value Read(string slot, int width) => Emit(OpCode.ReadSlot, width, [], slot: slot);
    public void Write(string slot, Value value) => operations.Add(new(OpCode.WriteSlot, null, [value], Slot: slot));
    public Value Extract(Value value, int offset, int width) => Emit(OpCode.Extract, width, [value], offset);
    public Value Concat(Value high, Value low) => Emit(OpCode.Concat, high.Width + low.Width, [high, low]);
    public Value Zext(Value value, int width) => value.Width == width ? value : Emit(OpCode.Zext, width, [value]);
    public Value Sext(Value value, int width) => value.Width == width ? value : Emit(OpCode.Sext, width, [value]);
    public Value Trunc(Value value, int width) => value.Width == width ? value : Extract(value, 0, width);
    public Value Add(Value a, Value b) => Emit(OpCode.Add, a.Width, [a, b]);
    public Value Sub(Value a, Value b) => Emit(OpCode.Sub, a.Width, [a, b]);
    public Value Mul(Value a, Value b) => Emit(OpCode.Mul, a.Width, [a, b]);
    // 总函数：除零取零；有符号最小值除以 -1 保留原位模式。
    public Value UDiv(Value a, Value b) => Emit(OpCode.UDiv, a.Width, [a, b]);
    public Value SDiv(Value a, Value b) => Emit(OpCode.SDiv, a.Width, [a, b]);
    public Value And(Value a, Value b) => Emit(OpCode.And, a.Width, [a, b]);
    public Value Or(Value a, Value b) => Emit(OpCode.Or, a.Width, [a, b]);
    public Value Xor(Value a, Value b) => Emit(OpCode.Xor, a.Width, [a, b]);
    public Value Not(Value a) => Emit(OpCode.Not, a.Width, [a]);
    public Value Shl(Value a, Value b) => Emit(OpCode.Shl, a.Width, [a, b]);
    public Value Shr(Value a, Value b) => Emit(OpCode.Shr, a.Width, [a, b]);
    public Value Sar(Value a, Value b) => Emit(OpCode.Sar, a.Width, [a, b]);
    public Value Eq(Value a, Value b) => Emit(OpCode.Eq, 1, [a, b]);
    public Value Ult(Value a, Value b) => Emit(OpCode.Ult, 1, [a, b]);
    public Value Slt(Value a, Value b) => Emit(OpCode.Slt, 1, [a, b]);
    public Value Select(Value condition, Value yes, Value no) => Emit(OpCode.Select, yes.Width, [condition, yes, no]);
    public Value BoolNot(Value value) => Xor(value, Const(1, 1UL));
    public Value Undefined(int width, string reason) => Emit(OpCode.Undefined, width, [], detail: reason);
    public void MarkNormalPathOnly(string reason)
    {
        if (!limitations.Contains(reason)) limitations.Add(reason);
    }

    public Value Load(Value address, int width)
    {
        var value = new Value(nextValue++, width);
        operations.Add(new(OpCode.Load, value, [address], WorldIn: world, WorldOut: ++world, Fault: FaultPolicy.StopUnmodeled));
        MarkNormalPathOnly("memory fault outcome is an explicit unmodeled stop");
        return value;
    }

    public void Store(Value address, Value data)
    {
        operations.Add(new(OpCode.Store, null, [address, data], WorldIn: world, WorldOut: ++world, Fault: FaultPolicy.StopUnmodeled));
        MarkNormalPathOnly("memory fault outcome is an explicit unmodeled stop");
    }

    public MirInstruction Finish(MirExit exit) => new(architecture, origin, rule, operations.ToArray(), exit,
        limitations.Count == 0 ? SupportClass.Exact : SupportClass.NormalPathOnly, limitations.ToArray());
}

public static class Arithmetic
{
    public static (Value Result, Value Carry, Value Overflow) AddWithCarry(MirBuilder b, Value a, Value c, Value carry)
    {
        var wide = b.Add(b.Add(b.Zext(a, a.Width + 1), b.Zext(c, a.Width + 1)), b.Zext(carry, a.Width + 1));
        var result = b.Trunc(wide, a.Width);
        var overflow = b.Extract(b.And(b.Not(b.Xor(a, c)), b.Xor(a, result)), a.Width - 1, 1);
        return (result, b.Extract(wide, a.Width, 1), overflow);
    }

    public static Value Parity(MirBuilder b, Value value)
    {
        var bits = b.Trunc(value, 8);
        var folded = b.Xor(bits, b.Shr(bits, b.Const(8, 4UL)));
        folded = b.Xor(folded, b.Shr(folded, b.Const(8, 2UL)));
        folded = b.Xor(folded, b.Shr(folded, b.Const(8, 1UL)));
        return b.BoolNot(b.Extract(folded, 0, 1));
    }
}
