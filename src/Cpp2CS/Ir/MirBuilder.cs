using System.Collections.Immutable;
using System.Numerics;

namespace Cpp2CS.Ir;

public sealed class MirBuilder(Architecture architecture, InstructionOrigin origin, string rule)
{
    private readonly List<Operation> operations = [];
    private readonly List<SemanticObligation> annotations = [];
    private int nextValue;
    private int state;

    private void Append(OpCode code, Value? result, ImmutableArray<Value> inputs, OperationPayload? payload = null)
    {
        var spec = OperationSpecs.For(code);
        StateFlow? flow = spec.HasStateFlow ? new(new(state), new(++state)) : null;
        operations.Add(new(code, result, inputs, payload ?? NoPayload.Instance, flow));
    }

    private Value Emit(OpCode code, int width, ImmutableArray<Value> inputs, OperationPayload? payload = null)
    {
        var value = new Value(nextValue++, width);
        Append(code, value, inputs, payload);
        return value;
    }

    public Value Const(int width, ulong value) => Const(width, new BigInteger(value));
    public Value Const(int width, BigInteger value) => Emit(OpCode.Constant, width, [], new ImmediatePayload(value & ((BigInteger.One << width) - 1)));
    public Value Read(string slot, int width) => Emit(OpCode.ReadSlot, width, [], new SlotPayload(slot));
    public void Write(string slot, Value value) => Append(OpCode.WriteSlot, null, [value], new SlotPayload(slot));
    public Value Extract(Value value, int offset, int width) => Emit(OpCode.Extract, width, [value], new ImmediatePayload(offset));
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
    public Value Undefined(int width, string reason) => Emit(OpCode.Undefined, width, [], new ChoicePayload(reason));
    public Value Qarma5(Value data, Value modifier, Value key) => Emit(OpCode.Qarma5, 64, [data, modifier, key]);
    public Value CodeGuarded(Value address)
    {
        return Emit(OpCode.CodeGuarded, 1, [address]);
    }
    public Value Float(FloatOperation operation, Value a, Value b, Value control)
    {
        return Emit(OpCode.Float, operation.ResultWidth + 12, [a, b, control], new FloatPayload(operation));
    }
    public Value FusedFloat(FloatOperation operation, Value a, Value b, Value c, Value control)
    {
        return Emit(OpCode.FloatFused, operation.ResultWidth + 12, [a, b, c, control], new FloatPayload(operation));
    }
    public void Guard(Value condition, string reason, StopKind stopKind = StopKind.FaultBoundary)
    {
        Append(OpCode.Guard, null, [condition], new GuardPayload(stopKind, reason));
    }
    public void MarkNormalPathOnly(string reason, ObligationKind kind = ObligationKind.PartialState)
    {
        var obligation = new SemanticObligation(kind, reason);
        if (!annotations.Contains(obligation)) annotations.Add(obligation);
    }

    public Value Load(Value address, int width, MemoryOperation? memory = null)
    {
        return Emit(OpCode.Load, width, [address], new MemoryPayload(memory ?? new(MemoryOrder.Relaxed, 8, 0)));
    }

    public void Store(Value address, Value data, MemoryOperation? memory = null)
    {
        Append(OpCode.Store, null, [address, data], new MemoryPayload(memory ?? new(MemoryOrder.Relaxed, 8, 0)));
    }

    public Value AtomicRmw(Value address, Value operand, Value expected, AtomicKind kind)
    {
        return Emit(OpCode.AtomicRmw, operand.Width, [address, operand, expected], new AtomicPayload(new(kind)));
    }

    public Value LoadIf(Value condition, Value address, int width)
    {
        return Emit(OpCode.LoadIf, width, [condition, address]);
    }

    public void StoreIf(Value condition, Value address, Value data)
    {
        Append(OpCode.StoreIf, null, [condition, address, data]);
    }

    public Value LoadExclusive(Value address, int width, MemoryOperation memory)
    {
        return Emit(OpCode.LoadExclusive, width, [address], new MemoryPayload(memory));
    }

    public Value StoreExclusive(Value address, Value data, MemoryOperation memory)
    {
        return Emit(OpCode.StoreExclusive, 32, [address, data], new MemoryPayload(memory));
    }

    public void ClearExclusive()
    {
        Append(OpCode.ClearExclusive, null, []);
    }

    public void Barrier(BarrierOperation barrier)
    {
        Append(OpCode.Barrier, null, [], new BarrierPayload(barrier));
    }

    public void Prefetch(Value address, int hint)
    {
        Append(OpCode.Prefetch, null, [address], new ImmediatePayload(hint));
    }

    public void WriteProbe(Value address, int sizeBytes)
    {
        Append(OpCode.WriteProbe, null, [address], new ImmediatePayload(sizeBytes));
    }

    public MirInstruction Finish(MirExit exit)
    {
        return new(architecture, origin, rule, operations.ToImmutableArray(), exit with { State = new(state) },
            annotations.ToImmutableArray(), MachineProfile.For(architecture).Id);
    }
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
