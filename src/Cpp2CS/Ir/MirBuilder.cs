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
    public Value Qarma5(Value data, Value modifier, Value key) => Emit(OpCode.Qarma5, 64, [data, modifier, key]);
    public Value CodeGuarded(Value address)
    {
        var value = new Value(nextValue++, 1);
        operations.Add(new(OpCode.CodeGuarded, value, [address], WorldIn: world, WorldOut: ++world, Fault: FaultPolicy.StopUnmodeled));
        MarkNormalPathOnly("BTI entry checks require explicit guarded-page attributes; branch-target fault delivery is unmodeled");
        return value;
    }
    public Value Float(FloatOperation operation, Value a, Value b, Value control)
    {
        var value = new Value(nextValue++, operation.ResultWidth + 12);
        operations.Add(new(OpCode.Float, value, [a, b, control], Floating: operation));
        return value;
    }
    public Value FusedFloat(FloatOperation operation, Value a, Value b, Value c, Value control)
    {
        var value = new Value(nextValue++, operation.ResultWidth + 12);
        operations.Add(new(OpCode.FloatFused, value, [a, b, c, control], Floating: operation));
        return value;
    }
    public void Guard(Value condition, string reason)
    {
        operations.Add(new(OpCode.Guard, null, [condition], Detail: reason,
            WorldIn: world, WorldOut: ++world, Fault: FaultPolicy.StopUnmodeled));
        MarkNormalPathOnly(reason);
    }
    public void MarkNormalPathOnly(string reason)
    {
        if (!limitations.Contains(reason)) limitations.Add(reason);
    }

    public Value Load(Value address, int width, MemoryOperation? memory = null)
    {
        var value = new Value(nextValue++, width);
        operations.Add(new(OpCode.Load, value, [address], WorldIn: world, WorldOut: ++world, Fault: FaultPolicy.StopUnmodeled, Memory: memory));
        MarkNormalPathOnly("memory fault outcome is an explicit unmodeled stop");
        return value;
    }

    public void Store(Value address, Value data, MemoryOperation? memory = null)
    {
        operations.Add(new(OpCode.Store, null, [address, data], WorldIn: world, WorldOut: ++world, Fault: FaultPolicy.StopUnmodeled, Memory: memory));
        MarkNormalPathOnly("memory fault outcome is an explicit unmodeled stop");
    }

    public Value LoadIf(Value condition, Value address, int width)
    {
        var value = new Value(nextValue++, width);
        operations.Add(new(OpCode.LoadIf, value, [condition, address], WorldIn: world, WorldOut: ++world, Fault: FaultPolicy.StopUnmodeled));
        MarkNormalPathOnly("inactive load returns zero without an access; active memory faults stop explicitly");
        return value;
    }

    public void StoreIf(Value condition, Value address, Value data)
    {
        operations.Add(new(OpCode.StoreIf, null, [condition, address, data], WorldIn: world, WorldOut: ++world, Fault: FaultPolicy.StopUnmodeled));
        MarkNormalPathOnly("inactive store performs no access; active memory faults stop explicitly");
    }

    public Value LoadExclusive(Value address, int width, MemoryOperation memory)
    {
        var value = new Value(nextValue++, width);
        operations.Add(new(OpCode.LoadExclusive, value, [address], WorldIn: world, WorldOut: ++world,
            Fault: FaultPolicy.StopUnmodeled, Memory: memory));
        MarkNormalPathOnly("exclusive monitor and ordered events are explicit; memory faults and implementation monitor granules are unmodeled");
        return value;
    }

    public Value StoreExclusive(Value address, Value data, MemoryOperation memory)
    {
        var value = new Value(nextValue++, 32);
        operations.Add(new(OpCode.StoreExclusive, value, [address, data], WorldIn: world, WorldOut: ++world,
            Fault: FaultPolicy.StopUnmodeled, Memory: memory));
        MarkNormalPathOnly("exclusive-store success requires an external monitor decision; faults and weak-memory executions are unmodeled");
        return value;
    }

    public void ClearExclusive()
    {
        operations.Add(new(OpCode.ClearExclusive, null, [], WorldIn: world, WorldOut: ++world));
        MarkNormalPathOnly("local monitor clear is represented; implementation monitor granules are unmodeled");
    }

    public void Barrier(BarrierOperation barrier)
    {
        operations.Add(new(OpCode.Barrier, null, [], WorldIn: world, WorldOut: ++world, Barrier: barrier));
        MarkNormalPathOnly("barrier ordering and domain are retained as events; this interpreter is not a weak-memory solver");
    }

    public void Prefetch(Value address, int hint)
    {
        operations.Add(new(OpCode.Prefetch, null, [address], hint, WorldIn: world, WorldOut: ++world));
        MarkNormalPathOnly("prefetch hint is an explicit event; implementation-defined cache effects are outside the byte-state model");
    }

    public void WriteProbe(Value address, int sizeBytes)
    {
        operations.Add(new(OpCode.WriteProbe, null, [address], sizeBytes, WorldIn: world, WorldOut: ++world,
            Fault: FaultPolicy.StopUnmodeled));
        MarkNormalPathOnly("write permission probe requires an explicit environment response; fault delivery is unmodeled");
    }

    public MirInstruction Finish(MirExit exit)
    {
        if (exit.Kind == ExitKind.Trap)
        {
            MarkNormalPathOnly("exception event and resume address are represented; delivery and handler state are unmodeled");
            return new(architecture, origin, rule, operations.ToArray(), exit, SupportClass.ExceptionBoundaryOnly, limitations.ToArray());
        }
        return new(architecture, origin, rule, operations.ToArray(), exit,
            limitations.Count == 0 ? SupportClass.Exact : SupportClass.NormalPathOnly, limitations.ToArray());
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
