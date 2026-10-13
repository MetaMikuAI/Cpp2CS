using System.Numerics;

namespace Cpp2CS.Ir;

public readonly record struct OperationStop(StopKind Kind, string Reason);
public readonly record struct OperationEvaluation(BigInteger Bits, OperationStop? Stop = null, int Choices = 0);

// 调用方验证 MIR 并提供按 Inputs 排列的位向量；本内核不解释局部 Value.Id 或 StateToken。
public static class MirOperationEvaluator
{
    public static BigInteger Mask(int width) => (BigInteger.One << width) - 1;
    public static BigInteger Signed(BigInteger bits, int width) => ((bits >> (width - 1)) & 1) != 0
        ? bits - (BigInteger.One << width) : bits;

    public static OperationEvaluation Evaluate(Architecture architecture, Operation op, ReadOnlySpan<BigInteger> inputs,
        MachineState state, InstructionOrigin origin, int operationIndex)
    {
        if (inputs.Length != op.Inputs.Length) throw new ArgumentException("Operation input count does not match MIR", nameof(inputs));
        var a = inputs.Length > 0 ? inputs[0] : BigInteger.Zero;
        var b = inputs.Length > 1 ? inputs[1] : BigInteger.Zero;
        var width = op.Result?.Width ?? 0;
        var value = BigInteger.Zero;
        var choices = 0;
        OperationEvaluation Stopped(StopKind kind, string reason) => new(BigInteger.Zero, new(kind, reason));
        switch (op.Code)
        {
            case OpCode.Constant: value = op.Immediate; break;
            case OpCode.ReadSlot:
                if (!state.Slots.TryGetValue(op.Slot!, out value))
                    return Stopped(StopKind.MissingEnvironment, $"state slot is required: {op.Slot}");
                if (value < 0 || value > Mask(width)) throw new InvalidOperationException($"State slot exceeds declared width: {op.Slot}");
                break;
            case OpCode.WriteSlot: state.Slots[op.Slot!] = a; break;
            case OpCode.Extract: value = a >> (int)op.Immediate; break;
            case OpCode.Concat: value = (a << op.Inputs[1].Width) | b; break;
            case OpCode.Zext: value = a; break;
            case OpCode.Sext: value = Signed(a, op.Inputs[0].Width); break;
            case OpCode.Add: value = a + b; break;
            case OpCode.Sub: value = a - b; break;
            case OpCode.Mul: value = a * b; break;
            case OpCode.UDiv: value = b.IsZero ? 0 : a / b; break;
            case OpCode.SDiv: value = b.IsZero ? 0 : Signed(a, width) / Signed(b, width); break;
            case OpCode.And: value = a & b; break;
            case OpCode.Or: value = a | b; break;
            case OpCode.Xor: value = a ^ b; break;
            case OpCode.Not: value = ~a; break;
            case OpCode.Shl: value = b >= width ? 0 : a << (int)b; break;
            case OpCode.Shr: value = b >= width ? 0 : a >> (int)b; break;
            case OpCode.Sar: value = b >= width ? (Signed(a, width) < 0 ? -1 : 0) : Signed(a, width) >> (int)b; break;
            case OpCode.Eq: value = a == b ? 1 : 0; break;
            case OpCode.Ult: value = a < b ? 1 : 0; break;
            case OpCode.Slt: value = Signed(a, op.Inputs[0].Width) < Signed(b, op.Inputs[1].Width) ? 1 : 0; break;
            case OpCode.Select: value = a != 0 ? b : inputs[2]; break;
            case OpCode.Undefined:
                var explicitChoice = state.ChoiceInputs.TryDequeue(out value);
                if (value < 0 || value > Mask(width)) throw new InvalidOperationException("Choice input exceeds declared width");
                state.ChoiceObservations.Add(new(state.ChoiceObservations.Count, origin.Address, operationIndex,
                    op.Result!.Value, value, explicitChoice));
                choices = 1;
                break;
            case OpCode.Qarma5: value = Qarma64.Evaluate((ulong)a, (ulong)b, inputs[2]); break;
            case OpCode.CodeGuarded:
                if (!state.CodeGuardedPages.TryGetValue((ulong)a >> 12, out var guarded))
                    return Stopped(StopKind.MissingEnvironment, "guarded-page attribute is required");
                value = guarded ? 1 : 0;
                break;
            case OpCode.Float:
            case OpCode.FloatFused:
            {
                var f = op.Floating!;
                var floating = op.Code == OpCode.Float
                    ? FloatEvaluator.Evaluate(architecture, f, a, b, (uint)inputs[2])
                    : FloatEvaluator.EvaluateFused(architecture, f, a, b, inputs[2], (uint)inputs[3]);
                value = floating.Bits | (new BigInteger(floating.Flags) << f.ResultWidth) |
                    (new BigInteger(floating.TrapFlags) << (f.ResultWidth + 6));
                break;
            }
            case OpCode.Guard:
                if (a.IsZero) return Stopped(op.StopKind!.Value, op.Detail!);
                break;
            case OpCode.AtomicRmw:
            {
                var effect = MemoryEffects.Atomic(op, state, (ulong)a, b, inputs[2]);
                if (effect.Stop is { } stop) return Stopped(stop.Kind, stop.Reason);
                value = effect.Value;
                break;
            }
            case OpCode.Load:
            case OpCode.Store:
            case OpCode.LoadIf:
            case OpCode.StoreIf:
            case OpCode.LoadExclusive:
            case OpCode.StoreExclusive:
            case OpCode.ClearExclusive:
            case OpCode.Barrier:
            case OpCode.Prefetch:
            case OpCode.WriteProbe:
            {
                if (op.Code is OpCode.LoadIf or OpCode.StoreIf)
                {
                    if (a.IsZero) break;
                    a = b;
                    b = op.Code == OpCode.StoreIf ? inputs[2] : BigInteger.Zero;
                }
                var effect = MemoryEffects.Execute(op, state, a, b);
                if (effect.Stop is { } stop) return Stopped(stop.Kind, stop.Reason);
                value = effect.Value;
                break;
            }
            default: throw new InvalidOperationException($"Unknown IR opcode {op.Code}");
        }
        return new(op.Result is { } result ? value & Mask(result.Width) : BigInteger.Zero, Choices: choices);
    }
}
