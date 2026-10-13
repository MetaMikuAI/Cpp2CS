using System.Numerics;

namespace Cpp2CS.Ir;

public sealed class MachineState
{
    public Dictionary<string, BigInteger> Slots { get; } = [];
    public Dictionary<ulong, byte> Memory { get; } = [];
    public List<string> Accesses { get; } = [];
    public List<WorldEvent> Events { get; } = [];
    public ExclusiveReservation? Reservation { get; set; }
    public Queue<bool> ExclusiveStoreDecisions { get; } = new();
    public Queue<ScheduledMemoryEvent> Schedule { get; } = new();
    public List<ScheduledMemoryEvent> AppliedSchedule { get; } = [];
    public Dictionary<ulong, bool> WritePermissions { get; } = [];
    public Dictionary<ulong, bool> CodeGuardedPages { get; } = [];
    public BigInteger ReadSlot(string slot) => Slots[slot];
}

public sealed record ExecutionResult(string Outcome, ulong? NextAddress, int? FaultOperation, int Choices,
    string? Event = null, ulong? ResumeAddress = null);

// 用于具体验证；Undefined 在本次执行取零，不能据此作静态常量传播。
public static class MirInterpreter
{
    public static BigInteger Mask(int width) => (BigInteger.One << width) - 1;
    public static BigInteger Signed(BigInteger bits, int width) => bits.TestBit(width - 1) ? bits - (BigInteger.One << width) : bits;
    private static bool TestBit(this BigInteger bits, int bit) => ((bits >> bit) & 1) != 0;

    public static ExecutionResult Execute(MirInstruction ir, MachineState state)
    {
        var values = new BigInteger[ir.Operations.Count];
        var choices = 0;
        for (var index = 0; index < ir.Operations.Count; index++)
        {
            var op = ir.Operations[index];
            var a = op.Inputs.Length > 0 ? values[op.Inputs[0].Id] : BigInteger.Zero;
            var b = op.Inputs.Length > 1 ? values[op.Inputs[1].Id] : BigInteger.Zero;
            var width = op.Result?.Width ?? 0;
            var value = BigInteger.Zero;
            switch (op.Code)
            {
                case OpCode.Constant: value = op.Immediate; break;
                case OpCode.ReadSlot:
                    value = state.ReadSlot(op.Slot!);
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
                case OpCode.Select: value = a != 0 ? b : values[op.Inputs[2].Id]; break;
                case OpCode.Undefined: choices++; break;
                case OpCode.Qarma5: value = Qarma64.Evaluate((ulong)a, (ulong)b, values[op.Inputs[2].Id]); break;
                case OpCode.CodeGuarded:
                    if (!state.CodeGuardedPages.TryGetValue((ulong)a >> 12, out var guarded))
                        return new("UnmodeledEnvironmentStop", null, index, choices, "guarded-page attribute is required");
                    value = guarded ? 1 : 0;
                    break;
                case OpCode.Float:
                case OpCode.FloatFused:
                {
                    var f = op.Floating!;
                    var floating = op.Code == OpCode.Float
                        ? FloatEvaluator.Evaluate(ir.Architecture, f, a, b, (uint)values[op.Inputs[2].Id])
                        : FloatEvaluator.EvaluateFused(ir.Architecture, f, a, b,
                            values[op.Inputs[2].Id], (uint)values[op.Inputs[3].Id]);
                    value = floating.Bits | (new BigInteger(floating.Flags) << f.ResultWidth) |
                        (new BigInteger(floating.TrapFlags) << (f.ResultWidth + 6));
                    break;
                }
                case OpCode.Guard:
                    if (a.IsZero) return new("UnmodeledFaultStop", null, index, choices, op.Detail);
                    break;
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
                        b = op.Code == OpCode.StoreIf ? values[op.Inputs[2].Id] : BigInteger.Zero;
                    }
                    var effect = MemoryEffects.Execute(op, state, a, b);
                    if (effect.Outcome is not null) return new(effect.Outcome, null, index, choices, effect.Reason);
                    value = effect.Value;
                    break;
                }
                default: throw new InvalidOperationException($"Unknown IR opcode {op.Code}");
            }
            if (op.Result is { } result) values[result.Id] = value & Mask(result.Width);
        }
        var exit = ir.Exit;
        var next = exit.Kind switch
        {
            ExitKind.Next => exit.Address,
            ExitKind.Jump => (ulong)values[exit.Target!.Value.Id],
            ExitKind.Branch => (ulong)values[(values[exit.Condition!.Value.Id] != 0 ? exit.Target : exit.Alternative)!.Value.Id],
            _ => (ulong?)null
        };
        return new(exit.Kind == ExitKind.Trap ? "Trap" : "Normal", next, null, choices,
            exit.Reason, exit.ResumeAddress);
    }
}
