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
    public Queue<BigInteger> ChoiceInputs { get; } = new();
    public List<ChoiceObservation> ChoiceObservations { get; } = [];
    public BigInteger ReadSlot(string slot) => Slots[slot];
}

// 用于具体验证；未显式给出的 Undefined 取零仅代表一个执行见证。
public static class MirInterpreter
{
    public static BigInteger Mask(int width) => (BigInteger.One << width) - 1;
    public static BigInteger Signed(BigInteger bits, int width) => bits.TestBit(width - 1) ? bits - (BigInteger.One << width) : bits;
    private static bool TestBit(this BigInteger bits, int bit) => ((bits >> bit) & 1) != 0;

    public static ExecutionResult Execute(MirInstruction ir, MachineState state)
    {
        var errors = MirValidator.Validate(ir);
        if (errors.Count != 0) throw new InvalidDataException(string.Join("; ", errors));
        var values = new BigInteger[ir.Operations.Length];
        var choices = 0;
        var completedState = new StateToken(0);
        var operationEventStart = state.Events.Count;
        ExecutionResult Stopped(StopKind kind, string reason, int index)
        {
            var stop = new ExecutionStop(kind, reason, index, completedState, operationEventStart, state.Events.Count);
            return ExecutionResult.Stopped(stop, choices);
        }
        for (var index = 0; index < ir.Operations.Length; index++)
        {
            var op = ir.Operations[index];
            operationEventStart = state.Events.Count;
            var a = op.Inputs.Length > 0 ? values[op.Inputs[0].Id] : BigInteger.Zero;
            var b = op.Inputs.Length > 1 ? values[op.Inputs[1].Id] : BigInteger.Zero;
            var width = op.Result?.Width ?? 0;
            var value = BigInteger.Zero;
            switch (op.Code)
            {
                case OpCode.Constant: value = op.Immediate; break;
                case OpCode.ReadSlot:
                    if (!state.Slots.TryGetValue(op.Slot!, out value))
                        return Stopped(StopKind.MissingEnvironment, $"state slot is required: {op.Slot}", index);
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
                case OpCode.Undefined:
                    var explicitChoice = state.ChoiceInputs.TryDequeue(out value);
                    if (value < 0 || value > Mask(width)) throw new InvalidOperationException("Choice input exceeds declared width");
                    state.ChoiceObservations.Add(new(state.ChoiceObservations.Count, ir.Origin.Address, index,
                        op.Result!.Value, value, explicitChoice));
                    choices++;
                    break;
                case OpCode.Qarma5: value = Qarma64.Evaluate((ulong)a, (ulong)b, values[op.Inputs[2].Id]); break;
                case OpCode.CodeGuarded:
                    if (!state.CodeGuardedPages.TryGetValue((ulong)a >> 12, out var guarded))
                        return Stopped(StopKind.MissingEnvironment, "guarded-page attribute is required", index);
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
                    if (a.IsZero) return Stopped(op.StopKind!.Value, op.Detail!, index);
                    break;
                case OpCode.AtomicRmw:
                {
                    var effect = MemoryEffects.Atomic(op, state, (ulong)a, b, values[op.Inputs[2].Id]);
                    if (effect.Stop is { } stop) return Stopped(stop.Kind, stop.Reason, index);
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
                        b = op.Code == OpCode.StoreIf ? values[op.Inputs[2].Id] : BigInteger.Zero;
                    }
                    var effect = MemoryEffects.Execute(op, state, a, b);
                    if (effect.Stop is { } stop) return Stopped(stop.Kind, stop.Reason, index);
                    value = effect.Value;
                    break;
                }
                default: throw new InvalidOperationException($"Unknown IR opcode {op.Code}");
            }
            if (op.Result is { } result) values[result.Id] = value & Mask(result.Width);
            if (op.Flow is { } flow) completedState = flow.Output;
        }
        var exit = ir.Exit;
        var next = exit.Kind switch
        {
            ExitKind.Next => exit.Address,
            ExitKind.Jump => (ulong)values[exit.Target!.Value.Id],
            ExitKind.Branch => (ulong)values[(values[exit.Condition!.Value.Id] != 0 ? exit.Target : exit.Alternative)!.Value.Id],
            _ => (ulong?)null
        };
        return exit is TrapExit trap ? ExecutionResult.Trapped(trap.Boundary, choices, completedState)
            : ExecutionResult.Completed(next!.Value, choices, completedState);
    }
}
