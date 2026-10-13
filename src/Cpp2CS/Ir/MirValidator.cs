namespace Cpp2CS.Ir;

public static class MirValidator
{
    public static IReadOnlyList<string> Validate(MirInstruction ir)
    {
        List<string> errors = [];
        List<int> widths = [];
        var slots = StateLayout.For(ir.Architecture);
        var world = 0;
        if (!Enum.IsDefined(ir.Architecture)) errors.Add("unknown architecture");
        if (!Enum.IsDefined(ir.Support)) errors.Add("unknown support class");
        if (ir.Architecture == Architecture.Arm64 && (ir.Origin.Address & 3) != 0) errors.Add("unaligned ARM64 instruction address");
        if (ir.Origin.FileOffset < 0) errors.Add("negative file offset");
        if (ir.Origin.Bytes.Length is < 1 or > 15 || ir.Architecture == Architecture.Arm64 && ir.Origin.Bytes.Length != 4)
            errors.Add("invalid instruction byte length");
        if (string.IsNullOrWhiteSpace(ir.Origin.ImageId) || string.IsNullOrWhiteSpace(ir.Rule)) errors.Add("missing origin or semantic rule");
        foreach (var op in ir.Operations)
        {
            var arity = op.Code switch
            {
                OpCode.Constant or OpCode.ReadSlot or OpCode.Undefined => 0,
                OpCode.WriteSlot or OpCode.Extract or OpCode.Zext or OpCode.Sext or OpCode.Not or OpCode.Load or OpCode.Guard => 1,
                OpCode.Select or OpCode.Float => 3,
                _ => 2
            };
            if (!Enum.IsDefined(op.Code) || op.Inputs.Length != arity) { errors.Add($"invalid opcode or arity: {op.Code}"); continue; }
            var inputError = false;
            foreach (var input in op.Inputs)
            {
                if (input.Id < 0 || input.Id >= widths.Count || widths[input.Id] != input.Width) { errors.Add($"undefined or mismatched input v{input.Id}"); inputError = true; }
            }
            var produces = op.Code is not (OpCode.WriteSlot or OpCode.Store or OpCode.Guard);
            if (produces != op.Result.HasValue) errors.Add($"result contract: {op.Code}");
            var width = op.Result?.Width ?? 0;
            if (op.Result is { } result)
            {
                if (result.Id != widths.Count || width is < 1 or > 4096)
                {
                    errors.Add($"invalid result v{result.Id}:{width}");
                    return errors;
                }
                widths.Add(width);
            }
            if (inputError) continue;
            var a = arity > 0 ? op.Inputs[0].Width : 0;
            var b = arity > 1 ? op.Inputs[1].Width : 0;
            var valid = op.Code switch
            {
                OpCode.Constant => op.Immediate >= 0 && op.Immediate < (System.Numerics.BigInteger.One << width),
                OpCode.ReadSlot => op.Slot is not null && slots.TryGetValue(op.Slot, out var sw) && sw == width,
                OpCode.WriteSlot => op.Slot is not null && slots.TryGetValue(op.Slot, out var sw) && sw == a,
                OpCode.Extract => op.Immediate >= 0 && op.Immediate + width <= a,
                OpCode.Concat => width == a + b,
                OpCode.Zext or OpCode.Sext => width > a,
                OpCode.Not => width == a,
                OpCode.Eq or OpCode.Ult or OpCode.Slt => a == b && width == 1,
                OpCode.Select => a == 1 && b == op.Inputs[2].Width && width == b,
                OpCode.Shl or OpCode.Shr or OpCode.Sar => width == a,
                OpCode.UDiv or OpCode.SDiv => width == a && a == b,
                OpCode.Load => a == 64 && width % 8 == 0,
                OpCode.Store => a == 64 && b % 8 == 0,
                OpCode.Undefined => !string.IsNullOrWhiteSpace(op.Detail),
                OpCode.Guard => a == 1 && !string.IsNullOrWhiteSpace(op.Detail) && op.Immediate == 0 && op.Slot is null,
                OpCode.Float => ValidFloat(ir.Architecture, op, a, b, width),
                _ => width == a && a == b
            };
            if (!valid) errors.Add($"type rule: {op.Code}");
            if (op.Code != OpCode.Float && op.Floating is not null) errors.Add("non-float operation has floating specification");
            if (op.Code is OpCode.Load or OpCode.Store or OpCode.Guard)
            {
                if (op.WorldIn != world || op.WorldOut != world + 1 || op.Fault != FaultPolicy.StopUnmodeled)
                    errors.Add("broken World or fault edge");
                world++;
                if (ir.Support == SupportClass.Exact) errors.Add("effect claimed exact without modeled fault");
            }
            else if (op.WorldIn != -1 || op.WorldOut != -1 || op.Fault != FaultPolicy.None) errors.Add("pure/state op has World or fault fields");
        }
        bool ValidValue(Value? value, int width) => value is { } v && v.Width == width && v.Id >= 0 && v.Id < widths.Count && widths[v.Id] == width;
        var exitValid = ir.Exit.Kind switch
        {
            ExitKind.Next => ir.Exit.Target is null && ir.Exit.Condition is null && ir.Exit.Alternative is null && ir.Exit.Reason is null,
            ExitKind.Jump => ValidValue(ir.Exit.Target, 64) && ir.Exit.Condition is null && ir.Exit.Alternative is null && ir.Exit.Reason is null && ir.Exit.Address == 0,
            ExitKind.Branch => ValidValue(ir.Exit.Target, 64) && ValidValue(ir.Exit.Condition, 1) && ValidValue(ir.Exit.Alternative, 64) && ir.Exit.Reason is null && ir.Exit.Address == 0,
            ExitKind.Trap => !string.IsNullOrWhiteSpace(ir.Exit.Reason) && ir.Exit.ResumeAddress is not null && ir.Exit.Target is null && ir.Exit.Condition is null && ir.Exit.Alternative is null && ir.Exit.Address == 0,
            _ => false
        };
        if (!exitValid) errors.Add("invalid terminator");
        if (ir.Exit.Kind != ExitKind.Trap && ir.Exit.ResumeAddress is not null) errors.Add("non-trap terminator has resume address");
        if ((ir.Exit.Kind == ExitKind.Trap) != (ir.Support == SupportClass.ExceptionBoundaryOnly)) errors.Add("trap/support boundary mismatch");
        if (ir.Support == SupportClass.Exact && ir.Limitations.Count != 0 || ir.Support != SupportClass.Exact && ir.Limitations.Count == 0)
            errors.Add("support/limitations mismatch");
        return errors;
    }

    private static bool ValidFloat(Architecture architecture, Operation op, int a, int b, int width)
    {
        var f = op.Floating;
        if (f is null || !Enum.IsDefined(f.Kind) || !Enum.IsDefined(f.Rounding) ||
            !FloatEvaluator.ValidFractionBits(architecture, f) ||
            f.OperandWidth is not (32 or 64) || a != f.OperandWidth || b != a ||
            op.Inputs[2].Width != 32 || width != f.ResultWidth + 12 || op.Immediate != 0 ||
            op.Slot is not null || op.Detail is not null) return false;
        if (architecture == Architecture.X64 && f.Kind is FloatKind.MinNumber or FloatKind.MaxNumber or FloatKind.ToUnsigned)
            return false;
        if (f.Kind is FloatKind.Compare or FloatKind.CompareSignal)
            return f.ResultWidth == 4 && f.Rounding == FloatRounding.Current;
        if (f.ResultWidth is not (32 or 64)) return false;
        if (f.Kind is FloatKind.Convert or FloatKind.FromSigned or FloatKind.FromUnsigned or FloatKind.ToSigned or FloatKind.ToUnsigned)
            return true;
        return f.ResultWidth == f.OperandWidth;
    }
}
