using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Ir;
using Cpp2CS.SemanticCore;

namespace Cpp2CS.Recovery;

internal static class RecoveryFloating
{
    public static bool IsFloating(OpCode code) => code is OpCode.Float or OpCode.FloatFused;
    public static bool IsEnvironmentSlot(string? slot) => slot is "fpcr" or "fpsr" or "mxcsr";

    // 验证原 MIR 的逐位状态更新，不能只凭指令名放行环境写入。
    public static string? Validate(MirInstruction instruction)
    {
        var floats = instruction.Operations.Where(operation => IsFloating(operation.Code)).ToArray();
        var environment = instruction.Operations.Where(operation => operation.Code is OpCode.ReadSlot or OpCode.WriteSlot && IsEnvironmentSlot(operation.Slot)).ToArray();
        if (floats.Length == 0) return environment.Length == 0 ? null : "显式读取或修改机器浮点控制与状态尚未投影";
        var arm = instruction.Architecture == Architecture.Arm64;
        var control = arm ? "fpcr" : "mxcsr";
        var status = arm ? "fpsr" : "mxcsr";
        var definitions = instruction.Operations.Where(operation => operation.Result is not null)
            .ToDictionary(operation => operation.Result!.Value.Id);
        foreach (var floating in floats)
        {
            var source = definitions[floating.Inputs[^1].Id];
            if (source.Code != OpCode.ReadSlot || source.Slot != control)
                return "浮点控制并非当前指令入口环境的直接读取";
        }
        var writes = environment.Where(operation => operation.Code == OpCode.WriteSlot).ToArray();
        if (writes.Length != 1 || writes[0].Slot != status) return "浮点指令未提供唯一的累积异常状态写入";
        var cache = new Dictionary<int, ImmutableHashSet<string>[]>();
        var actual = Bits(writes[0].Inputs[0]);
        int[] positions = arm ? [0, 1, 2, 3, 4, 7] : [0, 2, 3, 4, 5, 1];
        for (var bit = 0; bit < 32; bit++)
        {
            var expected = ImmutableHashSet.Create($"environment:{status}:{bit}");
            var flag = Array.IndexOf(positions, bit);
            if (flag >= 0)
                foreach (var floating in floats) expected = expected.Add($"flags:{floating.Result!.Value.Id}:{flag}");
            if (!actual[bit].SetEquals(expected)) return "浮点状态写入不等于原状态与本条指令异常位的逐位并集";
        }
        foreach (var operation in instruction.Operations)
        {
            if (IsFloating(operation.Code))
            {
                if (operation.Inputs.SkipLast(1).Any(Sensitive)) return "浮点数值操作数仍依赖机器控制或异常打包位";
                continue;
            }
            if (operation.Code == OpCode.Guard || operation.Code == OpCode.WriteSlot && operation.Slot == status) continue;
            if ((operation.Code == OpCode.WriteSlot || operation.Flow is not null) && operation.Inputs.Any(Sensitive))
                return "机器浮点控制或异常打包位流入了未恢复的可观察输出";
        }
        if (instruction.Exit.Target is { } target && Sensitive(target) || instruction.Exit.Condition is { } condition && Sensitive(condition))
            return "机器浮点控制或异常打包位流入了转移条件";
        return null;

        bool Sensitive(Value value) => Bits(value).Any(bits => bits.Any(token => token.StartsWith("environment:", StringComparison.Ordinal) ||
            token.StartsWith("flags:", StringComparison.Ordinal) || token.StartsWith("traps:", StringComparison.Ordinal)));
        ImmutableHashSet<string>[] Bits(Value value)
        {
            if (cache.TryGetValue(value.Id, out var found)) return found;
            var operation = definitions[value.Id];
            ImmutableHashSet<string>[] result;
            if (operation.Code == OpCode.Constant)
                result = Enumerable.Range(0, value.Width).Select(bit => (operation.Immediate & (BigInteger.One << bit)) == 0
                    ? ImmutableHashSet<string>.Empty : ImmutableHashSet.Create("one")).ToArray();
            else if (operation.Code == OpCode.ReadSlot)
                result = Enumerable.Range(0, value.Width).Select(bit => ImmutableHashSet.Create(
                    $"{(IsEnvironmentSlot(operation.Slot) ? "environment" : "slot")}:{operation.Slot}:{bit}")).ToArray();
            else if (IsFloating(operation.Code))
            {
                var width = operation.Floating!.ResultWidth;
                result = Enumerable.Range(0, value.Width).Select(bit => ImmutableHashSet.Create(bit < width
                    ? $"data:{value.Id}:{bit}" : bit < width + 6 ? $"flags:{value.Id}:{bit - width}" : $"traps:{value.Id}:{bit - width - 6}")).ToArray();
            }
            else if (operation.Code == OpCode.Extract)
                result = Bits(operation.Inputs[0]).Skip((int)operation.Immediate).Take(value.Width).ToArray();
            else if (operation.Code == OpCode.Zext)
                result = Bits(operation.Inputs[0]).Concat(Enumerable.Repeat(ImmutableHashSet<string>.Empty, value.Width - operation.Inputs[0].Width)).ToArray();
            else if (operation.Code == OpCode.Concat)
                result = Bits(operation.Inputs[1]).Concat(Bits(operation.Inputs[0])).ToArray();
            else if (operation.Code == OpCode.Or)
                result = Bits(operation.Inputs[0]).Zip(Bits(operation.Inputs[1]), (left, right) => left.Union(right)).ToArray();
            else if (operation.Code == OpCode.Shl && definitions[operation.Inputs[1].Id].Code == OpCode.Constant)
            {
                var shift = (int)BigInteger.Min(value.Width, definitions[operation.Inputs[1].Id].Immediate);
                result = Enumerable.Repeat(ImmutableHashSet<string>.Empty, shift).Concat(Bits(operation.Inputs[0])).Take(value.Width).ToArray();
            }
            else
            {
                var union = operation.Inputs.SelectMany(input => Bits(input)).Aggregate(ImmutableHashSet<string>.Empty, (set, bits) => set.Union(bits));
                result = Enumerable.Repeat(union.Add($"opaque:{value.Id}"), value.Width).ToArray();
            }
            cache.Add(value.Id, result);
            return result;
        }
    }

    public static BinaryFloatSpec Specification(Architecture architecture, FloatOperation source)
    {
        var arm = architecture == Architecture.Arm64;
        var kind = source.Kind switch
        {
            FloatKind.Add => BinaryFloatKind.Add, FloatKind.Sub => BinaryFloatKind.Sub,
            FloatKind.Mul => BinaryFloatKind.Mul, FloatKind.Div => BinaryFloatKind.Div,
            FloatKind.Sqrt => BinaryFloatKind.Sqrt, FloatKind.NegMul => BinaryFloatKind.NegMul,
            FloatKind.AbsDiff => BinaryFloatKind.AbsDiff, FloatKind.Convert => BinaryFloatKind.Convert,
            FloatKind.FromSigned => BinaryFloatKind.FromSigned, FloatKind.FromUnsigned => BinaryFloatKind.FromUnsigned,
            FloatKind.ToSigned => BinaryFloatKind.ToSigned, FloatKind.ToUnsigned => BinaryFloatKind.ToUnsigned,
            FloatKind.RoundIntegral => BinaryFloatKind.RoundIntegral, FloatKind.RoundIntegralExact => BinaryFloatKind.RoundIntegralExact,
            FloatKind.Compare => BinaryFloatKind.Compare, FloatKind.CompareSignal => BinaryFloatKind.CompareSignal,
            FloatKind.Min => arm ? BinaryFloatKind.Minimum : BinaryFloatKind.MinimumSecond,
            FloatKind.Max => arm ? BinaryFloatKind.Maximum : BinaryFloatKind.MaximumSecond,
            FloatKind.MinNumber => BinaryFloatKind.MinimumNumber, FloatKind.MaxNumber => BinaryFloatKind.MaximumNumber,
            FloatKind.MulAdd => BinaryFloatKind.MulAdd, FloatKind.MulSub => BinaryFloatKind.MulSub,
            FloatKind.NegMulAdd => BinaryFloatKind.NegMulAdd, FloatKind.NegMulSub => BinaryFloatKind.NegMulSub,
            _ => throw new ArgumentOutOfRangeException(nameof(source))
        };
        return new(kind, source.OperandWidth, source.Kind is FloatKind.Compare or FloatKind.CompareSignal ? 2 : source.ResultWidth,
            Rounding(source.Rounding), new()
            {
                NaN = arm ? BinaryNaNRule.FirstSignalingThenFirst : BinaryNaNRule.First,
                InvalidNaNNegative = !arm,
                SubnormalOutput = arm ? BinarySubnormalOutput.SignedZeroBeforeRounding : BinarySubnormalOutput.SignedZeroAfterRounding,
                DenormalException = arm ? BinaryDenormalException.WhenFlushed : BinaryDenormalException.OnNumericUse,
                Tininess = arm ? BinaryTininess.BeforeRounding : BinaryTininess.AfterRounding,
                FlushRaisesInexact = !arm,
                InvalidInteger = arm ? BinaryInvalidInteger.Saturate : BinaryInvalidInteger.Minimum
            }, source.FractionBits);
    }

    public static BinaryFloatRounding Rounding(FloatRounding rounding) => rounding switch
    {
        FloatRounding.Current or FloatRounding.TiesEven => BinaryFloatRounding.TiesEven,
        FloatRounding.TiesAway => BinaryFloatRounding.TiesAway, FloatRounding.PlusInfinity => BinaryFloatRounding.PlusInfinity,
        FloatRounding.MinusInfinity => BinaryFloatRounding.MinusInfinity, FloatRounding.TowardZero => BinaryFloatRounding.TowardZero,
        _ => throw new ArgumentOutOfRangeException(nameof(rounding))
    };
}
