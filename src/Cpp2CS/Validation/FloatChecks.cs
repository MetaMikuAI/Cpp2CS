using System.Numerics;
using Cpp2CS.Ir;

namespace Cpp2CS.Validation;

public static class FloatChecks
{
    public static int Run()
    {
        var checks = 0;
        void Check(Architecture arch, FloatKind kind, int width, ulong a, ulong b, ulong expected,
            uint flags = 0, uint control = 0, FloatRounding rounding = FloatRounding.Current,
            int resultWidth = 0, uint? trapFlags = null, int fractionBits = 0)
        {
            if (resultWidth == 0) resultWidth = kind is FloatKind.Compare or FloatKind.CompareSignal ? 4 : width;
            var result = FloatEvaluator.Evaluate(arch, new(kind, width, resultWidth, rounding, fractionBits), a, b, control);
            if (result.Bits != expected || result.Flags != flags || result.TrapFlags != (trapFlags ?? flags))
                throw new InvalidOperationException($"FP {arch} {kind}/{width}->{resultWidth} {a:X},{b:X} control={control:X} rounding={rounding}: " +
                    $"got {result.Bits:X}/{result.Flags:X}/{result.TrapFlags:X}, expected {expected:X}/{flags:X}/{trapFlags ?? flags:X}");
            checks++;
        }

        const uint ix = FloatEvaluator.Inexact, uf = FloatEvaluator.Underflow,
            inv = FloatEvaluator.Invalid, dz = FloatEvaluator.DivideByZero,
            ov = FloatEvaluator.Overflow, den = FloatEvaluator.InputDenormal;
        void Fused(FloatKind kind, int width, ulong a, ulong b, ulong c, ulong expected,
            uint flags = 0, uint control = 0x1F80)
        {
            var result = FloatEvaluator.EvaluateFused(Architecture.X64, new(kind, width, width), a, b, c, control);
            if (result.Bits != expected || result.Flags != flags || result.TrapFlags != flags)
                throw new InvalidOperationException($"FMA {kind}/{width} {a:X},{b:X},{c:X} control={control:X}: " +
                    $"got {result.Bits:X}/{result.Flags:X}/{result.TrapFlags:X}, expected {expected:X}/{flags:X}");
            checks++;
        }

        // (1 + 2^-p) * (1 - 2^-p) - 1 = -2^(-2p); rounding the product first loses the residual.
        Fused(FloatKind.MulAdd, 32, 0x3F800001, 0x3F7FFFFE, 0xBF800000, 0xA8800000);
        Fused(FloatKind.MulSub, 32, 0x3F800001, 0x3F7FFFFE, 0x3F800000, 0xA8800000);
        Fused(FloatKind.NegMulAdd, 32, 0x3F800001, 0x3F7FFFFE, 0x3F800000, 0x28800000);
        Fused(FloatKind.NegMulSub, 32, 0x3F800001, 0x3F7FFFFE, 0xBF800000, 0x28800000);
        Fused(FloatKind.MulAdd, 64, 0x3FF0000000000001, 0x3FEFFFFFFFFFFFFE, 0xBFF0000000000000, 0xB970000000000000);
        Fused(FloatKind.MulSub, 64, 0x3FF0000000000001, 0x3FEFFFFFFFFFFFFE, 0x3FF0000000000000, 0xB970000000000000);
        Fused(FloatKind.NegMulAdd, 64, 0x3FF0000000000001, 0x3FEFFFFFFFFFFFFE, 0x3FF0000000000000, 0x3970000000000000);
        Fused(FloatKind.NegMulSub, 64, 0x3FF0000000000001, 0x3FEFFFFFFFFFFFFE, 0xBFF0000000000000, 0x3970000000000000);
        // The final result is exact even though a separately rounded product would overflow.
        Fused(FloatKind.MulAdd, 32, 0x7F7FFFFF, 0x40000000, 0xFF7FFFFF, 0x7F7FFFFF);
        Fused(FloatKind.MulAdd, 64, 0x7FEFFFFFFFFFFFFF, 0x4000000000000000, 0xFFEFFFFFFFFFFFFF, 0x7FEFFFFFFFFFFFFF);
        // The tiny exact product is retained until the addition; only the final inexact flag applies.
        Fused(FloatKind.MulAdd, 32, 0x00800000, 0x00800000, 0x3F800000, 0x3F800000, ix);
        Fused(FloatKind.MulAdd, 64, 0x0010000000000000, 0x0010000000000000, 0x3FF0000000000000, 0x3FF0000000000000, ix);
        Fused(FloatKind.MulAdd, 32, 1, 0x3F800000, 0, 1, den);
        Fused(FloatKind.MulAdd, 32, 1, 0x3F800000, 0, 0, control: 0x1FC0);
        Fused(FloatKind.MulAdd, 32, 0x00800000, 0x3F000000, 0, 0, uf | ix, 0x9F80);
        Fused(FloatKind.MulAdd, 32, 0x00800000, 0x3F000000, 0, 0x00400000, uf, 0x9780);
        foreach (var kind in new[] { FloatKind.MulAdd, FloatKind.MulSub, FloatKind.NegMulAdd, FloatKind.NegMulSub })
        {
            Fused(kind, 32, 0xFFC00123, 0x7F800456, 0x7FC00789, 0xFFC00123, inv);
            Fused(kind, 32, 0x3F800000, 0xFFC00123, 0x7F800456, 0xFFC00123, inv);
            Fused(kind, 32, 0, 0x7F800000, 0xFFC00123, 0xFFC00123);
            Fused(kind, 32, 0, 0x7F800000, 0, 0xFFC00000, inv);
            Fused(kind, 32, 0, 0, 0, kind == FloatKind.NegMulSub ? 0x80000000UL : 0);
            Fused(kind, 32, 0, 0, 0, kind == FloatKind.MulAdd ? 0 : 0x80000000UL, control: 0x3F80);
        }
        foreach (var architecture in new[] { Architecture.Arm64, Architecture.X64 })
        {
            var control = architecture == Architecture.X64 ? 0x1F80U : 0;
            Check(architecture, FloatKind.Add, 32, 0x3F800000, 0x40000000, 0x40400000, control: control);
            Check(architecture, FloatKind.Sub, 64, 0x4008000000000000, 0x3FF0000000000000, 0x4000000000000000, control: control);
            Check(architecture, FloatKind.Mul, 32, 0x3FC00000, 0x40000000, 0x40400000, control: control);
            Check(architecture, FloatKind.Div, 32, 0x3F800000, 0x40400000, 0x3EAAAAAB, ix, control);
            Check(architecture, FloatKind.Div, 64, 0x3FF0000000000000, 0x4008000000000000, 0x3FD5555555555555, ix, control);
            Check(architecture, FloatKind.Sqrt, 32, 0x40000000, 0, 0x3FB504F3, ix, control);
            Check(architecture, FloatKind.Sqrt, 64, 0x4000000000000000, 0, 0x3FF6A09E667F3BCD, ix, control);
            Check(architecture, FloatKind.Sqrt, 64, 0x4010000000000000, 0, 0x4000000000000000, control: control);
            Check(architecture, FloatKind.Sqrt, 32, 0x80000000, 0, 0x80000000, control: control);
            Check(architecture, FloatKind.Add, 32, 0x80000000, 0x80000000, 0x80000000, control: control);
            Check(architecture, FloatKind.Add, 32, 0, 0x80000000, 0, control: control);
            Check(architecture, FloatKind.Add, 32, 0, 0x80000000, 0x80000000, control: control, rounding: FloatRounding.MinusInfinity);
            Check(architecture, FloatKind.Sub, 32, 0x3F800000, 0x3F800000, 0x80000000, control: control, rounding: FloatRounding.MinusInfinity);
            Check(architecture, FloatKind.Mul, 32, 0x80000000, 0x3F800000, 0x80000000, control: control);
            Check(architecture, FloatKind.Div, 32, 0x3F800000, 0x80000000, 0xFF800000, dz, control);
            Check(architecture, FloatKind.Div, 32, 0x7F800000, 0, 0x7F800000, control: control);
            Check(architecture, FloatKind.Add, 32, 0x3F800000, 0x33800000, 0x3F800000, ix, control);
            Check(architecture, FloatKind.Add, 32, 0x3F800001, 0x33800000, 0x3F800002, ix, control);
            Check(architecture, FloatKind.Add, 32, 0x3F800000, 0x33800000, 0x3F800001, ix, control, FloatRounding.PlusInfinity);
            Check(architecture, FloatKind.Add, 32, 0xBF800000, 0xB3800000, 0xBF800001, ix, control, FloatRounding.MinusInfinity);
            Check(architecture, FloatKind.Mul, 32, 0x7F7FFFFF, 0x40000000, 0x7F800000, ov | ix, control);
            Check(architecture, FloatKind.Mul, 32, 0x7F7FFFFF, 0x40000000, 0x7F7FFFFF, ov | ix, control, FloatRounding.TowardZero);
            Check(architecture, FloatKind.Mul, 32, 0xFF7FFFFF, 0x40000000, 0xFF7FFFFF, ov | ix, control, FloatRounding.PlusInfinity);
            Check(architecture, FloatKind.Mul, 32, 0x00800000, 0x3F000000, 0x00400000, control: control);
            Check(architecture, FloatKind.Mul, 32, 0x00800000, 0x34000000, 0x00000001, control: control);
            Check(architecture, FloatKind.Mul, 32, 0x00800000, 0x33800000, 0, uf | ix, control);
            Check(architecture, FloatKind.Mul, 32, 0x80800000, 0x33800000, 0x80000001, uf | ix, control, FloatRounding.MinusInfinity);
            Check(architecture, FloatKind.Compare, 32, 0, 0x80000000, 6, control: control);
            Check(architecture, FloatKind.Compare, 64, 0xBFF0000000000000, 0, 8, control: control);
            Check(architecture, FloatKind.Compare, 32, 0x7F800000, 0, 2, control: control);
            Check(architecture, FloatKind.Compare, 32, 0x7FC12345, 0, 3, control: control);
            Check(architecture, FloatKind.Compare, 32, 0x7F812345, 0, 3, inv, control);
            Check(architecture, FloatKind.CompareSignal, 32, 0x7FC12345, 0, 3, inv, control);
            Check(architecture, FloatKind.Convert, 32, 0x3F800001, 0, 0x3FF0000020000000, control: control, resultWidth: 64);
            Check(architecture, FloatKind.Convert, 64, 0x3FF0000010000000, 0, 0x3F800000, ix, control, resultWidth: 32);
            Check(architecture, FloatKind.Convert, 64, 0x380FFFFFE1000000, 0, 0x00800000, uf | ix, control, resultWidth: 32);
            Check(architecture, FloatKind.Convert, 32, 0xFFC12345, 0, 0xFFF82468A0000000, control: control, resultWidth: 64);
            Check(architecture, FloatKind.Convert, 64, 0x7FF0000000000001, 0, 0x7FC00000, inv, control, resultWidth: 32);
            Check(architecture, FloatKind.FromSigned, 32, 0xFFFFFFFF, 0, 0xBF800000, control: control);
            Check(architecture, FloatKind.FromSigned, 64, 0x8000000000000000, 0, 0xC3E0000000000000, control: control);
            Check(architecture, FloatKind.FromSigned, 32, 0x01000001, 0, 0x4B800000, ix, control);
            Check(architecture, FloatKind.ToSigned, 32, 0x3FC00000, 0, 2, ix, control);
            Check(architecture, FloatKind.ToSigned, 32, 0xBFC00000, 0, 0xFFFFFFFE, ix, control);
            Check(architecture, FloatKind.ToSigned, 32, 0xBFC00000, 0, 0xFFFFFFFF, ix, control, FloatRounding.TowardZero);
            Check(architecture, FloatKind.RoundIntegral, 32, 0xBF000000, 0, 0x80000000, control: control);
            Check(architecture, FloatKind.RoundIntegralExact, 32, 0x3FC00000, 0, 0x40000000, ix, control);

            var nan = architecture == Architecture.Arm64 ? 0x7FC00000UL : 0xFFC00000UL;
            Check(architecture, FloatKind.Mul, 32, 0x7F800000, 0, nan, inv, control);
            Check(architecture, FloatKind.Div, 32, 0, 0, nan, inv, control);
            Check(architecture, FloatKind.Sqrt, 32, 0xBF800000, 0, nan, inv, control);
            Check(architecture, FloatKind.Sub, 32, 0x7FC00123, 0x3F800000, 0x7FC00123, control: control);
        }

        Check(Architecture.Arm64, FloatKind.Add, 32, 0x7FC00011, 0xFF800022, 0xFFC00022, inv);
        Check(Architecture.X64, FloatKind.Add, 32, 0x7FC00011, 0xFF800022, 0x7FC00011, inv, 0x1F80);
        Check(Architecture.Arm64, FloatKind.Sub, 32, 0, 0xFFC12345, 0xFFC12345);
        Check(Architecture.Arm64, FloatKind.NegMul, 32, 0x7FC12345, 0x3F800000, 0xFFC12345);
        Check(Architecture.Arm64, FloatKind.AbsDiff, 32, 0xFFC12345, 0, 0x7FC12345);
        Check(Architecture.Arm64, FloatKind.Add, 32, 0xFF812345, 0, 0x7FC00000, inv, 1U << 25);
        Check(Architecture.Arm64, FloatKind.Min, 32, 0, 0x80000000, 0x80000000);
        Check(Architecture.Arm64, FloatKind.Max, 32, 0x80000000, 0, 0);
        Check(Architecture.Arm64, FloatKind.MinNumber, 32, 0x7FC12345, 0x3F800000, 0x3F800000);
        Check(Architecture.Arm64, FloatKind.MaxNumber, 32, 0x7F812345, 0x3F800000, 0x7FC12345, inv);
        Check(Architecture.X64, FloatKind.Min, 32, 0x80000000, 0, 0, control: 0x1F80);
        Check(Architecture.X64, FloatKind.Max, 32, 0, 0x80000000, 0x80000000, control: 0x1F80);
        Check(Architecture.X64, FloatKind.Min, 32, 0x7FC12345, 0x3F800000, 0x3F800000, inv, 0x1F80);
        Check(Architecture.X64, FloatKind.Max, 32, 0x3F800000, 0x7F812345, 0x7F812345, inv, 0x1F80);
        Check(Architecture.Arm64, FloatKind.Add, 32, 1, 0, 1);
        Check(Architecture.X64, FloatKind.Add, 32, 1, 0, 1, den, 0x1F80);
        Check(Architecture.Arm64, FloatKind.Add, 32, 1, 0x3F800000, 0x3F800000, den, 1U << 24);
        Check(Architecture.X64, FloatKind.Add, 32, 1, 0x3F800000, 0x3F800000, control: 0x1FC0);
        Check(Architecture.Arm64, FloatKind.Mul, 32, 0x00800000, 0x3F000000, 0, uf, 1U << 24, trapFlags: 0);
        Check(Architecture.Arm64, FloatKind.Mul, 32, 0x00800000, 0x3F000000, 0, uf, (1U << 24) | (1U << 11), trapFlags: 0);
        Check(Architecture.X64, FloatKind.Mul, 32, 0x00800000, 0x3F000000, 0, uf | ix, 0x9F80);
        Check(Architecture.X64, FloatKind.Mul, 32, 0x00800000, 0x3F000000, 0x00400000, uf, 0x9780);
        Check(Architecture.Arm64, FloatKind.Mul, 32, 0x00800000, 0x3F000000, 0x00400000, uf, 1U << 11);
        Check(Architecture.X64, FloatKind.ToSigned, 32, 1, 0, 0, ix, 0x1F80);
        Check(Architecture.X64, FloatKind.ToSigned, 32, 1, 0, 0, control: 0x1FC0);
        Check(Architecture.X64, FloatKind.ToSigned, 32, 0x7FC00000, 0, 0x80000000, inv, 0x1F80);
        Check(Architecture.Arm64, FloatKind.ToSigned, 32, 0x7FC00000, 0, 0, inv);
        Check(Architecture.Arm64, FloatKind.ToSigned, 32, 0x7F800000, 0, 0x7FFFFFFF, inv);
        Check(Architecture.Arm64, FloatKind.ToUnsigned, 32, 0xBF000000, 0, 0, ix, rounding: FloatRounding.TowardZero);
        Check(Architecture.Arm64, FloatKind.ToUnsigned, 32, 0xBF800000, 0, 0, inv);
        Check(Architecture.Arm64, FloatKind.FromUnsigned, 64, ulong.MaxValue, 0, 0x43F0000000000000, ix);
        Check(Architecture.Arm64, FloatKind.RoundIntegral, 32, 0x3F000000, 0, 0x3F800000, rounding: FloatRounding.TiesAway);
        Check(Architecture.Arm64, FloatKind.RoundIntegral, 32, 0xBF000000, 0, 0xBF800000, rounding: FloatRounding.TiesAway);

        Check(Architecture.Arm64, FloatKind.ToSigned, 32, 0x3FC00000, 0, 1536,
            rounding: FloatRounding.TowardZero, fractionBits: 10);
        Check(Architecture.Arm64, FloatKind.ToSigned, 32, 0xBFC00000, 0, 0xFFFFFA00,
            rounding: FloatRounding.TowardZero, fractionBits: 10);
        Check(Architecture.Arm64, FloatKind.ToSigned, 64, 0x3E70000000000000, 0, 1,
            rounding: FloatRounding.TowardZero, resultWidth: 32, fractionBits: 24);
        Check(Architecture.Arm64, FloatKind.ToSigned, 32, 0x3F000000, 0, 0x7FFFFFFF, inv,
            rounding: FloatRounding.TowardZero, fractionBits: 32);
        Check(Architecture.Arm64, FloatKind.ToSigned, 32, 0xBF000000, 0, 0x80000000,
            rounding: FloatRounding.TowardZero, fractionBits: 32);
        Check(Architecture.Arm64, FloatKind.ToUnsigned, 64, 0x3FE0000000000000, 0, 0x8000000000000000,
            rounding: FloatRounding.TowardZero, fractionBits: 64);
        Check(Architecture.Arm64, FloatKind.ToUnsigned, 32, 0xBF000000, 0, 0, inv,
            rounding: FloatRounding.TowardZero, fractionBits: 32);
        Check(Architecture.Arm64, FloatKind.ToSigned, 32, 0x7FC12345, 0, 0, inv,
            rounding: FloatRounding.TowardZero, fractionBits: 10);
        Check(Architecture.Arm64, FloatKind.ToSigned, 32, 1, 0, 0, ix,
            rounding: FloatRounding.TowardZero, resultWidth: 64, fractionBits: 64);
        Check(Architecture.Arm64, FloatKind.ToSigned, 32, 1, 0, 0, den, 1U << 24,
            FloatRounding.TowardZero, resultWidth: 64, fractionBits: 64);
        Check(Architecture.Arm64, FloatKind.FromSigned, 32, 1536, 0, 0x3FC00000, fractionBits: 10);
        Check(Architecture.Arm64, FloatKind.FromSigned, 32, 0xFFFFFA00, 0, 0xBFF8000000000000,
            resultWidth: 64, fractionBits: 10);
        Check(Architecture.Arm64, FloatKind.FromUnsigned, 64, 1, 0, 0x1F800000,
            resultWidth: 32, fractionBits: 64);
        Check(Architecture.Arm64, FloatKind.FromUnsigned, 64, ulong.MaxValue, 0, 0x3F800000, ix,
            resultWidth: 32, fractionBits: 64);
        Check(Architecture.Arm64, FloatKind.FromUnsigned, 64, ulong.MaxValue, 0, 0x3F7FFFFF, ix, 3U << 22,
            resultWidth: 32, fractionBits: 64);
        Check(Architecture.Arm64, FloatKind.FromSigned, 32, 0x01000001, 0, 0x3F800000, ix, fractionBits: 24);

        void ScaleContract(Architecture architecture, FloatOperation spec, bool expected)
        {
            Value a = new(0, spec.OperandWidth), b = new(1, spec.OperandWidth), control = new(2, 32);
            var operations = new Operation[]
            {
                new(OpCode.Constant, a, []), new(OpCode.Constant, b, []), new(OpCode.Constant, control, []),
                new(OpCode.Float, new Value(3, spec.ResultWidth + 12), [a, b, control], Floating: spec)
            };
            var ir = new MirInstruction(architecture, new("scale-check", 0x1000, 0, new byte[4]),
                "scale-check", operations, MirExit.Next(0x1004), SupportClass.Exact, []);
            if ((MirValidator.Validate(ir).Count == 0) != expected)
                throw new InvalidOperationException($"Fixed-point scale contract: {architecture} {spec}");
            checks++;
        }
        ScaleContract(Architecture.Arm64, new(FloatKind.FromSigned, 64, 32, FractionBits: 64), true);
        ScaleContract(Architecture.Arm64, new(FloatKind.FromUnsigned, 32, 64, FractionBits: 32), true);
        ScaleContract(Architecture.Arm64, new(FloatKind.FromSigned, 32, 64, FractionBits: 33), false);
        ScaleContract(Architecture.Arm64, new(FloatKind.FromUnsigned, 64, 32, FractionBits: 65), false);
        ScaleContract(Architecture.Arm64, new(FloatKind.ToSigned, 32, 64, FloatRounding.TowardZero, 64), true);
        ScaleContract(Architecture.Arm64, new(FloatKind.ToUnsigned, 64, 32, FloatRounding.TowardZero, 32), true);
        ScaleContract(Architecture.Arm64, new(FloatKind.ToSigned, 64, 32, FloatRounding.TowardZero, 33), false);
        ScaleContract(Architecture.Arm64, new(FloatKind.ToUnsigned, 32, 64, FloatRounding.TowardZero, 65), false);
        ScaleContract(Architecture.Arm64, new(FloatKind.ToSigned, 32, 32, FractionBits: 1), false);
        ScaleContract(Architecture.Arm64, new(FloatKind.FromSigned, 32, 32, FloatRounding.TowardZero, 1), false);
        ScaleContract(Architecture.Arm64, new(FloatKind.FromSigned, 32, 32, FractionBits: -1), false);
        ScaleContract(Architecture.Arm64, new(FloatKind.Add, 32, 32, FractionBits: 1), false);
        ScaleContract(Architecture.Arm64, new(FloatKind.Convert, 32, 64, FractionBits: 1), false);
        ScaleContract(Architecture.Arm64, new(FloatKind.Compare, 32, 4, FractionBits: 1), false);
        ScaleContract(Architecture.X64, new(FloatKind.FromSigned, 64, 32, FractionBits: 1), false);
        ScaleContract(Architecture.X64, new(FloatKind.ToSigned, 32, 64, FloatRounding.TowardZero, 1), false);
        ScaleContract(Architecture.Arm64, new(FloatKind.ToSigned, 32, 32, FloatRounding.TiesEven), true);
        ScaleContract(Architecture.X64, new(FloatKind.FromSigned, 32, 64), true);

        void FusedContract(Architecture architecture, FloatOperation spec, bool expected,
            int[]? inputWidths = null, int? resultWidth = null)
        {
            inputWidths ??= [spec.OperandWidth, spec.OperandWidth, spec.OperandWidth, 32];
            var operations = new List<Operation>();
            var inputs = new Value[inputWidths.Length];
            for (var i = 0; i < inputs.Length; i++)
            {
                inputs[i] = new(i, inputWidths[i]);
                operations.Add(new(OpCode.Constant, inputs[i], []));
            }
            operations.Add(new(OpCode.FloatFused, new Value(inputs.Length, resultWidth ?? spec.ResultWidth + 12), inputs, Floating: spec));
            var ir = new MirInstruction(architecture, new("fused-check", 0x1000, 0, new byte[4]),
                "fused-check", operations, MirExit.Next(0x1004), SupportClass.Exact, []);
            var errors = MirValidator.Validate(ir);
            if (expected ? errors.Count != 0 : !errors.Any(e => e.Contains("FloatFused", StringComparison.Ordinal)))
                throw new InvalidOperationException($"Fused floating contract: {architecture} {spec}; {string.Join("; ", errors)}");
            checks++;
        }
        foreach (var kind in new[] { FloatKind.MulAdd, FloatKind.MulSub, FloatKind.NegMulAdd, FloatKind.NegMulSub })
        {
            FusedContract(Architecture.X64, new(kind, 32, 32), true);
            FusedContract(Architecture.X64, new(kind, 64, 64), true);
            FusedContract(Architecture.Arm64, new(kind, 32, 32), false);
            FusedContract(Architecture.Arm64, new(kind, 64, 64), false);
            ScaleContract(Architecture.X64, new(kind, 32, 32), false);
            ScaleContract(Architecture.Arm64, new(kind, 32, 32), false);
        }
        foreach (var kind in Enum.GetValues<FloatKind>().Where(k => k is not (FloatKind.MulAdd or FloatKind.MulSub or FloatKind.NegMulAdd or FloatKind.NegMulSub)))
            FusedContract(Architecture.X64, new(kind, 32, 32), false);
        FusedContract(Architecture.X64, new((FloatKind)999, 32, 32), false);
        foreach (var rounding in Enum.GetValues<FloatRounding>().Where(r => r != FloatRounding.Current))
            FusedContract(Architecture.X64, new(FloatKind.MulAdd, 32, 32, rounding), false);
        FusedContract(Architecture.X64, new(FloatKind.MulAdd, 32, 32, (FloatRounding)999), false);
        FusedContract(Architecture.X64, new(FloatKind.MulAdd, 16, 16), false);
        FusedContract(Architecture.X64, new(FloatKind.MulAdd, 128, 128), false);
        FusedContract(Architecture.X64, new(FloatKind.MulAdd, 32, 64), false);
        FusedContract(Architecture.X64, new(FloatKind.MulAdd, 64, 32), false);
        FusedContract(Architecture.X64, new(FloatKind.MulAdd, 32, 32, FractionBits: 1), false);
        FusedContract(Architecture.X64, new(FloatKind.MulAdd, 32, 32, FractionBits: -1), false);
        foreach (var widths in new int[][] { [], [32], [32, 32], [32, 32, 32], [32, 32, 32, 32, 32],
                     [64, 32, 32, 32], [32, 64, 32, 32], [32, 32, 64, 32], [32, 32, 32, 64] })
            FusedContract(Architecture.X64, new(FloatKind.MulAdd, 32, 32), false, widths);
        FusedContract(Architecture.X64, new(FloatKind.MulAdd, 32, 32), false, resultWidth: 38);
        FusedContract(Architecture.X64, new(FloatKind.MulAdd, 32, 32), false, resultWidth: 32);

        // Independently known integer identities cover both signs, exact squares and format conversion.
        for (var value = -1024; value <= 1024; value++)
        {
            var integerBits = new BigInteger(value) & ((BigInteger.One << 32) - 1);
            var encoded = FloatEvaluator.Evaluate(Architecture.Arm64,
                new(FloatKind.FromSigned, 32, 64), integerBits, 0, 0);
            var decoded = FloatEvaluator.Evaluate(Architecture.Arm64,
                new(FloatKind.ToSigned, 64, 32), encoded.Bits, 0, 0);
            if (decoded.Bits != integerBits || encoded.Flags != 0 || decoded.Flags != 0)
                throw new InvalidOperationException($"Exact integer conversion {value}");
            checks++;
        }
        return checks;
    }
}
