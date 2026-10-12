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
            int resultWidth = 0, uint? trapFlags = null)
        {
            if (resultWidth == 0) resultWidth = kind is FloatKind.Compare or FloatKind.CompareSignal ? 4 : width;
            var result = FloatEvaluator.Evaluate(arch, new(kind, width, resultWidth, rounding), a, b, control);
            if (result.Bits != expected || result.Flags != flags || result.TrapFlags != (trapFlags ?? flags))
                throw new InvalidOperationException($"FP {arch} {kind}/{width}->{resultWidth} {a:X},{b:X} control={control:X} rounding={rounding}: " +
                    $"got {result.Bits:X}/{result.Flags:X}/{result.TrapFlags:X}, expected {expected:X}/{flags:X}/{trapFlags ?? flags:X}");
            checks++;
        }

        const uint ix = FloatEvaluator.Inexact, uf = FloatEvaluator.Underflow,
            inv = FloatEvaluator.Invalid, dz = FloatEvaluator.DivideByZero,
            ov = FloatEvaluator.Overflow, den = FloatEvaluator.InputDenormal;
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
