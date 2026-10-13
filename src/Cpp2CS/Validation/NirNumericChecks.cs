using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Nir;
using Cpp2CS.SemanticCore;

namespace Cpp2CS.Validation;

public static class NirNumericChecks
{
    private static readonly BinaryFloatRules Rules = new();
    private static BinaryFloatSpec Spec(BinaryFloatKind kind, int width = 32, int? resultWidth = null,
        BinaryFloatRounding rounding = BinaryFloatRounding.TiesEven) => new(kind, width, resultWidth ?? width, rounding, Rules);
    private static void Require(bool condition, string label)
    {
        if (!condition) throw new InvalidOperationException("NIR numeric check failed: " + label);
    }
    public static int Run() => Boundaries() + HalfFormats() + IndependentArithmetic() + IndependentRounding() + Graphs() + DynamicControls();

    private static int Boundaries()
    {
        var checks = 0;
        void Check(BinaryFloatSpec spec, BigInteger expected, BinaryFloatException flags, params BigInteger[] input)
        {
            var result = BinaryFloatMath.Evaluate(spec, input);
            Require(result.Bits == expected && result.Exceptions == flags,
                $"{spec.Kind}/{spec.Rounding}/{string.Join(',', input)} expected={expected}/{flags} actual={result}");
            checks++;
        }
        const BinaryFloatException ix = BinaryFloatException.Inexact;
        const BinaryFloatException uf = BinaryFloatException.Underflow;
        const BinaryFloatException inv = BinaryFloatException.Invalid;
        Check(Spec(BinaryFloatKind.Add), 0x40400000, 0, 0x3f800000, 0x40000000);
        Check(Spec(BinaryFloatKind.Add), 0x3f800000, ix, 0x3f800000, 0x33800000);
        Check(Spec(BinaryFloatKind.Add, rounding: BinaryFloatRounding.TiesAway), 0x3f800001, ix, 0x3f800000, 0x33800000);
        Check(Spec(BinaryFloatKind.Add, rounding: BinaryFloatRounding.PlusInfinity), 0x3f800001, ix, 0x3f800000, 0x33800000);
        Check(Spec(BinaryFloatKind.Sub, rounding: BinaryFloatRounding.MinusInfinity), 0x80000000, 0, 0x3f800000, 0x3f800000);
        Check(Spec(BinaryFloatKind.Add), 0x80000000, 0, 0x80000000, 0x80000000);
        Check(Spec(BinaryFloatKind.Add), 0, 0, 0, 0x80000000);
        Check(Spec(BinaryFloatKind.Mul), 0x80000000, 0, 0, 0xbf800000);
        Check(Spec(BinaryFloatKind.Add), 0x7f800000, BinaryFloatException.Overflow | ix, 0x7f7fffff, 0x7f7fffff);
        Check(Spec(BinaryFloatKind.Add, rounding: BinaryFloatRounding.TowardZero), 0x7f7fffff, BinaryFloatException.Overflow | ix, 0x7f7fffff, 0x7f7fffff);
        Check(Spec(BinaryFloatKind.Div), 0x7f800000, BinaryFloatException.DivideByZero, 0x3f800000, 0);
        Check(Spec(BinaryFloatKind.Div), 0x7fc00000, inv, 0, 0);
        Check(Spec(BinaryFloatKind.Mul), 0x00400000, 0, 0x00800000, 0x3f000000);
        Check(Spec(BinaryFloatKind.Div), 0, uf | ix, 1, 0x40000000);
        Check(Spec(BinaryFloatKind.Div, rounding: BinaryFloatRounding.PlusInfinity), 1, uf | ix, 1, 0x40000000);
        Check(Spec(BinaryFloatKind.Add), 0x00800000, 0, 0x007fffff, 1);
        Check(Spec(BinaryFloatKind.Sqrt), 0x40000000, 0, 0x40800000);
        Check(Spec(BinaryFloatKind.Sqrt), 0x3fb504f3, ix, 0x40000000);
        Check(Spec(BinaryFloatKind.Sqrt), 0x80000000, 0, 0x80000000);
        Check(Spec(BinaryFloatKind.Sqrt), 0x7fc00000, inv, 0xbf800000);
        Check(Spec(BinaryFloatKind.Minimum), 0x80000000, 0, 0, 0x80000000);
        Check(Spec(BinaryFloatKind.Maximum), 0, 0, 0x80000000, 0);
        Check(Spec(BinaryFloatKind.MinimumSecond), 0, 0, 0x80000000, 0);
        Check(Spec(BinaryFloatKind.MinimumSecond), 0x7f800123, inv, 0x3f800000, 0x7f800123);
        Check(Spec(BinaryFloatKind.MinimumNumber), 0x3f800000, 0, 0x7fc00123, 0x3f800000);
        Check(Spec(BinaryFloatKind.MinimumNumber), 0x7fc00123, inv, 0x7f800123, 0x3f800000);
        Check(Spec(BinaryFloatKind.Add), 0xffc00042, inv, 0x7fc00123, 0xff800042);
        Check(Spec(BinaryFloatKind.Add) with { Rules = Rules with { NaN = BinaryNaNRule.First } }, 0x7fc00123, inv, 0x7fc00123, 0xff800042);
        Check(Spec(BinaryFloatKind.Add) with { Rules = Rules with { NaN = BinaryNaNRule.Canonical } }, 0x7fc00000, inv, 0x7fc00123, 0xff800042);
        Check(Spec(BinaryFloatKind.Sqrt) with { Rules = Rules with { InvalidNaNNegative = true } }, 0xffc00000, inv, 0xbf800000);
        Check(Spec(BinaryFloatKind.Compare, resultWidth: 2), 0, 0, 0, 0x80000000);
        Check(Spec(BinaryFloatKind.Compare, resultWidth: 2), 1, 0, 0xbf800000, 0x3f800000);
        Check(Spec(BinaryFloatKind.Compare, resultWidth: 2), 2, 0, 0x7f800000, 0xff800000);
        Check(Spec(BinaryFloatKind.Compare, resultWidth: 2), 3, 0, 0x7fc00123, 0);
        Check(Spec(BinaryFloatKind.CompareSignal, resultWidth: 2), 3, inv, 0x7fc00123, 0);
        Check(Spec(BinaryFloatKind.ToSigned), 0x7fffffff, inv, 0x7f800000);
        Check(Spec(BinaryFloatKind.ToSigned) with { Rules = Rules with { InvalidInteger = BinaryInvalidInteger.Minimum } }, 0x80000000, inv, 0x7f800000);
        Check(Spec(BinaryFloatKind.ToUnsigned), 0, inv, 0xbf800000);
        Check(Spec(BinaryFloatKind.ToSigned), 2, ix, 0x3fc00000);
        Check(Spec(BinaryFloatKind.ToSigned, rounding: BinaryFloatRounding.TowardZero), 1, ix, 0x3fc00000);
        Check(Spec(BinaryFloatKind.FromSigned), 0xbf800000, 0, 0xffffffff);
        Check(Spec(BinaryFloatKind.FromUnsigned) with { FractionBits = 8 }, 0x3f800000, 0, 256);
        Check(Spec(BinaryFloatKind.ToUnsigned) with { FractionBits = 8 }, 256, 0, 0x3f800000);
        Check(Spec(BinaryFloatKind.RoundIntegral), 0x40000000, 0, 0x3fc00000);
        Check(Spec(BinaryFloatKind.RoundIntegralExact), 0x40000000, ix, 0x3fc00000);
        Check(Spec(BinaryFloatKind.MulAdd), 0xa8800000, 0, 0x3f800001, 0x3f7ffffe, 0xbf800000);
        Check(Spec(BinaryFloatKind.MulSub), 0xa8800000, 0, 0x3f800001, 0x3f7ffffe, 0x3f800000);
        Check(Spec(BinaryFloatKind.NegMulAdd), 0x28800000, 0, 0x3f800001, 0x3f7ffffe, 0x3f800000);
        Check(Spec(BinaryFloatKind.NegMulSub), 0x28800000, 0, 0x3f800001, 0x3f7ffffe, 0xbf800000);
        Check(Spec(BinaryFloatKind.NegMul), 0xc0000000, 0, 0x3f800000, 0x40000000);
        Check(Spec(BinaryFloatKind.AbsDiff), 0x3f800000, 0, 0x3f800000, 0x40000000);
        var flush = Rules with { SubnormalInput = BinarySubnormalInput.SignedZero, DenormalException = BinaryDenormalException.WhenFlushed };
        Check(Spec(BinaryFloatKind.Add) with { Rules = flush }, 0, BinaryFloatException.InputDenormal, 1, 0);
        Check(Spec(BinaryFloatKind.Mul) with { Rules = Rules with { SubnormalOutput = BinarySubnormalOutput.SignedZeroBeforeRounding, FlushRaisesInexact = false } },
            0, uf, 0x00800000, 0x3f000000);
        Check(Spec(BinaryFloatKind.Mul) with { Rules = Rules with { SubnormalOutput = BinarySubnormalOutput.SignedZeroAfterRounding } },
            0, uf | ix, 0x00800000, 0x3f000000);
        Check(Spec(BinaryFloatKind.Mul) with { Rules = Rules with { ExactTinyUnderflow = true } }, 0x00400000, uf, 0x00800000, 0x3f000000);
        Check(Spec(BinaryFloatKind.Add) with { Rules = Rules with { DenormalException = BinaryDenormalException.OnNumericUse } },
            2, BinaryFloatException.InputDenormal, 1, 1);
        Check(Spec(BinaryFloatKind.Convert, 64, 32), 0x00800000, ix, 0x380ffffff0000000UL);
        Check(Spec(BinaryFloatKind.Convert, 64, 32) with { Rules = Rules with { Tininess = BinaryTininess.BeforeRounding } },
            0x00800000, uf | ix, 0x380ffffff0000000UL);
        return checks;
    }

    private static int HalfFormats()
    {
        var checks = 0;
        var up = Spec(BinaryFloatKind.Convert, 16, 32);
        var down = Spec(BinaryFloatKind.Convert, 32, 16);
        for (var bits = 0; bits <= ushort.MaxValue; bits++)
        {
            var widened = BinaryFloatMath.Evaluate(up, bits);
            var restored = BinaryFloatMath.Evaluate(down, widened.Bits);
            var nan = (bits & 0x7c00) == 0x7c00 && (bits & 0x03ff) != 0;
            Require(restored.Bits == (nan ? bits | 0x0200 : bits), $"binary16 roundtrip {bits:x4}");
            Require(widened.Exceptions == (nan && (bits & 0x0200) == 0 ? BinaryFloatException.Invalid : 0) && restored.Exceptions == 0,
                $"binary16 conversion flags {bits:x4}");
            checks += 2;
            if (nan) continue;
            var host = BitConverter.SingleToUInt32Bits((float)BitConverter.UInt16BitsToHalf((ushort)bits));
            Require(widened.Bits == host, $"binary16 independent conversion {bits:x4}");
            checks++;
        }
        return checks;
    }

    private static int IndependentArithmetic()
    {
        var checks = 0;
        var random = new Random(701204);
        byte[] bytes = new byte[8];
        foreach (var width in new[] { 32, 64 })
        foreach (var kind in new[] { BinaryFloatKind.Add, BinaryFloatKind.Sub, BinaryFloatKind.Mul, BinaryFloatKind.Div, BinaryFloatKind.Sqrt, BinaryFloatKind.MulAdd })
        {
            var spec = Spec(kind, width);
            for (var i = 0; i < 192; i++)
            {
                ulong Next()
                {
                    random.NextBytes(bytes);
                    var raw = BitConverter.ToUInt64(bytes);
                    return width == 32 ? (uint)raw & 0xff7fffffU : raw & 0xffefffffffffffffUL;
                }
                var a = Next(); var b = Next(); var c = Next();
                if (kind == BinaryFloatKind.Sqrt) a &= width == 32 ? 0x7fffffffUL : 0x7fffffffffffffffUL;
                ulong expected;
                if (width == 32)
                {
                    var x = BitConverter.UInt32BitsToSingle((uint)a); var y = BitConverter.UInt32BitsToSingle((uint)b); var z = BitConverter.UInt32BitsToSingle((uint)c);
                    var value = kind switch
                    {
                        BinaryFloatKind.Add => x + y, BinaryFloatKind.Sub => x - y, BinaryFloatKind.Mul => x * y,
                        BinaryFloatKind.Div => x / y, BinaryFloatKind.Sqrt => MathF.Sqrt(x), BinaryFloatKind.MulAdd => MathF.FusedMultiplyAdd(x, y, z),
                        _ => throw new InvalidOperationException()
                    };
                    if (float.IsNaN(value)) continue;
                    expected = BitConverter.SingleToUInt32Bits(value);
                }
                else
                {
                    var x = BitConverter.UInt64BitsToDouble(a); var y = BitConverter.UInt64BitsToDouble(b); var z = BitConverter.UInt64BitsToDouble(c);
                    var value = kind switch
                    {
                        BinaryFloatKind.Add => x + y, BinaryFloatKind.Sub => x - y, BinaryFloatKind.Mul => x * y,
                        BinaryFloatKind.Div => x / y, BinaryFloatKind.Sqrt => Math.Sqrt(x), BinaryFloatKind.MulAdd => Math.FusedMultiplyAdd(x, y, z),
                        _ => throw new InvalidOperationException()
                    };
                    if (double.IsNaN(value)) continue;
                    expected = BitConverter.DoubleToUInt64Bits(value);
                }
                BigInteger[] operands = spec.InputCount == 3 ? [a, b, c] : spec.InputCount == 2 ? [a, b] : [a];
                var actual = BinaryFloatMath.Evaluate(spec, operands);
                Require(actual.Bits == expected, $"independent host oracle {kind}/{width}/{a:x}/{b:x}/{c:x}: {actual.Bits:x} != {expected:x}");
                checks++;
            }
        }
        return checks;
    }

    private static int IndependentRounding()
    {
        var checks = 0;
        foreach (var mode in Enum.GetValues<BinaryFloatRounding>())
        foreach (var negative in new[] { false, true })
        foreach (var integer in new[] { 16_777_217U, 16_777_219U, 33_554_434U })
        {
            var signed = negative ? -(long)integer : integer;
            var hostNearest = (float)signed;
            var hostBits = BitConverter.SingleToUInt32Bits(hostNearest);
            var exact = (double)signed;
            var floor = hostNearest <= exact ? hostBits : negative ? hostBits + 1 : hostBits - 1;
            var ceil = hostNearest >= exact ? hostBits : negative ? hostBits - 1 : hostBits + 1;
            var expected = mode switch
            {
                BinaryFloatRounding.TiesEven => hostBits,
                BinaryFloatRounding.TiesAway => negative ? floor : ceil,
                BinaryFloatRounding.PlusInfinity => ceil,
                BinaryFloatRounding.MinusInfinity => floor,
                BinaryFloatRounding.TowardZero => negative ? ceil : floor,
                _ => throw new InvalidOperationException()
            };
            var actual = BinaryFloatMath.Evaluate(Spec(BinaryFloatKind.FromSigned, 64, 32, mode), new BigInteger(signed) & ulong.MaxValue);
            Require(actual.Bits == expected && actual.Exceptions == BinaryFloatException.Inexact, $"directed integer rounding {mode}/{signed}");
            checks++;
        }
        return checks;
    }

    private static int Graphs()
    {
        var a = NirValue.Bits(0, 32); var b = NirValue.Bits(1, 32); var e = NirValue.Effect(2);
        var value = NirValue.Bits(3, 32); var flags = NirValue.Bits(4, 6);
        var operation = new NirFloat(value, flags, Spec(BinaryFloatKind.Div), [a, b]);
        var function = new NirFunction("divide", new([a.Type, b.Type], [value.Type, flags.Type]), new(0),
            [new(new(0), [a, b, e], [operation], new NirReturn([value, flags], e))]) { Outcomes = NirOutcomes.Return };
        var module = new NirModule([function], [], [], []);
        Require(NirValidator.Validate(module).IsValid, "float SSA graph validates");
        var json = NirJson.Serialize(module);
        var restored = NirJson.Deserialize(json);
        Require(NirJson.Serialize(restored) == json && NirValidator.Validate(restored).IsValid, "float JSON roundtrip");
        var result = NirInterpreter.Execute(restored, "divide", [NirRuntimeValue.Integer(32, 0x3f800000), NirRuntimeValue.Integer(32, 0)]);
        Require(result.Status == NirExecutionStatus.Returned && result.Values[0].Bits == 0x7f800000 && result.Values[1].Bits == 2 && result.Events.Length == 0,
            "floating exceptions are explicit values without hidden state");
        Require(NirText.Format(restored).Contains("float.Div", StringComparison.Ordinal), "float readable export");
        var invalid = module with { Functions = [function with { Blocks = [function.Blocks[0] with { Operations = [operation with { Exceptions = NirValue.Bits(4, 5) }] }] }] };
        Require(!NirValidator.Validate(invalid).IsValid, "float exception width rejected");
        invalid = module with { Functions = [function with { Blocks = [function.Blocks[0] with { Operations = [operation with { Spec = operation.Spec with { Rounding = (BinaryFloatRounding)99 } }] }] }] };
        Require(!NirValidator.Validate(invalid).IsValid, "unknown rounding rejected");
        invalid = module with { Functions = [function with { Blocks = [function.Blocks[0] with { Operations = [operation with { Inputs = [a] }] }] }] };
        Require(!NirValidator.Validate(invalid).IsValid, "float arity rejected");
        invalid = module with { Functions = [function with { Blocks = [function.Blocks[0] with { Operations = [operation with { Inputs = [a, value] }] }] }] };
        Require(!NirValidator.Validate(invalid).IsValid, "float use must be dominated");
        var raised = NirValue.Bits(5, 1); var en = NirValue.Effect(6); var ef = NirValue.Effect(7);
        var checkedFunction = function with
        {
            Id = "checked-divide", Outcomes = NirOutcomes.Return | NirOutcomes.Fault,
            Blocks = [
                function.Blocks[0] with
                {
                    Operations = [operation, new NirPure(raised, NirPureCode.Extract, [flags], 1)],
                    Terminator = new NirBranch(raised, new(new(2), [e]), new(new(1), [e]))
                },
                new(new(1), [en], [], new NirReturn([value, flags], en)),
                new(new(2), [ef], [], new NirFault("FloatingDivideByZero", ef))
            ]
        };
        var checkedModule = new NirModule([checkedFunction], [], [], []);
        Require(NirValidator.Validate(checkedModule).IsValid, "explicit floating exception branch validates");
        Require(NirInterpreter.Execute(checkedModule, "checked-divide", [NirRuntimeValue.Integer(32, 0x3f800000), NirRuntimeValue.Integer(32, 0)]).Status == NirExecutionStatus.Faulted,
            "floating exception branch determines semantic fault");
        Require(NirInterpreter.Execute(checkedModule, "checked-divide", [NirRuntimeValue.Integer(32, 0x3f800000), NirRuntimeValue.Integer(32, 0x3f800000)]).Status == NirExecutionStatus.Returned,
            "ordinary floating result takes normal edge");

        var va = NirValue.Bits(0, 64); var vb = NirValue.Bits(1, 64);
        var next = 3;
        NirValue Allocate(int width) => NirValue.Bits(next++, width);
        var expansion = NirVectorMath.Floating(Spec(BinaryFloatKind.Div), 2, [va, vb], Allocate);
        var vectorFunction = new NirFunction("vector", new([va.Type, vb.Type], [expansion.Result.Type, expansion.Exceptions!.Value.Type]), new(0),
            [new(new(0), [va, vb, e], expansion.Operations, new NirReturn([expansion.Result, expansion.Exceptions.Value], e))]) { Outcomes = NirOutcomes.Return };
        module = new([vectorFunction], [], [], []);
        Require(NirValidator.Validate(module).IsValid, "expanded vector validates");
        restored = NirJson.Deserialize(NirJson.Serialize(module));
        result = NirInterpreter.Execute(restored, "vector", [NirRuntimeValue.Integer(64, 0x400000003f800000UL), NirRuntimeValue.Integer(64, 0x3f80000000000000UL)]);
        Require(result.Status == NirExecutionStatus.Returned && result.Values[0].Bits == 0x400000007f800000UL && result.Values[1].Bits == 2,
            "vector lane order and exception union");
        next = 3;
        expansion = NirVectorMath.Integer(NirPureCode.Add, 8, 8, [va, vb], Allocate);
        vectorFunction = new("bytes", new([va.Type, vb.Type], [expansion.Result.Type]), new(0),
            [new(new(0), [va, vb, e], expansion.Operations, new NirReturn([expansion.Result], e))]) { Outcomes = NirOutcomes.Return };
        module = new([vectorFunction], [], [], []);
        Require(NirValidator.Validate(module).IsValid, "integer vector validates");
        result = NirInterpreter.Execute(module, "bytes", [NirRuntimeValue.Integer(64, ulong.MaxValue), NirRuntimeValue.Integer(64, 0x0101010101010101UL)]);
        Require(result.Status == NirExecutionStatus.Returned && result.Values[0].Bits == 0, "integer lanes wrap independently");
        return 15;
    }

    private static int DynamicControls()
    {
        var a = NirValue.Bits(0, 32); var b = NirValue.Bits(1, 32); var rounding = NirValue.Bits(2, 3);
        var inputFlush = NirValue.Bits(3, 1); var outputFlush = NirValue.Bits(4, 1); var canonical = NirValue.Bits(5, 1);
        var e = NirValue.Effect(6); var value = NirValue.Bits(7, 32); var flags = NirValue.Bits(8, 6);
        var controls = new NirFloatControls(rounding, inputFlush, outputFlush, canonical);
        var spec = Spec(BinaryFloatKind.Add) with { Rules = Rules with
        {
            SubnormalOutput = BinarySubnormalOutput.SignedZeroBeforeRounding, FlushRaisesInexact = false,
            DenormalException = BinaryDenormalException.WhenFlushed
        } };
        var operation = new NirFloat(value, flags, spec, [a, b], controls);
        var function = new NirFunction("dynamic", new([a.Type, b.Type, rounding.Type, inputFlush.Type, outputFlush.Type, canonical.Type], [value.Type, flags.Type]), new(0),
            [new(new(0), [a, b, rounding, inputFlush, outputFlush, canonical, e], [operation], new NirReturn([value, flags], e))]) { Outcomes = NirOutcomes.Return };
        var module = new NirModule([function], [], [], []);
        Require(NirValidator.Validate(module).IsValid, "dynamic control types and SSA");
        var restored = NirJson.Deserialize(NirJson.Serialize(module));
        NirExecutionResult Execute(uint x, uint y, int mode, int fi = 0, int fo = 0, int nan = 0) => NirInterpreter.Execute(restored, "dynamic",
            [NirRuntimeValue.Integer(32, x), NirRuntimeValue.Integer(32, y), NirRuntimeValue.Integer(3, mode), NirRuntimeValue.Integer(1, fi),
             NirRuntimeValue.Integer(1, fo), NirRuntimeValue.Integer(1, nan)]);
        foreach (var mode in Enum.GetValues<BinaryFloatRounding>())
        {
            var result = Execute(0x3f800000, 0x33800000, (int)mode);
            Require(result.Status == NirExecutionStatus.Returned && result.Values[0].Bits ==
                (mode is BinaryFloatRounding.TiesAway or BinaryFloatRounding.PlusInfinity ? 0x3f800001 : 0x3f800000), "dynamic rounding selection");
        }
        var flushed = Execute(1, 0, 0, fi: 1);
        Require(flushed.Status == NirExecutionStatus.Returned && flushed.Values[0].Bits == 0 && flushed.Values[1].Bits == 32, "dynamic input flush");
        var preserved = Execute(1, 0, 0);
        Require(preserved.Values[0].Bits == 1 && preserved.Values[1].Bits == 0, "dynamic preserve overrides flush template");
        flushed = Execute(0x00400000, 0x00400000, 0, fo: 1);
        Require(flushed.Values[0].Bits == 0x00800000 && flushed.Values[1].Bits == 0, "normal result unaffected by output flush");
        flushed = Execute(1, 1, 0, fo: 1);
        Require(flushed.Values[0].Bits == 0 && flushed.Values[1].Bits == 8, "dynamic output flush");
        Require(Execute(0x7fc00123, 0, 0, nan: 1).Values[0].Bits == 0x7fc00000 && Execute(0x7fc00123, 0, 0).Values[0].Bits == 0x7fc00123,
            "dynamic canonical NaN preserves explicit off policy");
        Require(Execute(1, 1, 7).Status == NirExecutionStatus.ContractViolation, "invalid rounding is not silently defaulted");
        var invalid = module with { Functions = [function with { Blocks = [function.Blocks[0] with { Operations = [operation with { Spec = spec with { Rules = Rules } }] }] }] };
        Require(!NirValidator.Validate(invalid).IsValid, "dynamic output flush needs explicit stage");
        var exactOperation = operation with { Controls = controls with { ExactTinyUnderflow = canonical } };
        restored = NirJson.Deserialize(NirJson.Serialize(module with { Functions = [function with { Blocks = [function.Blocks[0] with { Operations = [exactOperation] }] }] }));
        var tiny = Execute(1, 1, 0, nan: 1);
        Require(tiny.Status == NirExecutionStatus.Returned && tiny.Values[0].Bits == 2 && tiny.Values[1].Bits == 8, "dynamic exact tiny underflow");
        return 14;
    }
}
