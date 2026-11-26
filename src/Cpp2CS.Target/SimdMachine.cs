using Cpp2CS.Snapshot;

namespace Cpp2CS.Target;

internal sealed partial class Machine
{
    Term Lane(int reg, int index, int size) => T.Slice(registers[32 + reg], index * size, size);
    Term Pack(int count, Func<int, Term> element) => T.Concat(Enumerable.Range(0, count).Select(element).ToArray());
    Term Insert(int reg, int index, Term value) => Pack(128 / value.Width, e => e == index ? value : Lane(reg, e, value.Width));

    void ApplyExtension(Instruction i, ulong pc)
    {
        int w = i.Width, s = i.Size, count = s == 0 ? 0 : w / s;
        Term N(int e) => Lane(i.N, e, s);
        Term M(int e) => Lane(i.M, e, s);
        Term D(int e) => Lane(i.D, e, s);
        Term Map(Func<int, Term> op) => Pack(count, op);
        Term Bool(Term bit) => T.SignExtend(bit, s);
        Term Float(Op op, Term x, Term y) => T.Operation(op, s, x, y);
        Term x, y, value;
        switch (i.Form)
        {
            case Form.ConditionalCompare: case Form.FloatConditionalCompare:
                var condition = Condition(i.Mode);
                comparison = null;
                if (i.Form == Form.ConditionalCompare)
                {
                    x = G(i.N, w); y = i.Vector ? K(i.M, w) : G(i.M, w);
                    bool sub = i.Name == "ccmp";
                    Nz(sub ? T.Sub(x, y) : T.Add(x, y));
                    registers[Abi.Carry] = sub ? T.Uge(x, y) : T.Operation(Op.AddCarry, 1, x, y);
                    registers[Abi.Overflow] = T.Operation(sub ? Op.SubOverflow : Op.AddOverflow, 1, x, y);
                }
                else Apply(new(Form.FloatCompare, "fcmp", w, N: i.N, M: i.M), pc);
                for (int j = 0; j < 4; j++)
                    registers[Abi.Negative + j] = T.Select(condition, registers[Abi.Negative + j], K((i.Imm >> (3 - j)) & 1, 1));
                return;
            case Form.Reverse:
                x = G(i.N, w);
                Put(i.D, Pack(count, e => T.Operation(i.Name == "rbit" ? Op.BitReverse : Op.ByteSwap, s, T.Slice(x, e * s, s))));
                return;
            case Form.RoundConvert:
                x = V(i.N, s);
                if (i.Shift != 0)
                {
                    double scale = Math.ScaleB(1.0, i.Shift);
                    x = Float(Op.FMul, x, K(s == 32 ? BitConverter.SingleToInt32Bits((float)scale) : BitConverter.DoubleToInt64Bits(scale), s));
                }
                else x = T.Opaque((int)(i.Name[4] == 'p' ? ArmOperation.RoundPositive : ArmOperation.RoundNegative), s, x);
                Put(i.D, T.Operation(i.Name.EndsWith('s') ? Op.FToSSaturate : Op.FToUSaturate, w, x)); return;
            case Form.SimdBinary: case Form.SimdIndexed:
                value = Map(e =>
                {
                    Term l = N(e), r = M(i.Form == Form.SimdIndexed ? i.Shift : e);
                    return i.Name switch
                    {
                        "add" => T.Add(l, r), "sub" => T.Sub(l, r), "mul" => T.Mul(l, r),
                        "cmeq" => Bool(T.Eq(l, r)), "cmgt" => Bool(T.Sgt(l, r)), "cmhi" => Bool(T.Ugt(l, r)), "cmhs" => Bool(T.Uge(l, r)),
                        "smax" => T.Select(T.Sgt(l, r), l, r), "smin" => T.Select(T.Slt(l, r), l, r),
                        "ushl" => VariableShift(l, r),
                        "fcmeq" => Bool(T.Operation(Op.FEq, 1, l, r)), "fcmgt" => Bool(T.Operation(Op.FLt, 1, r, l)),
                        "fadd" => Float(Op.FAdd, l, r), "fsub" => Float(Op.FSub, l, r), "fmul" => Float(Op.FMul, l, r), "fdiv" => Float(Op.FDiv, l, r),
                        "fabd" => T.Operation(Op.FAbs, s, Float(Op.FSub, l, r)),
                        "fmin" => T.Opaque((int)ArmOperation.Minimum, s, l, r), "fmaxnm" => T.Opaque((int)ArmOperation.MaximumNumber, s, l, r),
                        _ => throw new InvalidOperationException(i.Name)
                    };
                }); break;
            case Form.SimdUnary:
                value = Map(e =>
                {
                    var l = N(e); var zero = T.Zero(s);
                    return i.Name switch
                    {
                        "mvn" => T.Not(l), "cnt" => T.Operation(Op.PopCount, s, l), "neg" => T.Neg(l), "rev64" => N(e ^ (64 / s - 1)),
                        "scvtf" => T.Operation(Op.SToF, s, l), "ucvtf" => T.Operation(Op.UToF, s, l), "fcvtzs" => T.Operation(Op.FToSSaturate, s, l),
                        "fabs" => T.Operation(Op.FAbs, s, l), "fneg" => T.Operation(Op.FNeg, s, l), "fsqrt" => T.Operation(Op.FSqrt, s, l),
                        "frintm" => T.Opaque((int)ArmOperation.RoundNegative, s, l),
                        "fcmeq" => Bool(T.Operation(Op.FEq, 1, l, zero)), "fcmgt" => Bool(T.Operation(Op.FLt, 1, zero, l)),
                        "fcmlt" => Bool(T.Operation(Op.FLt, 1, l, zero)), "fcmge" => Bool(T.Operation(Op.FLe, 1, zero, l)),
                        _ => throw new InvalidOperationException(i.Name)
                    };
                }); break;
            case Form.SimdCopy:
                if (i.Mode == 5) { Put(i.D, N(i.Shift)); return; }
                value = i.Mode switch
                {
                    0 => Map(_ => G(i.N, s)), 1 => Map(_ => N(i.Shift)), 2 => N(i.Shift),
                    3 => Insert(i.D, i.Shift, G(i.N, s)), 4 => Insert(i.D, i.Shift, N(i.A)),
                    _ => throw new InvalidOperationException(i.Name)
                }; break;
            case Form.SimdBits:
                x = V(i.N, w); y = V(i.M, w); var old = V(i.D, w);
                Term Blend(Term mask, Term yes, Term no) => T.Or(T.And(mask, yes), T.And(T.Not(mask), no));
                value = i.Name switch
                {
                    "and" => T.And(x, y), "bic" => T.And(x, T.Not(y)), "orn" => T.Or(x, T.Not(y)), "eor" => T.Xor(x, y),
                    "bsl" => Blend(old, x, y), "bif" => Blend(y, old, x), "bit" => Blend(y, x, old),
                    _ => throw new InvalidOperationException(i.Name)
                }; break;
            case Form.SimdPermute:
                Term Both(int e) => e < count ? N(e) : M(e - count);
                value = Map(e => i.Name switch
                {
                    "zip1" => (e & 1) == 0 ? N(e / 2) : M(e / 2),
                    "ext" => Both(e + i.Shift), _ => Both(e * 2 + (i.Name == "uzp2" ? 1 : 0))
                }); break;
            case Form.SimdNarrow:
                value = Pack(64 / s, e => i.Name.StartsWith("fcvt") ? T.Operation(Op.FConvert, s, Lane(i.N, e, s * 2)) : T.Truncate(Lane(i.N, e, s * 2), s));
                if (i.Mode == 1) value = T.Concat(V(i.D, 64), value);
                break;
            case Form.SimdWiden:
                value = Pack(64 / s, e =>
                {
                    Term input = N(e + i.Mode * (64 / s));
                    if (i.Name.StartsWith("fcvt")) return T.Operation(Op.FConvert, s * 2, input);
                    return Shift(i.Name[0] == 's' ? T.SignExtend(input, s * 2) : T.ZeroExtend(input, s * 2), 0, i.Shift);
                }); break;
            case Form.SimdReduce:
                if (i.Name == "faddp") value = Float(Op.FAdd, N(0), N(1));
                else
                {
                    value = T.Zero(i.Name == "uaddlv" ? s * 2 : s);
                    for (int e = 0; e < count; e++) value = T.Add(value, T.ZeroExtend(N(e), value.Width));
                }
                break;
            case Form.SimdShift:
                value = Map(e => Shift(N(e), i.Name switch { "shl" => 0, "sshr" => 2, _ => 1 }, i.Shift)); break;
            case Form.SimdFloatImmediate: value = Map(_ => K(i.Imm, s)); break;
            case Form.SimdImmediate:
                x = K((i.Imm << i.Shift) | (i.Mode == 1 ? (1L << i.Shift) - 1 : 0), s);
                value = Map(e => i.Name switch { "movi" => x, "mvni" => T.Not(x), "orr" => T.Or(D(e), x), _ => T.And(D(e), T.Not(x)) }); break;
            case Form.SimdTransfer:
                var address = G(i.N, 64, true);
                var increment = i.Mode == 0 || i.M == 31 ? K(s / 8, 64) : G(i.M);
                if (i.Name == "st2")
                {
                    for (int e = 0; e < count; e++)
                        for (int j = 0; j < 2; j++)
                            builder.Write(block, T.Add(address, K((e * 2 + j) * (s / 8), 64)), Lane((i.D + j) % 32, e, s), pc);
                }
                else if (i.Name == "st1") builder.Write(block, address, D(i.Shift), pc);
                else
                {
                    var loaded = builder.Read(block, address, s, pc);
                    Vector(i.D, i.Name == "ld1r" ? Map(_ => loaded) : Insert(i.D, i.Shift, loaded));
                }
                if (i.Mode != 0) Put(i.N, T.Add(address, increment), true);
                return;
            default: throw new InvalidOperationException("指令不是块内计算");
        }
        Vector(i.D, value);
    }

    Term VariableShift(Term value, Term amount)
    {
        var signed = T.SignExtend(T.Truncate(amount, 8), value.Width);
        return T.Select(T.Slt(signed, T.Zero(value.Width)), T.LShr(value, T.Neg(signed)), T.Shl(value, signed));
    }
}
