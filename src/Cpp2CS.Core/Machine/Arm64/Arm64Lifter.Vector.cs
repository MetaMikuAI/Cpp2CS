using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Arm64;



/// <summary>
/// Advanced SIMD 向量指令。按车道展开为标量运算再用 Insert 拼回，
/// IR 中不引入向量类型；托管代码里这些指令主要来自 Vector2/Vector3/Color 的逐分量运算。
/// </summary>
public static partial class Arm64Lifter
{
    private sealed partial class Context
    {
        private static Expr Lane(int reg, int index, int size) => Field(V(reg, 128), index * size, size);

        private static Expr Pack(int total, int size, Func<int, Expr> lane)
        {
            if (total == size) return lane(0);
            Expr result = C(0, total);
            for (var i = 0; i < total / size; i++) result = new Insert(result, lane(i), i * size);
            return result;
        }

        private void SetLanes(int total, int size, Func<int, Expr> lane) => SetV(Rd, Pack(total, size, lane));

        private static Expr FloatLane(BinOp op, Expr a, Expr b) => new Binary(op, a, b, a.Width);

        private static Expr AllOnes(Expr condition, int size) => new Select(condition, C(Expr.Mask(size), size), C(0, size), size);

        private static Expr Lt(Expr a, int value) => new Compare(Cond.Slt, a, C((ulong)(long)value & Expr.Mask(a.Width), a.Width));

        private bool VectorDispatch()
        {
            if ((w & 0xBF3FFC00) == 0x0E31B800) { AddAcross(); return true; }
            if ((w & 0x9F200400) == 0x0E200400) { VectorThreeSame(); return true; }
            if ((w & 0x9F3E0C00) == 0x0E200800) { VectorTwoMisc(); return true; }
            if ((w & 0xDF3E0C00) == 0x5E200800) { ScalarTwoMisc(); return true; }
            if ((w & 0xDF200400) == 0x5E200400) { ScalarThreeSame(); return true; }
            if ((w & 0xDF3E0C00) == 0x5E300800) { ScalarPairwise(); return true; }
            if ((w & 0x9F000400) == 0x0F000000) { ByElement(scalar: false); return true; }
            if ((w & 0xDF000400) == 0x5F000000) { ByElement(scalar: true); return true; }
            if ((w & 0x9F800400) == 0x0F000400) { ShiftImmediate(); return true; }
            if ((w & 0xBFE08400) == 0x2E000000) { Ext(); return true; }
            if ((w & 0xBF208C00) == 0x0E000800) { Permute(); return true; }
            return false;
        }

        private void AddAcross()
        {
            var size = 8 << (int)Bits(22, 2);
            var total = Bit(30) ? 128 : 64;
            if (size == 64 || size == 32 && total == 64) { Unsupported("simd.addv.size"); return; }
            Expr sum = Lane(Rn, 0, size);
            for (var i = 1; i < total / size; i++) sum = Add(sum, Lane(Rn, i, size));
            SetV(Rd, sum);
        }

        private void VectorThreeSame()
        {
            var q = Bit(30);
            var u = Bit(29);
            var size = (int)Bits(22, 2);
            var opcode = Bits(11, 5);
            var total = q ? 128 : 64;
            if (opcode >= 0x18)
            {
                var esize = 32 << (size & 1);
                if (esize == 64 && !q) { Unsupported("simd.3same.float.size"); return; }
                FloatThreeSame(u, size >> 1 == 1, opcode, total, esize, Rn, Rm);
                return;
            }
            var lane = 8 << size;
            switch (opcode)
            {
                case 0x10:
                    if (lane == 64 && !q) { Unsupported("simd.add.size"); return; }
                    SetLanes(total, lane, i => u ? Sub(Lane(Rn, i, lane), Lane(Rm, i, lane)) : Add(Lane(Rn, i, lane), Lane(Rm, i, lane)));
                    return;
                case 0x03:
                    {
                        var n = V(Rn, total);
                        var m = V(Rm, total);
                        var d = V(Rd, total);
                        Expr Not(Expr e) => new Unary(UnOp.Not, e, total);
                        Expr result = (u, size) switch
                        {
                            (false, 0) => Op(BinOp.And, n, m),
                            (false, 1) => Op(BinOp.And, n, Not(m)),
                            (false, 2) => Rn == Rm ? n : Op(BinOp.Or, n, m),
                            (false, _) => Op(BinOp.Or, n, Not(m)),
                            (true, 0) => Op(BinOp.Xor, n, m),
                            // bsl: d 为选择掩码；bit: m 为掩码插入 n；bif: ~m 为掩码插入 n
                            (true, 1) => Op(BinOp.Xor, m, Op(BinOp.And, Op(BinOp.Xor, m, n), d)),
                            (true, 2) => Op(BinOp.Xor, d, Op(BinOp.And, Op(BinOp.Xor, d, n), m)),
                            _ => Op(BinOp.Xor, d, Op(BinOp.And, Op(BinOp.Xor, d, n), Not(m))),
                        };
                        SetV(Rd, result);
                        return;
                    }
                case 0x08:
                    if (lane == 64 && !q) { Unsupported("simd.shl.size"); return; }
                    SetLanes(total, lane, i => RegisterShift(Lane(Rn, i, lane), Lane(Rm, i, lane), lane, signed: !u));
                    return;
                case 0x13 when !u && lane < 64:
                    SetLanes(total, lane, i => Op(BinOp.Mul, Lane(Rn, i, lane), Lane(Rm, i, lane)));
                    return;
                case 0x0C or 0x0D when lane < 64:
                    var comparison = opcode == 0x0C ? u ? Cond.Ugt : Cond.Sgt : u ? Cond.Ult : Cond.Slt;
                    SetLanes(total, lane, i => new Select(new Compare(comparison, Lane(Rn, i, lane), Lane(Rm, i, lane)), Lane(Rn, i, lane), Lane(Rm, i, lane), lane));
                    return;
                case 0x11:
                    // cmtst / cmeq
                    if (lane == 64 && !q) { Unsupported("simd.cmtst.size"); return; }
                    SetLanes(total, lane, i => u
                        ? AllOnes(new Compare(Cond.Eq, Lane(Rn, i, lane), Lane(Rm, i, lane)), lane)
                        : AllOnes(new Compare(Cond.Ne, Op(BinOp.And, Lane(Rn, i, lane), Lane(Rm, i, lane)), C(0, lane)), lane));
                    return;
                case 0x06 or 0x07:
                    {
                        if (lane == 64 && !q) { Unsupported("simd.cm.size"); return; }
                        var cond = (u, opcode) switch
                        {
                            (false, 0x06) => Cond.Sgt,
                            (false, _) => Cond.Sge,
                            (true, 0x06) => Cond.Ugt,
                            _ => Cond.Uge,
                        };
                        SetLanes(total, lane, i => AllOnes(new Compare(cond, Lane(Rn, i, lane), Lane(Rm, i, lane)), lane));
                        return;
                    }
                default:
                    Unsupported("simd.3same");
                    return;
            }
        }

        /// <summary>USHL/SSHL：按 m 车道低 8 位的有符号值移位，正左负右，越界得 0（有符号右移得符号填充）。</summary>
        private static Expr RegisterShift(Expr value, Expr amount, int size, bool signed)
        {
            var count = Low(amount, 8);
            var widened = SExt(count, size);
            var left = new Select(Lt(count, size), Op(BinOp.Shl, value, widened), C(0, size), size);
            var negated = new Unary(UnOp.Neg, widened, size);
            var inRange = new Compare(Cond.Sgt, count, C((ulong)(-size) & 0xFF, 8));
            Expr right = signed
                ? Op(BinOp.AShr, value, new Select(inRange, negated, C((ulong)(size - 1), size), size))
                : new Select(inRange, Op(BinOp.LShr, value, negated), C(0, size), size);
            return new Select(Lt(count, 0), right, left, size);
        }

        private void FloatThreeSame(bool u, bool a, uint opcode, int total, int esize, int rn, int rm)
        {
            Expr N(int i) => Lane(rn, i, esize);
            Expr M(int i) => Lane(rm, i, esize);
            Func<int, Expr>? lane = (u, a, opcode) switch
            {
                (false, false, 0x1A) => i => FloatLane(BinOp.FAdd, N(i), M(i)),
                (false, true, 0x1A) => i => FloatLane(BinOp.FSub, N(i), M(i)),
                (true, false, 0x1B) => i => FloatLane(BinOp.FMul, N(i), M(i)),
                (true, false, 0x1F) => i => FloatLane(BinOp.FDiv, N(i), M(i)),
                (true, true, 0x1A) => i => new Unary(UnOp.FAbs, FloatLane(BinOp.FSub, N(i), M(i)), esize),
                (false, false, 0x1E) => i => FloatLane(BinOp.FMax, N(i), M(i)),
                (false, true, 0x1E) => i => FloatLane(BinOp.FMin, N(i), M(i)),
                (false, false, 0x18) => i => FloatLane(BinOp.FMaxNumber, N(i), M(i)),
                (false, true, 0x18) => i => FloatLane(BinOp.FMinNumber, N(i), M(i)),
                (false, false, 0x1C) => i => AllOnes(new Compare(Cond.FEq, N(i), M(i)), esize),
                (true, false, 0x1C) => i => AllOnes(new Compare(Cond.FGe, N(i), M(i)), esize),
                (true, true, 0x1C) => i => AllOnes(new Compare(Cond.FGt, N(i), M(i)), esize),
                (false, false, 0x19) => i => FloatLane(BinOp.FAdd, Lane(Rd, i, esize), FloatLane(BinOp.FMul, N(i), M(i))),
                (false, true, 0x19) => i => FloatLane(BinOp.FSub, Lane(Rd, i, esize), FloatLane(BinOp.FMul, N(i), M(i))),
                _ => null,
            };
            if (u && !a && opcode == 0x1A)
            {
                // faddp：先取 n 的相邻对，再取 m 的相邻对
                var half = total / esize / 2;
                SetLanes(total, esize, i => i < half
                    ? FloatLane(BinOp.FAdd, N(2 * i), N(2 * i + 1))
                    : FloatLane(BinOp.FAdd, M(2 * (i - half)), M(2 * (i - half) + 1)));
                return;
            }
            if (lane is null) { Unsupported("simd.3same.float"); return; }
            SetLanes(total, esize, lane);
        }

        private void VectorTwoMisc()
        {
            var q = Bit(30);
            var u = Bit(29);
            var size = (int)Bits(22, 2);
            var opcode = Bits(12, 5);
            var total = q ? 128 : 64;
            var sz = size & 1;
            var fsize = 32 << sz;
            var floatReserved = sz == 1 && !q;
            switch (u, opcode)
            {
                case (false, 0x00) when size < 3:
                    {
                        // rev64：每个 64 位双字内倒转元素顺序
                        var lane = 8 << size;
                        var per = 64 / lane;
                        SetLanes(total, lane, i => Lane(Rn, i / per * per + (per - 1 - i % per), lane));
                        return;
                    }
                case (false, 0x05) when size == 0:
                    SetLanes(total, 8, i => new Unary(UnOp.PopCount, Lane(Rn, i, 8), 8));
                    return;
                case (true, 0x05) when size == 0:
                    SetV(Rd, new Unary(UnOp.Not, V(Rn, total), total));
                    return;
                case (true, 0x0B) when !(size == 3 && !q):
                    {
                        var lane = 8 << size;
                        SetLanes(total, lane, i => new Unary(UnOp.Neg, Lane(Rn, i, lane), lane));
                        return;
                    }
                case (_, 0x0F) when size >= 2 && !floatReserved:
                    SetLanes(total, fsize, i => new Unary(u ? UnOp.FNeg : UnOp.FAbs, Lane(Rn, i, fsize), fsize));
                    return;
                case (true, 0x1F) when size >= 2 && !floatReserved:
                    SetLanes(total, fsize, i => new Unary(UnOp.FSqrt, Lane(Rn, i, fsize), fsize));
                    return;
                case (_, 0x1B) when size >= 2 && !floatReserved:
                    SetLanes(total, fsize, i => new Ir.Convert(u ? ConvKind.FloatToUInt : ConvKind.FloatToSInt, Lane(Rn, i, fsize), fsize));
                    return;
                case (_, 0x1D) when size < 2 && !floatReserved:
                    SetLanes(total, fsize, i => new Ir.Convert(u ? ConvKind.UIntToFloat : ConvKind.SIntToFloat, Lane(Rn, i, fsize), fsize));
                    return;
                case (_, 0x18 or 0x19) when !floatReserved && !(u && size >= 2 && opcode == 0x18):
                    {
                        var op = (u, size >= 2, opcode) switch
                        {
                            (false, false, 0x18) => UnOp.FRoundEven,
                            (false, false, _) => UnOp.FFloor,
                            (false, true, 0x18) => UnOp.FCeil,
                            (false, true, _) => UnOp.FTrunc,
                            (true, false, 0x18) => UnOp.FRoundAway,
                            _ => UnOp.FRoundCurrent,
                        };
                        SetLanes(total, fsize, i => new Unary(op, Lane(Rn, i, fsize), fsize));
                        return;
                    }
                case (false, 0x17) when size < 2:
                    {
                        // fcvtl/fcvtl2：取低半或高半的窄元素扩宽
                        var from = 16 << sz;
                        var to = from * 2;
                        var basis = q ? 64 / from : 0;
                        SetLanes(128, to, i => new Ir.Convert(ConvKind.FloatToFloat, Lane(Rn, basis + i, from), to));
                        return;
                    }
                case (false, 0x16) when size < 2:
                    {
                        // fcvtn/fcvtn2：窄化结果写入低半（清高半）或高半（保留低半）
                        var to = 16 << sz;
                        var from = to * 2;
                        var narrowed = Pack(64, to, i => new Ir.Convert(ConvKind.FloatToFloat, Lane(Rn, i, from), to));
                        SetV(Rd, q ? new Insert(V(Rd, 128), narrowed, 64) : narrowed);
                        return;
                    }
                case (false, 0x0C or 0x0D or 0x0E) or (true, 0x0C or 0x0D) when size >= 2 && !floatReserved:
                    {
                        var cond = (u, opcode) switch
                        {
                            (false, 0x0C) => Cond.FGt,
                            (false, 0x0D) => Cond.FEq,
                            (false, _) => Cond.FLt,
                            (true, 0x0C) => Cond.FGe,
                            _ => Cond.FLe,
                        };
                        SetLanes(total, fsize, i => AllOnes(new Compare(cond, Lane(Rn, i, fsize), C(0, fsize)), fsize));
                        return;
                    }
                default:
                    Unsupported("simd.2misc");
                    return;
            }
        }

        private void ScalarTwoMisc()
        {
            var u = Bit(29);
            var size = (int)Bits(22, 2);
            var opcode = Bits(12, 5);
            var fsize = 32 << (size & 1);
            switch (u, opcode)
            {
                case (_, 0x1D) when size < 2:
                    SetV(Rd, new Ir.Convert(u ? ConvKind.UIntToFloat : ConvKind.SIntToFloat, V(Rn, fsize), fsize));
                    return;
                case (_, 0x1B) when size >= 2:
                    SetV(Rd, new Ir.Convert(u ? ConvKind.FloatToUInt : ConvKind.FloatToSInt, V(Rn, fsize), fsize));
                    return;
                case (true, 0x0B) when size == 3:
                    SetV(Rd, new Unary(UnOp.Neg, V(Rn, 64), 64));
                    return;
                default:
                    Unsupported("simd.scalar.2misc");
                    return;
            }
        }

        private void ScalarThreeSame()
        {
            var u = Bit(29);
            var size = (int)Bits(22, 2);
            var opcode = Bits(11, 5);
            if (opcode >= 0x18)
            {
                FloatThreeSame(u, size >> 1 == 1, opcode, 32 << (size & 1), 32 << (size & 1), Rn, Rm);
                return;
            }
            if (opcode == 0x10 && size == 3)
            {
                SetV(Rd, u ? Sub(V(Rn, 64), V(Rm, 64)) : Add(V(Rn, 64), V(Rm, 64)));
                return;
            }
            Unsupported("simd.scalar.3same");
        }

        private void ScalarPairwise()
        {
            var u = Bit(29);
            var size = (int)Bits(22, 2);
            var opcode = Bits(12, 5);
            var fsize = 32 << (size & 1);
            Expr First(int s) => Lane(Rn, 0, s);
            Expr Second(int s) => Lane(Rn, 1, s);
            switch (u, opcode)
            {
                case (false, 0x1B) when size == 3:
                    SetV(Rd, Add(First(64), Second(64)));
                    return;
                case (true, 0x0D) when size < 2:
                    SetV(Rd, FloatLane(BinOp.FAdd, First(fsize), Second(fsize)));
                    return;
                case (true, 0x0F):
                    SetV(Rd, FloatLane(size < 2 ? BinOp.FMax : BinOp.FMin, First(fsize), Second(fsize)));
                    return;
                case (true, 0x0C):
                    SetV(Rd, FloatLane(size < 2 ? BinOp.FMaxNumber : BinOp.FMinNumber, First(fsize), Second(fsize)));
                    return;
                default:
                    Unsupported("simd.scalar.pairwise");
                    return;
            }
        }

        private void ByElement(bool scalar)
        {
            var q = Bit(30);
            var u = Bit(29);
            var size = (int)Bits(22, 2);
            var opcode = Bits(12, 4);
            var h = Bits(11, 1);
            var l = Bits(21, 1);
            var total = scalar ? 0 : q ? 128 : 64;
            if (!u && opcode is 0x9 or 0x1 or 0x5 && size >= 2)
            {
                var esize = 32 << (size & 1);
                if (esize == 64 && l != 0) { Unsupported("simd.element.L"); return; }
                var index = esize == 32 ? (int)((h << 1) | l) : (int)h;
                var rm = (int)Bits(16, 5);
                if (scalar) total = esize;
                else if (esize == 64 && !q) { Unsupported("simd.element.size"); return; }
                var element = Lane(rm, index, esize);
                SetLanes(total, esize, i =>
                {
                    var product = FloatLane(BinOp.FMul, Lane(Rn, i, esize), element);
                    return opcode switch
                    {
                        0x9 => product,
                        0x1 => FloatLane(BinOp.FAdd, Lane(Rd, i, esize), product),
                        _ => FloatLane(BinOp.FSub, Lane(Rd, i, esize), product),
                    };
                });
                return;
            }
            if (!scalar && !u && opcode == 0x8 && size is 1 or 2)
            {
                var esize = 8 << size;
                var m = Bit(20) ? 1u : 0u;
                var index = size == 1 ? (int)((h << 2) | (l << 1) | m) : (int)((h << 1) | l);
                var rm = size == 1 ? (int)Bits(16, 4) : (int)Bits(16, 5);
                var element = Lane(rm, index, esize);
                SetLanes(total, esize, i => Op(BinOp.Mul, Lane(Rn, i, esize), element));
                return;
            }
            Unsupported("simd.element");
        }

        private void ShiftImmediate()
        {
            var q = Bit(30);
            var u = Bit(29);
            var immh = Bits(19, 4);
            var immhb = (int)Bits(16, 7);
            var opcode = Bits(11, 5);
            var esize = 8 << System.Numerics.BitOperations.Log2(immh);
            var total = q ? 128 : 64;
            if (opcode == 0x14)
            {
                // sshll/ushll（sxtl/uxtl）：低半或高半扩宽后左移
                if (esize == 64) { Unsupported("simd.shll.size"); return; }
                var amount = immhb - esize;
                var basis = q ? 64 / esize : 0;
                var wide = esize * 2;
                SetLanes(128, wide, i =>
                {
                    var element = u ? ZExt(Lane(Rn, basis + i, esize), wide) : SExt(Lane(Rn, basis + i, esize), wide);
                    return amount == 0 ? element : Op(BinOp.Shl, element, C((ulong)amount, wide));
                });
                return;
            }
            if (esize == 64 && !q) { Unsupported("simd.shift.size"); return; }
            switch (u, opcode)
            {
                case (_, 0x00):
                    {
                        var amount = 2 * esize - immhb;
                        // 移位量等于元素宽度：逻辑右移得 0，算术右移等于移 esize-1
                        SetLanes(total, esize, i => u
                            ? amount == esize ? C(0, esize) : Op(BinOp.LShr, Lane(Rn, i, esize), C((ulong)amount, esize))
                            : Op(BinOp.AShr, Lane(Rn, i, esize), C((ulong)Math.Min(amount, esize - 1), esize)));
                        return;
                    }
                case (false, 0x0A):
                    {
                        var amount = immhb - esize;
                        SetLanes(total, esize, i => Op(BinOp.Shl, Lane(Rn, i, esize), C((ulong)amount, esize)));
                        return;
                    }
                default:
                    Unsupported("simd.shift");
                    return;
            }
        }

        private void Ext()
        {
            var q = Bit(30);
            var imm4 = (int)Bits(11, 4);
            var total = q ? 128 : 64;
            if (!q && imm4 >= 8) { Unsupported("ext.imm4"); return; }
            var shift = imm4 * 8;
            if (shift == 0) { SetV(Rd, V(Rn, total)); return; }
            SetV(Rd, Op(BinOp.Or, Op(BinOp.LShr, V(Rn, total), C((ulong)shift, total)), Op(BinOp.Shl, V(Rm, total), C((ulong)(total - shift), total))));
        }

        private void Permute()
        {
            var q = Bit(30);
            var size = (int)Bits(22, 2);
            var opcode = Bits(12, 3);
            var esize = 8 << size;
            var total = q ? 128 : 64;
            if (esize == 64 && !q) { Unsupported("simd.permute.size"); return; }
            var count = total / esize;
            var part = (int)(opcode >> 2);
            Expr Concat(int j) => j < count ? Lane(Rn, j, esize) : Lane(Rm, j - count, esize);
            Func<int, Expr>? lane = (opcode & 3) switch
            {
                1 => i => Concat(2 * i + part),
                2 => i => (i & 1) == 0 ? Lane(Rn, (i & ~1) + part, esize) : Lane(Rm, (i & ~1) + part, esize),
                3 => i => (i & 1) == 0 ? Lane(Rn, part * count / 2 + i / 2, esize) : Lane(Rm, part * count / 2 + i / 2, esize),
                _ => null,
            };
            if (lane is null) { Unsupported("simd.permute"); return; }
            SetLanes(total, esize, lane);
        }

        /// <summary>LD1/ST1 单车道与 LD1R。返回 false 表示不是该类编码。</summary>
        private bool SingleStructure()
        {
            // ST2 的交错存储；无回写，每个元素保留原位宽。
            if ((w & 0xBFFFF000) == 0x0C008000)
            {
                var laneSize = 8 << (int)Bits(10, 2);
                var total = Bit(30) ? 128 : 64;
                if (laneSize == 64 && total == 64) { Unsupported("st2.size"); return true; }
                var pairAddress = XSp(Rn, 64);
                for (var i = 0; i < total / laneSize; i++)
                    for (var j = 0; j < 2; j++)
                        Emit(new Store(pc, Add(pairAddress, C((ulong)((i * 2 + j) * laneSize / 8), 64)), Lane((Rd + j) % 32, i, laneSize)));
                return true;
            }
            var postIndex = (w & 0xBF800000) == 0x0D800000;
            if (!postIndex && (w & 0xBF9F0000) != 0x0D000000) return false;
            if (Bit(21)) { Unsupported("ldst.structure.multi"); return true; }
            var q = Bit(30);
            var load = Bit(22);
            var opcode = Bits(13, 3);
            var s = Bits(12, 1);
            var size = Bits(10, 2);
            var qbit = q ? 1u : 0u;
            int esize, index;
            switch (opcode)
            {
                case 0: esize = 8; index = (int)((qbit << 3) | (s << 2) | size); break;
                case 2 when (size & 1) == 0: esize = 16; index = (int)((qbit << 2) | (s << 1) | (size >> 1)); break;
                case 4 when size == 0: esize = 32; index = (int)((qbit << 1) | s); break;
                case 4 when size == 1 && s == 0: esize = 64; index = (int)qbit; break;
                case 6 when load && s == 0: esize = 8 << (int)size; index = -1; break;
                default: Unsupported("ldst.structure.single"); return true;
            }
            var basis = XSp(Rn, 64);
            if (index < 0)
            {
                var total = q ? 128 : 64;
                SetV(Rd, new Intrinsic($"vdup.{esize}", [new Load(basis, esize)], total));
            }
            else if (load) SetV(Rd, new Insert(V(Rd, 128), new Load(basis, esize), index * esize));
            else Emit(new Store(pc, basis, Lane(Rd, index, esize)));
            if (postIndex)
            {
                var rm = Rm;
                var step = esize / 8;
                SetXSp(Rn, Add(basis, rm == 31 ? C((ulong)step, 64) : X(rm, 64)));
            }
            return true;
        }
    }
}
