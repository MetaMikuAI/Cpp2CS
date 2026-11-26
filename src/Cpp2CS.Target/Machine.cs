using Cpp2CS.Snapshot;

namespace Cpp2CS.Target;

internal sealed partial class Machine(SnapshotBuilder builder, BlockId block, Term[] registers)
{
    TermPool T => builder.Terms;
    public Term[] Row => registers;
    public bool PlatformRegister { get; private set; }
    public Term G(int r, int w = 64, bool sp = false)
    {
        if (r == 18) PlatformRegister = true;
        return r == 31 && !sp ? T.Zero(w) : T.Truncate(registers[r], w);
    }
    Term V(int r, int w) => T.Truncate(registers[32 + r], w);
    void Put(int r, Term v)
    {
        if (r != 31) registers[r] = T.ZeroExtend(v, 64);
    }
    // size 恒为改写前的 SP 减去新值；寄存器寻址和立即数寻址共用同一约定。
    void PutBase(int r, Term value, ulong pc, Term? size = null)
    {
        if (r != 31) { Put(r, value); return; }
        var basis = registers[31];
        var next = T.ZeroExtend(value, 64);
        size ??= T.Sub(basis, next);
        registers[31] = size.IsConstant ? next : builder.StackAllocate(block, basis, size, pc);
    }
    void Vector(int r, Term v) => registers[32 + r] = T.ZeroExtend(v, 128);
    Term K(long v, int w) => T.Constant(v, w);
    Term Shift(Term v, int kind, int amount)
    {
        Term k = K(amount, v.Width);
        return kind switch { 0 => T.Shl(v, k), 1 => T.LShr(v, k), 2 => T.AShr(v, k), _ => T.Or(T.LShr(v, k), T.Shl(v, K(v.Width - amount, v.Width))) };
    }
    Term Extend(int reg, int option, int width)
    {
        int from = Math.Min(width, 8 << (option & 3));
        Term v = G(reg, from);
        return option < 4 ? T.ZeroExtend(v, width) : T.SignExtend(v, width);
    }
    (Term Left, Term Right)? comparison;
    public Term Condition(int code)
    {
        if (comparison is { } operands)
        {
            var (x, y) = operands;
            Term? direct = code switch
            {
                0 => T.Eq(x, y),
                1 => T.Ne(x, y),
                2 => T.Uge(x, y),
                3 => T.Ult(x, y),
                8 => T.Ugt(x, y),
                9 => T.Ule(x, y),
                10 => T.Sge(x, y),
                11 => T.Slt(x, y),
                12 => T.Sgt(x, y),
                13 => T.Sle(x, y),
                _ => null
            };
            if (direct != null) return direct;
        }
        Term n = registers[Abi.Negative], z = registers[Abi.Zero], c = registers[Abi.Carry], v = registers[Abi.Overflow];
        Term value = (code >> 1) switch { 0 => z, 1 => c, 2 => n, 3 => v, 4 => T.And(c, T.Not(z)), 5 => T.Eq(n, v), 6 => T.And(T.Eq(n, v), T.Not(z)), _ => T.True };
        return code < 14 && (code & 1) != 0 ? T.Not(value) : value;
    }
    public Term Predicate(Instruction i) => i.Form switch
    {
        Form.Condition => Condition(i.Mode),
        Form.CompareBranch => i.Name == "cbz" ? T.Eq(G(i.D, i.Width), T.Zero(i.Width)) : T.Ne(G(i.D, i.Width), T.Zero(i.Width)),
        Form.TestBranch => i.Name == "tbz" ? T.Not(T.Slice(G(i.D, i.Width), i.Shift, 1)) : T.Slice(G(i.D, i.Width), i.Shift, 1),
        _ => throw new ArgumentOutOfRangeException(nameof(i))
    };

    void Nz(Term result)
    {
        registers[Abi.Negative] = T.Slice(result, result.Width - 1, 1);
        registers[Abi.Zero] = T.Eq(result, T.Zero(result.Width));
    }

    public void Apply(Instruction i, ulong pc)
    {
        int w = i.Width;
        Term x, y, value;
        switch (i.Form)
        {
            case Form.Nop: return;
            case Form.Thread: Put(i.D, registers[Abi.Thread]); return;
            case Form.Address:
                Put(i.D, T.Bits(i.Destination(i.Name == "adrp" ? pc & ~4095ul : pc), 64)); return;
            case Form.Wide:
                value = K(i.Imm << i.Shift, w);
                if (i.Name == "movk") value = T.Or(T.And(G(i.D, w), K(~(65535L << i.Shift), w)), value);
                Put(i.D, i.Name == "movn" ? T.Not(value) : value); return;
            case Form.Immediate:
            case Form.Extended:
            case Form.Shifted:
                x = G(i.N, w, i.Form != Form.Shifted);
                y = i.Form switch { Form.Immediate => K(i.Imm << i.Shift, w), Form.Extended => Shift(Extend(i.M, i.Mode, w), 0, i.Shift), _ => Shift(G(i.M, w), i.Mode, i.Shift) };
                bool sub = i.Name.StartsWith("sub", StringComparison.Ordinal), flags = i.Name.EndsWith('s');
                value = sub ? T.Sub(x, y) : T.Add(x, y);
                if (flags)
                {
                    comparison = sub ? (x, y) : null;
                    Nz(value);
                    registers[Abi.Carry] = sub ? T.Uge(x, y) : T.Operation(Op.AddCarry, 1, x, y);
                    registers[Abi.Overflow] = T.Operation(sub ? Op.SubOverflow : Op.AddOverflow, 1, x, y);
                }
                if (!flags && i.Form != Form.Shifted && i.D == 31)
                    PutBase(31, value, pc, w == 64 && i.N == 31 ? (sub ? y : T.Neg(y)) : null);
                else Put(i.D, value);
                return;
            case Form.Logical:
            case Form.Mask:
                x = G(i.N, w);
                y = i.Form == Form.Mask ? K(i.Imm, w) : Shift(G(i.M, w), i.Mode, i.Shift);
                if (i.Name is "bic" or "orn" or "eon" or "bics") y = T.Not(y);
                value = i.Name switch { "orr" or "orn" => T.Or(x, y), "eor" or "eon" => T.Xor(x, y), _ => T.And(x, y) };
                if (i.Name is "ands" or "bics") { comparison = null; Nz(value); registers[Abi.Carry] = registers[Abi.Overflow] = T.False; }
                if (i.Form == Form.Mask && i.Name != "ands") PutBase(i.D, value, pc);
                else Put(i.D, value);
                return;
            case Form.Bitfield:
                int r = (int)i.Imm, s = i.Shift, offset = r <= s ? 0 : w - r, count = r <= s ? s - r + 1 : s + 1;
                value = T.Slice(G(i.N, w), r <= s ? r : 0, count);
                value = i.Name == "sbfm" ? T.SignExtend(value, w) : T.ZeroExtend(value, w);
                value = Shift(value, 0, offset);
                if (i.Name == "bfm")
                {
                    ulong mask = (ulong.MaxValue >> (64 - count)) << offset;
                    value = T.Or(T.And(G(i.D, w), K((long)~mask, w)), value);
                }
                Put(i.D, value); return;
            case Form.Select:
                x = G(i.N, w); y = G(i.M, w);
                y = i.Name switch { "csinc" => T.Add(y, K(1, w)), "csinv" => T.Not(y), "csneg" => T.Neg(y), _ => y };
                Put(i.D, T.Select(Condition(i.Mode), x, y)); return;
            case Form.Extract:
                Put(i.D, T.Slice(T.Concat(G(i.M, w), G(i.N, w)), i.Shift, w)); return;
            case Form.LongMultiply:
                Term Factor(int reg) => i.Name[0] == 's' ? T.SignExtend(G(reg, 32), 64) : T.ZeroExtend(G(reg, 32), 64);
                value = T.Mul(Factor(i.N), Factor(i.M)); x = G(i.A);
                Put(i.D, i.Name.Contains("sub") ? T.Sub(x, value) : T.Add(x, value)); return;
            case Form.VectorOr: Vector(i.D, T.Or(V(i.N, w), V(i.M, w))); return;
            case Form.VectorImmediate:
                value = K(i.Imm << i.Shift, i.Size);
                if (i.Name == "mvni") value = T.Not(value);
                while (value.Width < w) value = T.Concat(value, value);
                Vector(i.D, value); return;
            case Form.FloatImmediate: Vector(i.D, K(i.Imm, w)); return;
            case Form.Convert:
                if (i.Name is "fcvtzs" or "fcvtzu")
                    Put(i.D, T.Operation(i.Name == "fcvtzs" ? Op.FToSSaturate : Op.FToUSaturate, w, V(i.N, i.Size)));
                else if (i.Name == "fcvt") Vector(i.D, T.Operation(Op.FConvert, w, V(i.N, i.Size)));
                else Vector(i.D, T.Operation(i.Name == "scvtf" ? Op.SToF : Op.UToF, w, G(i.N, i.Size)));
                return;
            case Form.Multiply:
                value = T.Mul(G(i.N, w), G(i.M, w)); x = G(i.A, w);
                Put(i.D, i.Name == "madd" ? T.Add(x, value) : T.Sub(x, value)); return;
            case Form.Binary:
                x = G(i.N, w); y = G(i.M, w);
                Term k = T.And(y, K(w - 1, w));
                value = i.Name switch
                {
                    "udiv" or "sdiv" => T.Select(T.Eq(y, T.Zero(w)), T.Zero(w), T.Divide(i.Name == "udiv" ? Op.UDiv : Op.SDiv, x, y)),
                    "umulh" or "smulh" => T.Operation(i.Name == "umulh" ? Op.UMulHigh : Op.SMulHigh, w, x, y),
                    "lslv" => T.Shl(x, k),
                    "lsrv" => T.LShr(x, k),
                    "asrv" => T.AShr(x, k),
                    _ => T.Or(T.LShr(x, k), T.Shl(x, T.Sub(K(w, w), k)))
                };
                Put(i.D, value); return;
            case Form.Unary: Put(i.D, T.Operation(Op.CountLeadingZeros, w, G(i.N, w))); return;
            case Form.Memory: case Form.Pair: case Form.Literal: Memory(i, pc); return;
            case Form.FloatMove:
                if (i.Mode == 0) Put(i.D, V(i.N, w)); else Vector(i.D, G(i.N, w));
                return;
            case Form.FloatSelect: Vector(i.D, T.Select(Condition(i.Mode), V(i.N, w), V(i.M, w))); return;
            case Form.FloatCompare:
                comparison = null;
                x = V(i.N, w); y = i.Mode == 0 ? V(i.M, w) : T.Zero(w);
                registers[Abi.Negative] = T.Operation(Op.FLt, 1, x, y);
                registers[Abi.Zero] = T.Operation(Op.FEq, 1, x, y);
                registers[Abi.Carry] = T.Not(registers[Abi.Negative]);
                registers[Abi.Overflow] = T.Operation(Op.FUnordered, 1, x, y); return;
            case Form.FloatBinary:
                x = V(i.N, w); y = V(i.M, w);
                value = i.Name switch
                {
                    "fmul" or "fnmul" => T.Operation(Op.FMul, w, x, y),
                    "fdiv" => T.Operation(Op.FDiv, w, x, y),
                    "fadd" => T.Operation(Op.FAdd, w, x, y),
                    "fsub" => T.Operation(Op.FSub, w, x, y),
                    _ => T.Opaque((int)(i.Name switch { "fmax" => ArmOperation.Maximum, "fmin" => ArmOperation.Minimum, "fmaxnm" => ArmOperation.MaximumNumber, _ => ArmOperation.MinimumNumber }), w, x, y)
                };
                Vector(i.D, i.Name == "fnmul" ? T.Operation(Op.FNeg, w, value) : value); return;
            case Form.FloatUnary:
                x = V(i.N, w);
                value = i.Name switch
                {
                    "fmov" => x,
                    "fabs" => T.Operation(Op.FAbs, w, x),
                    "fneg" => T.Operation(Op.FNeg, w, x),
                    "fsqrt" => T.Operation(Op.FSqrt, w, x),
                    _ => T.Opaque((int)(i.Name switch { "frintn" => ArmOperation.RoundEven, "frintp" => ArmOperation.RoundPositive, "frintm" => ArmOperation.RoundNegative, _ => ArmOperation.RoundZero }), w, x)
                };
                Vector(i.D, value); return;
            case Form.Fused:
                x = V(i.N, w); y = V(i.A, w);
                if (i.Name is "fmsub" or "fnmadd") x = T.Operation(Op.FNeg, w, x);
                if (i.Name is "fnmadd" or "fnmsub") y = T.Operation(Op.FNeg, w, y);
                Vector(i.D, T.Opaque((int)ArmOperation.FusedMultiplyAdd, w, y, x, V(i.M, w))); return;
            default: ApplyExtension(i, pc); return;
        }
    }

    void Memory(Instruction i, ulong pc)
    {
        Term basis = i.Form == Form.Literal ? T.Bits(pc, 64) : G(i.N, 64, true);
        Term offset = i.Mode >= 4 ? Shift(Extend(i.M, i.Mode - 4, 64), 0, i.Shift) : K(i.Imm, 64);
        Term updated = T.Add(basis, offset);
        Term address = i.Mode == 1 ? basis : updated;
        void Access(int r, Term loc)
        {
            if (i.Name[0] == 's') builder.Write(block, loc, i.Vector ? V(r, i.Size) : G(r, i.Size), pc);
            else
            {
                Term data = builder.Read(block, loc, i.Size, pc);
                if (i.Vector) Vector(r, data);
                else Put(r, i.Name.Contains('s') ? T.SignExtend(data, i.Width) : T.ZeroExtend(data, i.Width));
            }
        }
        Access(i.D, address);
        if (i.Form == Form.Pair) Access(i.A, T.Add(address, K(i.Size / 8, 64)));
        if (i.Mode is 1 or 3) PutBase(i.N, updated, pc, T.Neg(offset));
    }

    public Term[] ReturnValues(Term link) => Abi.Return.Select(r => r == 30 ? link : r is >= 40 and < 48 ? T.Truncate(registers[r], 64) : registers[r]).ToArray();

    (Slot, Term)[] Arguments() => Abi.Arguments.Select(r => (Abi.Entry(r)!.Value, registers[r])).ToArray();

    public void TailCall(Term target, ulong pc)
    {
        var results = builder.TailCall(block, target, Arguments(), Abi.Slots(Abi.Results), pc);
        for (int j = 0; j < Abi.Results.Length; j++) registers[Abi.Results[j]] = results[j];
        builder.Return(block, ReturnValues(registers[30]));
    }

    public Term[] Call(Term target, ulong pc, bool unwind)
    {
        comparison = null;
        var resultSlots = Abi.Slots(Abi.Results);
        if (unwind) resultSlots = [.. resultSlots, (new(SlotKind.Unwind, 0), 64), (new(SlotKind.Unwind, 1), 64)];
        var results = builder.Call(block, target, Arguments(), resultSlots, pc);
        for (int r = 0; r < Abi.Count; r++)
        {
            if (r is >= 19 and <= 29 or 31 or Abi.Thread) continue;
            if (r is >= 40 and < 48) registers[r] = T.Concat(T.Truncate(registers[r], 64), T.Undefined(64));
            else registers[r] = T.Undefined(Abi.Width(r));
        }
        var row = unwind ? (Term[])registers.Clone() : [];
        if (unwind) { row[0] = results[^2]; row[1] = results[^1]; }
        for (int j = 0; j < Abi.Results.Length; j++) registers[Abi.Results[j]] = results[j];
        return row;
    }
}
