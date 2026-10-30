
namespace Cpp2CS.Ir;

/// <summary>
/// 表达式化简：常量折叠、代数恒等式、惰性标志位按条件码展开为比较。
/// 每条规则对所有输入都等价；不确定等价的形式原样保留。
/// </summary>
public static class Fold
{
    public static Expr Simplify(Expr expr) => expr switch
    {
        Binary b => Binary(b.Op, Simplify(b.Left), Simplify(b.Right), b.Width),
        Unary u => Unary(u.Op, Simplify(u.Operand), u.Width),
        Convert c => Convert(c.Kind, Simplify(c.Operand), c.Width),
        Compare c => Compare(c.Cond, Simplify(c.Left), Simplify(c.Right)),
        Select s => Select(Simplify(s.Condition), Simplify(s.True), Simplify(s.False), s.Width),
        Logical l => Logical(l.IsAnd, Simplify(l.Left), Simplify(l.Right)),
        Not n => Not(Simplify(n.Operand)),
        Extract e => Extract(Simplify(e.Operand), e.Low, e.Width),
        Insert i => Insert(Simplify(i.Base), Simplify(i.Value), i.Low),
        Load l => l with { Address = Simplify(l.Address) },
        Flags f => new Flags(f.Kind, Simplify(f.Left), f.Right is null ? null : Simplify(f.Right), f.OperandWidth),
        TestFlags t => TestFlags(Simplify(t.FlagsValue), t.Code),
        ConditionalFlags c => new ConditionalFlags(Simplify(c.Condition), Simplify(c.Taken), c.Nzcv),
        Intrinsic i => new Intrinsic(i.Name, i.Arguments.Select(Simplify).ToArray(), i.Width),
        _ => expr,
    };

    private static Const C(ulong value, int width) => Expr.C(value, width);
    private static bool IsConst(Expr e, ulong value) => e is Const c && c.Value == (value & Expr.Mask(c.Width));
    private static ulong Mask(int width) => Expr.Mask(width);
    private static long SignExtend(ulong value, int width) => width >= 64 ? (long)value : (long)(value << (64 - width)) >> (64 - width);

    public static Expr Binary(BinOp op, Expr left, Expr right, int width)
    {
        if (left is Const a && right is Const b && Evaluate(op, a.Value, b.Value, width) is { } value) return C(value, width);
        // 常量放右边，便于后续匹配
        if (left is Const && right is not Const && op is BinOp.Add or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor)
            (left, right) = (right, left);
        if (left is FrameAddress frame && right is Const offset && width == 64)
        {
            if (op == BinOp.Add) return new FrameAddress(frame.Offset + (long)offset.Value);
            if (op == BinOp.Sub) return new FrameAddress(frame.Offset - (long)offset.Value);
            // AAPCS64：函数入口 SP 16 字节对齐，所以 16 字节对齐的栈地址与小于 16 的常量按位或等于相加
            if (op == BinOp.Or && (frame.Offset & 15) == 0 && offset.Value < 16) return new FrameAddress(frame.Offset + (long)offset.Value);
        }
        if (right is Const r)
        {
            // 高位中的窄整数加法，再算术右移，可还原为符号扩展后的缩放索引。
            if (op == BinOp.AShr && width is 32 or 64
                && left is Binary { Op: BinOp.Add, Left: Binary { Op: BinOp.Shl, Left: var source, Right: Const up }, Right: Const delta }
                && up.Value < (ulong)width && r.Value <= up.Value && width - (int)up.Value is 8 or 16 or 32
                && (delta.Value & Mask((int)up.Value)) == 0)
            {
                var bits = width - (int)up.Value;
                var index = Binary(BinOp.Add, Convert(ConvKind.Truncate, source, bits), C(delta.Value >> (int)up.Value, bits), bits);
                return Binary(BinOp.Shl, Convert(ConvKind.SignExtend, index, width), C(up.Value - r.Value, width), width);
            }
            switch (op)
            {
                case BinOp.Add or BinOp.Sub or BinOp.Or or BinOp.Xor or BinOp.Shl or BinOp.LShr or BinOp.AShr or BinOp.Ror when r.Value == 0:
                    return left;
                case BinOp.And when r.Value == 0:
                case BinOp.Mul when r.Value == 0:
                    return C(0, width);
                case BinOp.And when r.Value == Mask(width):
                case BinOp.Mul when r.Value == 1:
                case BinOp.SDiv or BinOp.UDiv when r.Value == 1:
                    return left;
                case BinOp.Sub:
                    // x - c 统一成 x + (-c)，地址与偏移的匹配只需处理加法
                    return Binary(BinOp.Add, left, C((ulong)-(long)r.Value, width), width);
                case BinOp.Add when left is Binary { Op: BinOp.Add, Right: Const inner } nested:
                    return Binary(BinOp.Add, nested.Left, C(inner.Value + r.Value, width), width);
                case BinOp.And when left is Convert { Kind: ConvKind.ZeroExtend } z && (r.Value & Mask(z.Operand.Width)) == Mask(z.Operand.Width):
                    return left;
            }
        }
        if (op == BinOp.Xor && left == right) return C(0, width);
        if (op is BinOp.And or BinOp.Or && left == right) return left;
        if (op == BinOp.Sub && left == right) return C(0, width);
        return new Binary(op, left, right, width);
    }

    private static ulong? Evaluate(BinOp op, ulong a, ulong b, int width)
    {
        var mask = Mask(width);
        a &= mask;
        b &= mask;
        int Shift() => (int)(b % (ulong)width);
        return op switch
        {
            BinOp.Add => (a + b) & mask,
            BinOp.Sub => (a - b) & mask,
            BinOp.Mul => (a * b) & mask,
            BinOp.And => a & b,
            BinOp.Or => a | b,
            BinOp.Xor => a ^ b,
            BinOp.Shl when width <= 64 => (a << Shift()) & mask,
            BinOp.LShr when width <= 64 => a >> Shift(),
            BinOp.AShr when width <= 64 => (ulong)(SignExtend(a, width) >> Shift()) & mask,
            BinOp.UDiv when b != 0 => a / b,
            BinOp.URem when b != 0 => a % b,
            BinOp.SDiv when b != 0 && !(SignExtend(b, width) == -1 && SignExtend(a, width) == SignExtend(1UL << (width - 1), width)) =>
                (ulong)(SignExtend(a, width) / SignExtend(b, width)) & mask,
            _ => null,
        };
    }

    public static Expr Unary(UnOp op, Expr operand, int width)
    {
        if (operand is Const c && width <= 64)
        {
            switch (op)
            {
                case UnOp.Neg: return C((ulong)-(long)c.Value, width);
                case UnOp.Not: return C(~c.Value, width);
            }
        }
        if (op is UnOp.Not or UnOp.Neg && operand is Unary inner && inner.Op == op) return inner.Operand;
        return new Unary(op, operand, width);
    }

    public static Expr Convert(ConvKind kind, Expr operand, int width)
    {
        if (operand.Width == width && kind is ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate or ConvKind.Bitcast) return operand;
        if (operand is Const c && width <= 64)
        {
            switch (kind)
            {
                case ConvKind.ZeroExtend or ConvKind.Truncate: return C(c.Value, width);
                case ConvKind.SignExtend: return C((ulong)c.Signed, width);
            }
        }
        if (kind == ConvKind.Truncate)
        {
            switch (operand)
            {
                case Convert { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend } ext when width <= ext.Operand.Width:
                    return Convert(ConvKind.Truncate, ext.Operand, width);
                case Convert { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend } ext:
                    return Convert(ext.Kind, ext.Operand, width);
                case Convert { Kind: ConvKind.Truncate } inner:
                    return Convert(ConvKind.Truncate, inner.Operand, width);
                case Use use:
                    return use with { Width = width };
                case Read read:
                    return read with { Width = width };
                case Binary { Op: BinOp.Add or BinOp.Sub or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor } b
                    when b.Left is Ir.Convert or Const or Use && b.Right is Ir.Convert or Const or Use:
                    // 低位只依赖操作数低位
                    return Binary(b.Op, Convert(ConvKind.Truncate, b.Left, width), Convert(ConvKind.Truncate, b.Right, width), width);
            }
        }
        if (kind == ConvKind.ZeroExtend && operand is Convert { Kind: ConvKind.ZeroExtend } z) return Convert(ConvKind.ZeroExtend, z.Operand, width);
        if (kind == ConvKind.SignExtend && operand is Convert { Kind: ConvKind.SignExtend } s) return Convert(ConvKind.SignExtend, s.Operand, width);
        return new Convert(kind, operand, width);
    }

    public static Expr Extract(Expr operand, int low, int width)
    {
        if (low == 0) return Convert(ConvKind.Truncate, operand, width);
        if (operand is Const c && low + width <= 64) return C(c.Value >> low, width);
        if (operand is Insert insert && low == insert.Low && width == insert.Value.Width) return insert.Value;
        if (operand is Convert { Kind: ConvKind.ZeroExtend } z && low >= z.Operand.Width) return C(0, width);
        return new Extract(operand, low, width);
    }

    public static Expr Insert(Expr target, Expr value, int low)
    {
        if (low == 0 && value.Width == target.Width) return value;
        if (target is Const a && value is Const b && target.Width <= 64
            && low >= 0 && value.Width > 0 && low <= target.Width - value.Width)
            return C((a.Value & ~(Mask(value.Width) << low)) | ((b.Value & Mask(value.Width)) << low), target.Width);
        return new Insert(target, value, low);
    }

    /// <summary>普通整数的位段替换；向量继续保留逐道表示。</summary>
    public static Expr? ScalarInsert(Insert insert)
    {
        var width = insert.Width;
        if (width is not (32 or 64) || insert.Low < 0 || insert.Value.Width <= 0
            || insert.Low > width - insert.Value.Width) return null;
        var mask = Mask(insert.Value.Width) << insert.Low;
        return Binary(BinOp.Or, Binary(BinOp.And, insert.Base, C(~mask, width), width),
            Binary(BinOp.Shl, Convert(ConvKind.ZeroExtend, insert.Value, width), C((ulong)insert.Low, width), width), width);
    }

    /// <summary>整数位段零扩展到普通宽度；先移位和掩码，不把非字节位宽伪装成托管整数。</summary>
    public static Expr? ScalarExtract(Extract extract, int width)
    {
        var source = extract.Operand.Width;
        if (source is not (32 or 64) || width is not (8 or 16 or 32 or 64)
            || extract.Low < 0 || extract.Width <= 0 || extract.Width > width || extract.Low > source - extract.Width) return null;
        var shifted = Binary(BinOp.LShr, extract.Operand, C((ulong)extract.Low, source), source);
        var masked = Binary(BinOp.And, shifted, C(Mask(extract.Width), source), source);
        return Convert(source > width ? ConvKind.Truncate : ConvKind.ZeroExtend, masked, width);
    }

    public static Expr Compare(Cond cond, Expr left, Expr right)
    {
        if (left is Const a && right is Const b && left.Width <= 64)
        {
            var sa = a.Signed;
            var sb = b.Signed;
            bool? result = cond switch
            {
                Cond.Eq => a.Value == b.Value,
                Cond.Ne => a.Value != b.Value,
                Cond.Ult => a.Value < b.Value,
                Cond.Ule => a.Value <= b.Value,
                Cond.Ugt => a.Value > b.Value,
                Cond.Uge => a.Value >= b.Value,
                Cond.Slt => sa < sb,
                Cond.Sle => sa <= sb,
                Cond.Sgt => sa > sb,
                Cond.Sge => sa >= sb,
                _ => null,
            };
            if (result is { } r) return C(r ? 1UL : 0, 1);
        }
        // 1 位布尔与常量比较
        if (left.Width == 1 && right is Const one)
        {
            if (cond == Cond.Ne && one.Value == 0 || cond == Cond.Eq && one.Value == 1) return left;
            if (cond == Cond.Eq && one.Value == 0 || cond == Cond.Ne && one.Value == 1) return Not(left);
        }
        // zext(x) ==/!= c：比较可以在原宽度进行
        if (cond is Cond.Eq or Cond.Ne && left is Convert { Kind: ConvKind.ZeroExtend } z && right is Const k && (k.Value & ~Mask(z.Operand.Width)) == 0)
            return Compare(cond, z.Operand, C(k.Value, z.Operand.Width));
        if (cond is Cond.Eq or Cond.Ne && left is Convert { Kind: ConvKind.ZeroExtend } z1 && z1.Operand.Width == 1 && right is Const k1)
            return k1.Value == 0 == (cond == Cond.Ne) ? z1.Operand : Not(z1.Operand);
        return new Compare(cond, left, right);
    }

    public static Expr Select(Expr condition, Expr whenTrue, Expr whenFalse, int width)
    {
        if (condition is Const c) return c.Value != 0 ? whenTrue : whenFalse;
        if (whenTrue == whenFalse) return whenTrue;
        if (width == 1 && whenTrue is Const t && whenFalse is Const f)
            return t.Value != 0 && f.Value == 0 ? condition : t.Value == 0 && f.Value != 0 ? Not(condition) : new Select(condition, whenTrue, whenFalse, width);
        return new Select(condition, whenTrue, whenFalse, width);
    }

    public static Expr Logical(bool isAnd, Expr left, Expr right)
    {
        if (left is Const l) return (l.Value != 0) == isAnd ? right : l;
        if (right is Const r) return (r.Value != 0) == isAnd ? left : r;
        return new Logical(isAnd, left, right);
    }

    public static Expr Not(Expr operand) => operand switch
    {
        Const c => C(c.Value == 0 ? 1UL : 0, 1),
        Not n => n.Operand,
        Compare c => new Compare(Invert(c.Cond), c.Left, c.Right),
        Logical l => Logical(!l.IsAnd, Not(l.Left), Not(l.Right)),
        _ => new Not(operand),
    };

    public static Cond Invert(Cond cond) => cond switch
    {
        Cond.Eq => Cond.Ne,
        Cond.Ne => Cond.Eq,
        Cond.Slt => Cond.Sge,
        Cond.Sge => Cond.Slt,
        Cond.Sle => Cond.Sgt,
        Cond.Sgt => Cond.Sle,
        Cond.Ult => Cond.Uge,
        Cond.Uge => Cond.Ult,
        Cond.Ule => Cond.Ugt,
        Cond.Ugt => Cond.Ule,
        // 浮点：取反后无序情况的真假也随之翻转
        Cond.FEq => Cond.FUne,
        Cond.FUne => Cond.FEq,
        Cond.FNe => Cond.FUeq,
        Cond.FUeq => Cond.FNe,
        Cond.FLt => Cond.FUge,
        Cond.FUge => Cond.FLt,
        Cond.FLe => Cond.FUgt,
        Cond.FUgt => Cond.FLe,
        Cond.FGt => Cond.FUle,
        Cond.FUle => Cond.FGt,
        Cond.FGe => Cond.FUlt,
        Cond.FUlt => Cond.FGe,
        Cond.FUnordered => Cond.FOrdered,
        Cond.FOrdered => Cond.FUnordered,
        Cond.Neg => Cond.NotNeg,
        Cond.NotNeg => Cond.Neg,
        Cond.Overflow => Cond.NoOverflow,
        Cond.NoOverflow => Cond.Overflow,
        _ => throw new ArgumentOutOfRangeException(nameof(cond)),
    };

    /// <summary>条件码对惰性标志位的解释，按 ARM64 NZCV 语义。无法展开时保留 TestFlags。</summary>
    public static Expr TestFlags(Expr flags, FlagCondition code)
    {
        if (code == FlagCondition.Al) return C(1, 1);
        if (code == FlagCondition.Nv) return C(1, 1);
        switch (flags)
        {
            case Flags { Kind: FlagKind.Sub, Right: { } right } sub:
                {
                    Cond? cond = code switch
                    {
                        FlagCondition.Eq => Cond.Eq,
                        FlagCondition.Ne => Cond.Ne,
                        FlagCondition.Hs => Cond.Uge,
                        FlagCondition.Lo => Cond.Ult,
                        FlagCondition.Hi => Cond.Ugt,
                        FlagCondition.Ls => Cond.Ule,
                        FlagCondition.Ge => Cond.Sge,
                        FlagCondition.Lt => Cond.Slt,
                        FlagCondition.Gt => Cond.Sgt,
                        FlagCondition.Le => Cond.Sle,
                        _ => null,
                    };
                    if (cond is { } c) return Compare(c, sub.Left, right);
                    if (code is FlagCondition.Mi or FlagCondition.Pl)
                        return Compare(code == FlagCondition.Mi ? Cond.Slt : Cond.Sge, Binary(BinOp.Sub, sub.Left, right, sub.OperandWidth), C(0, sub.OperandWidth));
                    break;
                }
            case Flags { Kind: FlagKind.Add, Right: { } right } add:
                {
                    if (code is FlagCondition.Mi or FlagCondition.Pl)
                        return Compare(code == FlagCondition.Mi ? Cond.Slt : Cond.Sge, Binary(BinOp.Add, add.Left, right, add.OperandWidth), C(0, add.OperandWidth));
                    if (code is FlagCondition.Eq or FlagCondition.Ne)
                        return Compare(code == FlagCondition.Eq ? Cond.Eq : Cond.Ne, Binary(BinOp.Add, add.Left, right, add.OperandWidth), C(0, add.OperandWidth));
                    if (right is Const amount && code is FlagCondition.Hs or FlagCondition.Lo or FlagCondition.Hi or FlagCondition.Ls)
                    {
                        // 加 k 的进位边界为 2^width-k；k=0 时永不进位。
                        if (amount.Value == 0) return C(code is FlagCondition.Lo or FlagCondition.Ls ? 1UL : 0, 1);
                        var boundary = C(unchecked(0UL - amount.Value), add.OperandWidth);
                        var condition = code switch { FlagCondition.Hs => Cond.Uge, FlagCondition.Lo => Cond.Ult, FlagCondition.Hi => Cond.Ugt, _ => Cond.Ule };
                        return Compare(condition, add.Left, boundary);
                    }
                    // cmn x, #k 等价于 cmp x, #-k（-k 可表示时有符号条件一致）
                    if (right is Const k && k.Value != 0 && k.Value != 1UL << (add.OperandWidth - 1) && code is FlagCondition.Ge or FlagCondition.Lt or FlagCondition.Gt or FlagCondition.Le)
                    {
                        var negated = C((ulong)-(long)k.Value, add.OperandWidth);
                        var cond = code switch { FlagCondition.Ge => Cond.Sge, FlagCondition.Lt => Cond.Slt, FlagCondition.Gt => Cond.Sgt, _ => Cond.Sle };
                        return Compare(cond, add.Left, negated);
                    }
                    break;
                }
            case Flags { Kind: FlagKind.Logic } logic:
                {
                    var value = logic.Right is null ? logic.Left : Binary(BinOp.And, logic.Left, logic.Right, logic.OperandWidth);
                    var zero = C(0, logic.OperandWidth);
                    // 逻辑运算 C=V=0
                    return code switch
                    {
                        FlagCondition.Eq => Compare(Cond.Eq, value, zero),
                        FlagCondition.Ne => Compare(Cond.Ne, value, zero),
                        FlagCondition.Mi or FlagCondition.Lt => Compare(Cond.Slt, value, zero),
                        FlagCondition.Pl or FlagCondition.Ge => Compare(Cond.Sge, value, zero),
                        FlagCondition.Gt => Compare(Cond.Sgt, value, zero),
                        FlagCondition.Le => Compare(Cond.Sle, value, zero),
                        FlagCondition.Hs or FlagCondition.Hi or FlagCondition.Vs => C(0, 1),
                        FlagCondition.Lo or FlagCondition.Ls or FlagCondition.Vc => C(1, 1),
                        _ => new TestFlags(flags, code),
                    };
                }
            case Flags { Kind: FlagKind.FloatCompare, Right: { } right } fc:
                {
                    Cond? cond = code switch
                    {
                        FlagCondition.Eq => Cond.FEq,
                        FlagCondition.Ne => Cond.FUne,
                        FlagCondition.Mi or FlagCondition.Lo => Cond.FLt,
                        FlagCondition.Pl or FlagCondition.Hs => Cond.FUge,
                        FlagCondition.Ge => Cond.FGe,
                        FlagCondition.Lt => Cond.FUlt,
                        FlagCondition.Gt => Cond.FGt,
                        FlagCondition.Le => Cond.FUle,
                        FlagCondition.Hi => Cond.FUgt,
                        FlagCondition.Ls => Cond.FLe,
                        FlagCondition.Vs => Cond.FUnordered,
                        FlagCondition.Vc => Cond.FOrdered,
                        _ => null,
                    };
                    if (cond is { } c) return new Compare(c, fc.Left, right);
                    break;
                }
            case ConditionalFlags ccmp when ccmp.Condition is not Const:
                {
                    var taken = TestFlags(ccmp.Taken, code);
                    var otherwise = Cpp2CS.Ir.Evaluator.Holds(code, ccmp.Nzcv);
                    return otherwise ? Logical(false, Not(ccmp.Condition), taken) : Logical(true, ccmp.Condition, taken);
                }
            case ConditionalFlags { Condition: Const c } ccmp:
                return c.Value != 0 ? TestFlags(ccmp.Taken, code) : C(Cpp2CS.Ir.Evaluator.Holds(code, ccmp.Nzcv) ? 1UL : 0, 1);
        }
        return new TestFlags(flags, code);
    }
}
