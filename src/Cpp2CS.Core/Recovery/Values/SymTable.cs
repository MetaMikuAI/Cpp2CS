using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Memory;
using IrConst = Cpp2CS.Ir.Const;

namespace Cpp2CS.Recovery.Values;

/// <summary>
/// 单个方法的符号值表：创建、驻留并规范化节点。规范化只依据位的来源，不依据类型：
/// 移位、掩码、插入、提取、零扩展、截断与位转换只重排片；按位运算与低位算术可以推到片上；
/// φ 的一段在至少一条入边上恰是一个 IL 值时，投影为该段的 φ。
/// </summary>
public sealed partial class SymTable
{
    private readonly Dictionary<Sym, Sym> interned = [];
    private readonly Dictionary<(Call, int), ResultSym> results = [];
    private readonly Dictionary<(Call, int), OutSym> outs = [];
    private readonly Dictionary<(Stmt, int), ReadSym> reads = new(new SiteComparer());
    private readonly Dictionary<object, PhiSym> phis = [];
    private readonly Dictionary<(PhiSym, int, int), PhiSym> projections = [];
    private readonly Dictionary<PhiSym, List<PhiSym>> projectionsOf = [];
    private readonly HashSet<(PhiSym, int, int)> projecting = [];
    private readonly Dictionary<ConcatSym, PhiSym> joins = [];
    private readonly Dictionary<PhiSym, List<ConcatSym>> joinsOf = [];
    private int next;

    public IEnumerable<PhiSym> Phis => phis.Values.Concat(projections.Values);

    private T Intern<T>(T candidate) where T : Sym
    {
        if (interned.TryGetValue(candidate, out var known)) return (T)known;
        candidate.Id = ++next;
        interned.Add(candidate, candidate);
        return candidate;
    }

    private T Fresh<T>(T sym) where T : Sym
    {
        sym.Id = ++next;
        return sym;
    }

    public Sym Const(ulong value, int width)
    {
        if (width <= 64) return Intern(new ConstSym(width == 64 ? value : value & Expr.Mask(width), width));
        return Concat(Const(value, 64), Zero(width - 64));
    }

    public Sym Zero(int width) => Const(0, width);
    public Sym Undef(int width) => Intern(new UndefSym(width));
    public Sym Unknown(string reason, int width) => Intern(new UnknownSym(reason, width));
    public Sym Arg(int index, int width) => Intern(new ArgSym(index, width));
    public Sym Entity(Symbol symbol) => Intern(new EntitySym(symbol));
    public Sym Local(LocalSpace space, long offset) => Intern(new LocalSym(space, offset));

    public ResultSym Result(Call site, int index, int width)
    {
        if (!results.TryGetValue((site, index), out var sym)) results[(site, index)] = sym = Fresh(new ResultSym(site, index, width));
        return sym;
    }

    public OutSym Out(Call site, int argument, int width)
    {
        if (!outs.TryGetValue((site, argument), out var sym)) outs[(site, argument)] = sym = Fresh(new OutSym(site, argument, width));
        return sym;
    }

    public ReadSym Read(Stmt site, int ordinal, Sym address, int width)
    {
        if (!reads.TryGetValue((site, ordinal), out var sym) || !ReferenceEquals(sym.Address, address) || sym.Width != width)
            reads[(site, ordinal)] = sym = Fresh(new ReadSym(site, ordinal, address, width));
        return sym;
    }

    /// <summary>以 Origin 为身份的 φ；同一 Origin 总是得到同一个节点。</summary>
    public PhiSym Phi(Block block, object origin, int width)
    {
        if (!phis.TryGetValue(origin, out var phi)) phis[origin] = phi = Fresh(new PhiSym(block, origin, width));
        return phi;
    }

    /// <summary>设置 φ 的一个来源，并同步到它的投影。</summary>
    public void SetSource(PhiSym phi, int index, Sym value)
    {
        phi.Sources[index] = value;
        if (projectionsOf.TryGetValue(phi, out var list))
            foreach (var projection in list.ToArray())
                SetSource(projection, index, Slice(value, projection.Projection!.Value.Low, projection.Width));
        if (joinsOf.TryGetValue(phi, out var combined))
            foreach (var concat in combined.ToArray())
                SetSource(joins[concat], index, Concat(concat.Parts.Cast<PhiSym>().Select(p => p.Sources[index]!)));
    }

    public static Sym Resolve(Sym sym)
    {
        while (sym is PhiSym { Forward: { } forward }) sym = forward;
        return sym;
    }

    /// <summary>位视图：拼接的各部分，或单个节点。</summary>
    public static IReadOnlyList<Sym> Segments(Sym sym) => Resolve(sym) is ConcatSym concat ? concat.Parts : [Resolve(sym)];

    public static bool IsZero(Sym sym) => Resolve(sym) is ConstSym { Value: 0 };

    public Sym Slice(Sym sym, int low, int width)
    {
        sym = Resolve(sym);
        if (low < 0 || width <= 0 || low + width > sym.Width) throw new ArgumentOutOfRangeException(nameof(low), $"{sym}[{low}:{width}]");
        if (low == 0 && width == sym.Width) return sym;
        switch (sym)
        {
            case ConstSym c:
                return Const(low >= 64 ? 0 : c.Value >> low, width);
            case UndefSym:
                return Undef(width);
            case UnknownSym u:
                return Unknown(u.Reason, width);
            case SliceSym s:
                return Slice(s.Base, s.Low + low, width);
            case ConcatSym concat:
                {
                    var parts = new List<Sym>();
                    var at = 0;
                    foreach (var part in concat.Parts)
                    {
                        var from = Math.Max(low, at);
                        var to = Math.Min(low + width, at + part.Width);
                        if (from < to) parts.Add(Slice(part, from - at, to - from));
                        at += part.Width;
                    }
                    return Concat(parts);
                }
            case OpSym { Op: { Kind: OperatorKind.Convert } op } convert when op.Conversion == ConvKind.SignExtend && low + width <= convert.Args[0].Width:
                return Slice(convert.Args[0], low, width);
            case OpSym { Op: { Kind: OperatorKind.Binary } op } binary when op.Binary is BinOp.And or BinOp.Or or BinOp.Xor
                || low == 0 && op.Binary is BinOp.Add or BinOp.Sub or BinOp.Mul:
                return Binary(op.Binary, Slice(binary.Args[0], low, width), Slice(binary.Args[1], low, width), width);
            // 一个加数的低 low 位全为零（减法时是减数）：低位不产生进位或借位，高段只由两侧的高段决定。
            case OpSym { Op: { Kind: OperatorKind.Binary } op } carryless when low > 0 && op.Binary is BinOp.Add or BinOp.Sub
                && (LowZeros(carryless.Args[1]) >= low || op.Binary == BinOp.Add && LowZeros(carryless.Args[0]) >= low):
                return Binary(op.Binary, Slice(carryless.Args[0], low, width), Slice(carryless.Args[1], low, width), width);
            case OpSym { Op: { Kind: OperatorKind.Unary } op } unary when op.Unary == UnOp.Not || low == 0 && op.Unary == UnOp.Neg:
                return Unary(op.Unary, Slice(unary.Args[0], low, width), width);
            case PhiSym phi when ProjectPhi(phi, low, width) is { } projected:
                return projected;
        }
        return Intern(new SliceSym(sym, low, width));
    }

    /// <summary>沿合流环存在完整片来源时投影 φ；先驻留投影身份，再连接来源，允许循环互相引用。</summary>
    private PhiSym? ProjectPhi(PhiSym phi, int low, int width)
    {
        if (phi.Projection is { } outer) return ProjectPhi(outer.Whole, outer.Low + low, width);
        if (projections.TryGetValue((phi, low, width), out var known)) return known;
        if (!projecting.Add((phi, low, width))) return null;
        // 沿合流环查找完整片来源，不能因先访问到回边就把另一条边上的证据丢掉。
        var seen = new HashSet<PhiSym>();
        bool Evidence(PhiSym current)
        {
            if (!seen.Add(current)) return false;
            return current.Sources.OfType<Sym>().Select(Resolve).Any(source => source is PhiSym next
                ? Evidence(next) : Slice(source, low, width) is not SliceSym piece || !ReferenceEquals(piece.Base, source));
        }
        var useful = Evidence(phi);
        projecting.Remove((phi, low, width));
        return useful ? Projection(phi, low, width) : null;
    }

    /// <summary>φ 的一段，来源为各入边的同一段。</summary>
    public PhiSym Projection(PhiSym phi, int low, int width)
    {
        if (phi.Projection is { } outer) return Projection(outer.Whole, outer.Low + low, width);
        if (projections.TryGetValue((phi, low, width), out var known)) return known;
        var projection = Fresh(new PhiSym(phi.Block, (phi.Origin, low, width), width) { Projection = (phi, low) });
        projections[(phi, low, width)] = projection;
        if (!projectionsOf.TryGetValue(phi, out var list)) projectionsOf[phi] = list = [];
        list.Add(projection);
        for (var i = 0; i < phi.Sources.Length; i++)
            if (phi.Sources[i] is { } source) projection.Sources[i] = Slice(source, low, width);
        return projection;
    }

    public Sym Concat(params Sym[] parts) => Concat((IEnumerable<Sym>)parts);

    public Sym Concat(IEnumerable<Sym> parts)
    {
        var flat = new List<Sym>();
        foreach (var part in parts)
            foreach (var segment in Segments(part))
                if (segment.Width > 0) Append(flat, segment);
        return flat.Count switch
        {
            0 => throw new ArgumentException("空拼接"),
            1 => flat[0],
            _ => JoinPhi(Intern(new ConcatSym(flat.ToArray()))),
        };
    }

    /// <summary>
    /// 同一合流的各片在每条入边上都连续覆盖同一个整体时，直接合流整体；不混用不同边的片。
    /// 错位复制把一个标量跨在两个寄存器 φ 上时，各片都只是 φ 的一部分，覆盖的是整体的连续一段，也合流这一段；
    /// 更宽的值可以按字段逐个取片，不需要合流。
    /// </summary>
    private Sym JoinPhi(ConcatSym concat)
    {
        if (joins.TryGetValue(concat, out var known)) return known;
        if (concat.Parts[0] is not PhiSym first || concat.Parts.Any(p => p is not PhiSym phi || phi.Block != first.Block)) return concat;
        var parts = concat.Parts.Cast<PhiSym>().ToArray();
        var misaligned = concat.Width <= 64 && parts.All(p => p.Projection is not null);
        var sources = new Sym[first.Sources.Length];
        for (var edge = 0; edge < sources.Length; edge++)
        {
            Sym? whole = null;
            var (start, at) = (0, 0);
            foreach (var part in parts)
            {
                if (part.Sources[edge] is not { } source) return concat;
                var (value, low, width) = Piece(Resolve(source));
                if (whole is null) (whole, start, at) = (value, low, low);
                if (!ReferenceEquals(whole, value) || low != at) return concat;
                at += width;
            }
            if (whole is null || !misaligned && (start != 0 || at != whole.Width)) return concat;
            sources[edge] = Slice(whole, start, at - start);
        }
        var joined = Phi(first.Block, concat, concat.Width);
        joins[concat] = joined;
        foreach (var part in parts)
        {
            if (!joinsOf.TryGetValue(part, out var list)) joinsOf[part] = list = [];
            list.Add(concat);
        }
        for (var edge = 0; edge < sources.Length; edge++) SetSource(joined, edge, sources[edge]);
        return joined;
    }

    private void Append(List<Sym> parts, Sym next)
    {
        if (parts.Count == 0) { parts.Add(next); return; }
        var last = parts[^1];
        Sym? merged = (last, next) switch
        {
            (ConstSym a, ConstSym b) when a.Width + b.Width <= 64 => Const(a.Value | b.Value << a.Width, a.Width + b.Width),
            (UndefSym a, UndefSym b) => Undef(a.Width + b.Width),
            _ when Piece(last) is var (lb, ll, lw) && Piece(next) is var (nb, nl, nw) && ReferenceEquals(lb, nb) && ll + lw == nl => Slice(lb, ll, lw + nw),
            _ => null,
        };
        if (merged is null) { parts.Add(next); return; }
        parts.RemoveAt(parts.Count - 1);
        Append(parts, merged);
    }

    private static (Sym Base, int Low, int Width) Piece(Sym sym) => sym switch
    {
        SliceSym s => (s.Base, s.Low, s.Width),
        PhiSym { Projection: { } p } phi => (p.Whole, p.Low, phi.Width),
        _ => (sym, 0, sym.Width),
    };

    public Sym ZeroExtend(Sym sym, int width) => sym.Width >= width ? Slice(sym, 0, width) : Concat(sym, Zero(width - sym.Width));

    /// <summary>把值放到 width 位的存储中，高位未定义（ABI 不保证的位）。</summary>
    public Sym Widen(Sym sym, int width) => sym.Width >= width ? Slice(sym, 0, width) : Concat(sym, Undef(width - sym.Width));

    public Sym Op(Operator op, int width, params Sym[] args) => Intern(new OpSym(op, args.Select(Resolve).ToArray(), width));

    public Sym Binary(BinOp op, Sym left, Sym right, int width)
    {
        left = Resolve(left);
        right = Resolve(right);
        // 模 2 算术：低一位的加减等于异或，乘法等于与。
        if (width == 1 && op is BinOp.Add or BinOp.Sub or BinOp.Mul)
            return Binary(op == BinOp.Mul ? BinOp.And : BinOp.Xor, Slice(left, 0, 1), Slice(right, 0, 1), 1);
        if (left is ConstSym lc && right is ConstSym rc && left.Width <= 64 && right.Width <= 64
            && Fold.Binary(op, new IrConst(lc.Value, lc.Width), new IrConst(rc.Value, rc.Width), width) is IrConst folded)
            return Const(folded.Value, width);
        if (left is ConstSym && op is BinOp.Add or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor)
            (left, right) = (right, left);
        var shift = ConstantAmount(right);
        switch (op)
        {
            case BinOp.Shl when shift >= 0:
                return shift >= width ? Zero(width) : Concat(Zero(shift), Slice(left, 0, width - shift));
            case BinOp.LShr when shift >= 0:
                return shift >= width ? Zero(width) : Concat(Slice(left, shift, width - shift), Zero(shift));
            case BinOp.AShr when shift >= 0:
                shift = Math.Min(shift, width - 1);
                return shift == 0 ? left : Convert(ConvKind.SignExtend, Slice(left, shift, width - shift), width);
            case BinOp.Ror when shift >= 0:
                shift %= width;
                return shift == 0 ? left : Concat(Slice(left, shift, width - shift), Slice(left, 0, shift));
            case BinOp.And or BinOp.Or or BinOp.Xor when Bitwise(op, left, right, width) is { } bits:
                return bits;
            case BinOp.Add or BinOp.Sub when right is ConstSym { Value: 0 }:
                return left;
            // InstCombine 把 sext(x + c) << k 写成 ((x << n) + (c << n)) asr (n - k)。低半部分全零的加减不产生进位，只作用于高半部分。
            case BinOp.Add or BinOp.Sub when left.Width == width && right.Width == width && Math.Min(LowZeros(left), LowZeros(right)) is var zeros && zeros >= width / 2:
                return Concat(Zero(zeros), Binary(op, Slice(left, zeros, width - zeros), Slice(right, zeros, width - zeros), width - zeros));
            case BinOp.Sub when right is ConstSym c:
                return Binary(BinOp.Add, left, Const(0 - c.Value, c.Width), width);
            case BinOp.Add when right is ConstSym c && left is LocalSym local:
                return Local(local.Space, local.Offset + c.Signed);
            case BinOp.Add when right is ConstSym c && left is OpSym { Op: { Kind: OperatorKind.Binary } inner, Args: [var x, ConstSym c0] } && inner.Binary == BinOp.Add:
                return Binary(BinOp.Add, x, Const(c0.Value + c.Value, width), width);
            case BinOp.Mul when right is ConstSym { Value: 1 }:
                return left;
        }
        return Op(Operator.Of(op), width, left, right);
    }

    /// <summary>常量移位量；向量宽度的常量是低 64 位与全零高位的拼接。其余为 -1。</summary>
    private static int ConstantAmount(Sym amount) => amount switch
    {
        ConstSym { Width: <= 64 } constant => (int)Math.Min(constant.Value, int.MaxValue),
        ConcatSym { Parts: [ConstSym { Width: <= 64 } low, ..] } wide when wide.Parts.Skip(1).All(IsZero) => (int)Math.Min(low.Value, int.MaxValue),
        _ => -1,
    };

    /// <summary>已知为零的最低位数。</summary>
    private static int LowZeros(Sym sym) => sym switch
    {
        ConstSym { Value: not 0, Width: <= 64 } c => System.Numerics.BitOperations.TrailingZeroCount(c.Value),
        ConcatSym { Parts: [ConstSym { Value: 0 } zero, ..] } => zero.Width,
        _ => 0,
    };

    /// <summary>按位运算逐段化简：掩码保留或清零片，与零的或、异或保留另一侧。不能逐段确定时返回 null。</summary>
    private Sym? Bitwise(BinOp op, Sym left, Sym right, int width)
    {
        if (left.Width != width || right.Width != width) return null;
        var bounds = new SortedSet<int> { 0, width };
        foreach (var side in new[] { left, right })
        {
            var at = 0;
            foreach (var segment in Segments(side)) { at += segment.Width; bounds.Add(at); }
        }
        if (right is ConstSym mask)
            for (var bit = 1; bit < width; bit++)
                if ((mask.Value >> bit & 1) != (mask.Value >> (bit - 1) & 1)) bounds.Add(bit);
        if (bounds.Count > 18) return null;
        var parts = new List<Sym>();
        var points = bounds.ToArray();
        for (var k = 0; k + 1 < points.Length; k++)
        {
            var (low, size) = (points[k], points[k + 1] - points[k]);
            var a = Slice(left, low, size);
            var b = Slice(right, low, size);
            var ones = Expr.Mask(size);
            Sym? part = op switch
            {
                BinOp.And when IsZero(a) || IsZero(b) => Zero(size),
                BinOp.And when b is ConstSym cb && cb.Value == ones => a,
                BinOp.And when a is ConstSym ca && ca.Value == ones => b,
                BinOp.Or or BinOp.Xor when IsZero(b) => a,
                BinOp.Or or BinOp.Xor when IsZero(a) => b,
                _ => null,
            };
            if (part is null) return null;
            parts.Add(part);
        }
        return Concat(parts);
    }

    public Sym Unary(UnOp op, Sym operand, int width)
    {
        operand = Resolve(operand);
        if (op == UnOp.Not && width == 1 && operand.Width == 1) return Not(operand);
        if (operand is ConstSym c && Fold.Unary(op, new IrConst(c.Value, c.Width), width) is IrConst folded) return Const(folded.Value, width);
        if (op == UnOp.Not && operand is OpSym { Op: { Kind: OperatorKind.Unary } inner, Args: [var x] } && inner.Unary == UnOp.Not) return x;
        return Op(Operator.Of(op), width, operand);
    }

    public Sym Convert(ConvKind kind, Sym operand, int width)
    {
        operand = Resolve(operand);
        switch (kind)
        {
            case ConvKind.ZeroExtend: return ZeroExtend(operand, width);
            case ConvKind.Truncate: return Slice(operand, 0, width);
            case ConvKind.Bitcast when operand.Width == width: return operand;
            case ConvKind.SignExtend when operand.Width >= width: return Slice(operand, 0, width);
            case ConvKind.SignExtend when operand is ConstSym c: return Const(unchecked((ulong)c.Signed), width);
            // 符号扩展只看最高位，低位的零片留在原位；形式与 sext(x) << k 的规范化相同。
            case ConvKind.SignExtend when operand is ConcatSym { Parts: [ConstSym { Value: 0 } zero, ..] }:
                return Concat(zero, Slice(Convert(ConvKind.SignExtend, Slice(operand, zero.Width, operand.Width - zero.Width), width), 0, width - zero.Width));
        }
        if (operand is ConstSym k && operand.Width <= 64 && Fold.Convert(kind, new IrConst(k.Value, k.Width), width) is IrConst folded)
            return Const(folded.Value, width);
        return Op(Operator.Of(kind), width, operand);
    }

    public Sym Compare(Cond cond, Sym left, Sym right)
    {
        left = Resolve(left);
        right = Resolve(right);
        if (left is ConstSym lc && right is ConstSym rc && Fold.Compare(cond, new IrConst(lc.Value, lc.Width), new IrConst(rc.Value, rc.Width)) is IrConst folded)
            return Const(folded.Value, 1);
        // 只取 0/1 的值与 0 或 1 的相等比较就是那一位或其否定。
        if (cond is Cond.Eq or Cond.Ne)
        {
            var (value, constant) = left is ConstSym ? (right, left as ConstSym) : (left, right as ConstSym);
            if (constant is { Value: 0 or 1 } && Bit(value) is { } bit)
                return (cond == Cond.Ne) == (constant.Value == 0) ? bit : Not(bit);
        }
        return Op(Operator.Of(cond), 1, left, right);
    }

    public Sym Select(Sym condition, Sym whenTrue, Sym whenFalse, int width)
    {
        condition = Resolve(condition);
        if (condition is ConstSym c) return c.Value != 0 ? whenTrue : whenFalse;
        if (ReferenceEquals(Resolve(whenTrue), Resolve(whenFalse))) return whenTrue;
        // 按条件选 1 或 0 就是条件位的零扩展。
        if (condition.Width == 1 && Resolve(whenTrue) is ConstSym t && Resolve(whenFalse) is ConstSym f && t.Value + f.Value == 1)
            return ZeroExtend(t.Value == 1 ? condition : Not(condition), width);
        return Op(new Operator(OperatorKind.Select, 0), width, condition, whenTrue, whenFalse);
    }

    /// <summary>只取 0/1 的值的那一位：1 位的值本身，或高位全为常量 0 的拼接的最低位；其余为 null。</summary>
    public static Sym? Bit(Sym sym)
    {
        sym = Resolve(sym);
        if (sym.Width == 1) return sym;
        if (sym is not ConcatSym { Parts: [{ Width: 1 } low, ..] } concat) return null;
        for (var i = 1; i < concat.Parts.Length; i++)
            if (Resolve(concat.Parts[i]) is not ConstSym { Value: 0 }) return null;
        return low;
    }

    public Sym Logical(bool isAnd, Sym left, Sym right)
    {
        left = Resolve(left);
        right = Resolve(right);
        if (left is ConstSym l) return (l.Value != 0) == isAnd ? right : left;
        if (right is ConstSym r) return (r.Value != 0) == isAnd ? left : right;
        return Op(new Operator(isAnd ? OperatorKind.And : OperatorKind.Or, 0), 1, left, right);
    }

    public Sym Not(Sym operand)
    {
        operand = Resolve(operand);
        return operand switch
        {
            ConstSym c => Const(c.Value == 0 ? 1UL : 0UL, 1),
            OpSym { Op.Kind: OperatorKind.Not, Args: [var inner] } => inner,
            OpSym { Op.Kind: OperatorKind.Compare } compare => Op(Operator.Of(Fold.Invert(compare.Op.Cond)), 1, compare.Args),
            _ => Op(new Operator(OperatorKind.Not, 0), 1, operand),
        };
    }

    /// <summary>机器内建操作；车道广播（vdup.N）只复制位，规范为拼接。</summary>
    public Sym Intrinsic(string name, Sym[] args, int width)
    {
        if (name.StartsWith("vdup.", StringComparison.Ordinal) && int.TryParse(name.AsSpan(5), out var lane) && lane > 0 && width % lane == 0
            && args is [var scalar] && scalar.Width >= lane)
            return Concat(Enumerable.Repeat(Slice(scalar, 0, lane), width / lane));
        return Op(new Operator(OperatorKind.Intrinsic, 0, name), width, args);
    }

    private sealed class SiteComparer : IEqualityComparer<(Stmt Site, int Ordinal)>
    {
        public bool Equals((Stmt Site, int Ordinal) x, (Stmt Site, int Ordinal) y) => ReferenceEquals(x.Site, y.Site) && x.Ordinal == y.Ordinal;
        public int GetHashCode((Stmt Site, int Ordinal) obj) => HashCode.Combine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(obj.Site), obj.Ordinal);
    }
}
