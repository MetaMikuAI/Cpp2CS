using Cpp2CS.Snapshot;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>
/// 项的规范化的语义核对。依据是各运算符自身的定义：随机生成表达式，一边按定义直接求值，
/// 一边经项池构造（规范化）后再对得到的项求值，两者在随机取值与边界取值上必须相同。
/// 同时核对：同一个表达式构造两次得到同一个项；用项自己的操作数重建得到它自己。
/// </summary>
internal sealed class TermCheck
{
    private enum K
    {
        Variable, Constant, Add, Sub, Mul, Neg, And, Or, Xor, Not, Shl, LShr, AShr, UDiv, SDiv, URem, SRem,
        SignExtend, ZeroExtend, Slice, Concat, Select, Eq, Ne, Ult, Ule, Ugt, Uge, Slt, Sle, Sgt, Sge,
    }

    private sealed record Expr(K Kind, int Width, Expr[] Children, UInt128 Value = default, int A = 0);

    private static readonly int[] widths = [1, 2, 3, 5, 8, 16, 27, 32, 64, 128];
    private readonly List<UInt128> constants = [];
    private const int VariablesPerWidth = 3;

    private readonly Random random;
    private readonly TermPool pool = new();
    private readonly Dictionary<(int Width, int Index), Term> variables = [];

    public TermCheck(int seed) => random = new Random(seed);

    private static UInt128 Mask(int width) => width >= 128 ? UInt128.MaxValue : (UInt128.One << width) - 1;
    private static Int128 Signed(UInt128 value, int width) => width >= 128 ? (Int128)value : (Int128)(value << (128 - width)) >> (128 - width);

    private UInt128 RandomValue(int width)
    {
        UInt128 raw = ((UInt128)(ulong)random.NextInt64() << 64 | (ulong)random.NextInt64()) ^ ((UInt128)(ulong)random.NextInt64() << 1);
        // 取值偏向边界，以及表达式里出现过的常量及其邻近值：与常量的比较才有机会成立。
        if (constants.Count > 0 && random.Next(3) == 0)
            return unchecked(constants[random.Next(constants.Count)] + (UInt128)(Int128)(random.Next(5) - 2)) & Mask(width);
        return random.Next(8) switch
        {
            0 => UInt128.Zero,
            1 => Mask(width),
            2 => UInt128.One << (width - 1),
            3 => UInt128.One,
            4 => raw & Mask(Math.Min(width, 6)),
            5 => UInt128.One << random.Next(width),
            _ => raw & Mask(width),
        };
    }

    private int PickWidth() => widths[random.Next(2) == 0 ? random.Next(5) : random.Next(widths.Length)];

    private Expr Generate(int width, int depth)
    {
        if (depth == 0 || random.Next(4) == 0)
        {
            if (random.Next(2) != 0) return new Expr(K.Variable, width, [], A: random.Next(VariablesPerWidth));
            var constant = RandomValue(width);
            constants.Add(constant);
            return new Expr(K.Constant, width, [], constant);
        }
        Expr Sub(int w) => Generate(w, depth - 1);
        int other = PickWidth();
        switch (random.Next(width == 1 ? 26 : 18))
        {
            case 0: return new(K.Add, width, [Sub(width), Sub(width)]);
            case 1: return new(K.Sub, width, [Sub(width), Sub(width)]);
            case 2: return new(K.Mul, width, [Sub(width), Sub(width)]);
            case 3: return new(K.Neg, width, [Sub(width)]);
            case 4: return new(K.And, width, [Sub(width), Sub(width)]);
            case 5: return new(K.Or, width, [Sub(width), Sub(width)]);
            case 6: return new(K.Xor, width, [Sub(width), Sub(width)]);
            case 7: return new(K.Not, width, [Sub(width)]);
            case 8: return new((K)((int)K.Shl + random.Next(3)), width, [Sub(width), Sub(width)]);
            case 9: return new((K)((int)K.UDiv + random.Next(4)), width, [Sub(width), Sub(width)]);
            case 10 when width > 1: { int from = 1 + random.Next(width - 1); return new(K.SignExtend, width, [Sub(from)]); }
            case 11 when width > 1: { int from = 1 + random.Next(width - 1); return new(K.ZeroExtend, width, [Sub(from)]); }
            case 12 when other > width: return new(K.Slice, width, [Sub(other)], A: random.Next(other - width + 1));
            case 13 when width > 1: { int low = 1 + random.Next(width - 1); return new(K.Concat, width, [Sub(low), Sub(width - low)]); }
            case 14 or 15: return new(K.Select, width, [Sub(1), Sub(width), Sub(width)]);
            case >= 18: return new((K)((int)K.Eq + random.Next(10)), 1, [Sub(other), Sub(other)]);
            default: return new(K.Xor, width, [Sub(width), Sub(width)]);
        }
    }

    /// <summary>按运算符的定义求值。除数为零时，约定除得全 1、余得被除数（只为让两边一致，项池不折叠这种情形）。</summary>
    private static UInt128 Apply(Op op, int width, ReadOnlySpan<UInt128> x, ReadOnlySpan<int> operandWidths)
    {
        UInt128 mask = Mask(width);
        int w0 = operandWidths.Length > 0 ? operandWidths[0] : width;
        switch (op)
        {
            case Op.Add: return unchecked(x[0] + x[1]) & mask;
            case Op.Sub: return unchecked(x[0] - x[1]) & mask;
            case Op.Mul: return unchecked(x[0] * x[1]) & mask;
            case Op.Neg: return unchecked(UInt128.Zero - x[0]) & mask;
            case Op.And: return x[0] & x[1];
            case Op.Or: return x[0] | x[1];
            case Op.Xor: return x[0] ^ x[1];
            case Op.Not: return ~x[0] & mask;
            case Op.Shl: return x[1] >= (UInt128)width ? UInt128.Zero : (x[0] << (int)x[1]) & mask;
            case Op.LShr: return x[1] >= (UInt128)width ? UInt128.Zero : x[0] >> (int)x[1];
            case Op.AShr:
            {
                Int128 value = Signed(x[0], width);
                return unchecked((UInt128)(x[1] >= (UInt128)width ? (value < 0 ? -1 : 0) : value >> (int)x[1])) & mask;
            }
            case Op.UDiv: return x[1] == UInt128.Zero ? mask : x[0] / x[1];
            case Op.URem: return x[1] == UInt128.Zero ? x[0] : x[0] % x[1];
            case Op.SDiv or Op.SRem:
            {
                if (x[1] == UInt128.Zero) return op == Op.SDiv ? mask : x[0];
                Int128 a = Signed(x[0], width), b = Signed(x[1], width);
                if (b == -1) return op == Op.SDiv ? unchecked(UInt128.Zero - x[0]) & mask : UInt128.Zero;
                return unchecked((UInt128)(op == Op.SDiv ? a / b : a % b)) & mask;
            }
            case Op.SignExtend: return unchecked((UInt128)Signed(x[0], w0)) & mask;
            case Op.Eq: return x[0] == x[1] ? UInt128.One : UInt128.Zero;
            case Op.Ult: return x[0] < x[1] ? UInt128.One : UInt128.Zero;
            case Op.Slt: return Signed(x[0], w0) < Signed(x[1], w0) ? UInt128.One : UInt128.Zero;
            default: throw new InvalidOperationException($"核对不涉及 {op}");
        }
    }

    private UInt128 Reference(Expr e, Dictionary<(int, int), UInt128> assignment)
    {
        var c = e.Children;
        UInt128 X(int i) => Reference(c[i], assignment);
        UInt128 Binary(Op op) => Apply(op, e.Width, [X(0), X(1)], [c[0].Width, c[1].Width]);
        UInt128 Flip(UInt128 bit) => bit ^ UInt128.One;
        switch (e.Kind)
        {
            case K.Variable: return assignment[(e.Width, e.A)];
            case K.Constant: return e.Value;
            case K.Add: return Binary(Op.Add);
            case K.Sub: return Binary(Op.Sub);
            case K.Mul: return Binary(Op.Mul);
            case K.Neg: return Apply(Op.Neg, e.Width, [X(0)], [e.Width]);
            case K.And: return Binary(Op.And);
            case K.Or: return Binary(Op.Or);
            case K.Xor: return Binary(Op.Xor);
            case K.Not: return Apply(Op.Not, e.Width, [X(0)], [e.Width]);
            case K.Shl: return Binary(Op.Shl);
            case K.LShr: return Binary(Op.LShr);
            case K.AShr: return Binary(Op.AShr);
            case K.UDiv: return Binary(Op.UDiv);
            case K.SDiv: return Binary(Op.SDiv);
            case K.URem: return Binary(Op.URem);
            case K.SRem: return Binary(Op.SRem);
            case K.SignExtend: return Apply(Op.SignExtend, e.Width, [X(0)], [c[0].Width]);
            case K.ZeroExtend: return X(0);
            case K.Slice: return (X(0) >> e.A) & Mask(e.Width);
            case K.Concat: return X(0) | (X(1) << c[0].Width);
            case K.Select: return X(0) != UInt128.Zero ? X(1) : X(2);
            case K.Eq: return Binary(Op.Eq);
            case K.Ne: return Flip(Binary(Op.Eq));
            case K.Ult: return Binary(Op.Ult);
            case K.Uge: return Flip(Binary(Op.Ult));
            case K.Ugt: return Apply(Op.Ult, 1, [X(1), X(0)], [c[0].Width]);
            case K.Ule: return Flip(Apply(Op.Ult, 1, [X(1), X(0)], [c[0].Width]));
            case K.Slt: return Binary(Op.Slt);
            case K.Sge: return Flip(Binary(Op.Slt));
            case K.Sgt: return Apply(Op.Slt, 1, [X(1), X(0)], [c[0].Width]);
            case K.Sle: return Flip(Apply(Op.Slt, 1, [X(1), X(0)], [c[0].Width]));
            default: throw new InvalidOperationException();
        }
    }

    private Term Variable(int width, int index)
    {
        if (!variables.TryGetValue((width, index), out var term))
            variables[(width, index)] = term = pool.EntryParameter(0, new Slot(SlotKind.Integer, width * 16 + index), width);
        return term;
    }

    private Term Build(Expr e)
    {
        var c = e.Children;
        Term X(int i) => Build(c[i]);
        return e.Kind switch
        {
            K.Variable => Variable(e.Width, e.A),
            K.Constant => pool.Bits(e.Value, e.Width),
            K.Add => pool.Add(X(0), X(1)),
            K.Sub => pool.Sub(X(0), X(1)),
            K.Mul => pool.Mul(X(0), X(1)),
            K.Neg => pool.Neg(X(0)),
            K.And => pool.And(X(0), X(1)),
            K.Or => pool.Or(X(0), X(1)),
            K.Xor => pool.Xor(X(0), X(1)),
            K.Not => pool.Not(X(0)),
            K.Shl => pool.Shl(X(0), X(1)),
            K.LShr => pool.LShr(X(0), X(1)),
            K.AShr => pool.AShr(X(0), X(1)),
            K.UDiv => pool.Divide(Op.UDiv, X(0), X(1)),
            K.SDiv => pool.Divide(Op.SDiv, X(0), X(1)),
            K.URem => pool.Divide(Op.URem, X(0), X(1)),
            K.SRem => pool.Divide(Op.SRem, X(0), X(1)),
            K.SignExtend => pool.SignExtend(X(0), e.Width),
            K.ZeroExtend => pool.ZeroExtend(X(0), e.Width),
            K.Slice => pool.Slice(X(0), e.A, e.Width),
            K.Concat => pool.Concat(X(0), X(1)),
            K.Select => pool.Select(X(0), X(1), X(2)),
            K.Eq => pool.Eq(X(0), X(1)),
            K.Ne => pool.Ne(X(0), X(1)),
            K.Ult => pool.Ult(X(0), X(1)),
            K.Ule => pool.Ule(X(0), X(1)),
            K.Ugt => pool.Ugt(X(0), X(1)),
            K.Uge => pool.Uge(X(0), X(1)),
            K.Slt => pool.Slt(X(0), X(1)),
            K.Sle => pool.Sle(X(0), X(1)),
            K.Sgt => pool.Sgt(X(0), X(1)),
            _ => pool.Sge(X(0), X(1)),
        };
    }

    /// <summary>对规范化之后的项求值。</summary>
    private static UInt128 Evaluate(Term t, Dictionary<Term, UInt128> assignment, Dictionary<Term, UInt128> memo)
    {
        if (memo.TryGetValue(t, out var known)) return known;
        UInt128 result;
        switch (t.Kind)
        {
            case TermKind.Constant: result = t.Value; break;
            case TermKind.EntryParameter: result = assignment[t]; break;
            case TermKind.Slice: result = (Evaluate(t.Operands[0], assignment, memo) >> t.Offset) & Mask(t.Width); break;
            case TermKind.Concat:
            {
                result = UInt128.Zero;
                int at = 0;
                foreach (var part in t.Operands)
                {
                    result |= Evaluate(part, assignment, memo) << at;
                    at += part.Width;
                }
                break;
            }
            case TermKind.Select:
                result = Evaluate(t.Operands[0], assignment, memo) != UInt128.Zero
                    ? Evaluate(t.Operands[1], assignment, memo) : Evaluate(t.Operands[2], assignment, memo);
                break;
            case TermKind.Operation:
            {
                Span<UInt128> values = stackalloc UInt128[t.Operands.Length];
                Span<int> operandWidths = stackalloc int[t.Operands.Length];
                for (int i = 0; i < values.Length; i++)
                {
                    values[i] = Evaluate(t.Operands[i], assignment, memo);
                    operandWidths[i] = t.Operands[i].Width;
                }
                result = Apply(t.Op, t.Width, values, operandWidths);
                break;
            }
            default: throw new InvalidOperationException($"核对不涉及 {t.Kind}");
        }
        memo[t] = result;
        return result;
    }

    private static void Collect(Expr e, HashSet<(int, int)> used)
    {
        if (e.Kind == K.Variable) used.Add((e.Width, e.A));
        foreach (var child in e.Children) Collect(child, used);
    }

    private static string Print(Expr e) => e.Kind switch
    {
        K.Variable => $"v{e.Width}_{e.A}",
        K.Constant => $"0x{e.Value:x}:{e.Width}",
        K.Slice => $"{Print(e.Children[0])}[{e.A}+:{e.Width}]",
        _ => $"{e.Kind}:{e.Width}({string.Join(", ", e.Children.Select(Print))})",
    };

    public int Run(int rounds, int depth, int samples)
    {
        long comparisons = 0;
        int mismatches = 0, unstable = 0, notInterned = 0;
        for (int round = 0; round < rounds; round++)
        {
            constants.Clear();
            var expression = Generate(PickWidth(), depth);
            var term = Build(expression);
            var used = new HashSet<(int, int)>();
            Collect(expression, used);
            if (!ReferenceEquals(term, Build(expression))) notInterned++;
            if (term.Operands.Length > 0 && !ReferenceEquals(pool.Rebuild(term, term.Operands.AsSpan()), term)) unstable++;
            for (int s = 0; s < samples; s++)
            {
                var byIndex = new Dictionary<(int, int), UInt128>();
                var byTerm = new Dictionary<Term, UInt128>(ReferenceEqualityComparer.Instance);
                foreach (var (width, index) in used)
                {
                    var value = RandomValue(width);
                    byIndex[(width, index)] = value;
                    byTerm[Variable(width, index)] = value;
                }
                UInt128 expected = Reference(expression, byIndex);
                UInt128 actual = Evaluate(term, byTerm, new(ReferenceEqualityComparer.Instance));
                comparisons++;
                if (expected == actual) continue;
                if (++mismatches <= 5)
                {
                    Console.WriteLine($"不一致：{Print(expression)}");
                    Console.WriteLine($"  规范化为 {term}");
                    Console.WriteLine($"  按定义 0x{expected:x}，规范化后 0x{actual:x}");
                }
                break;
            }
        }
        Console.WriteLine($"项的语义核对：表达式 {rounds} 个，求值比较 {comparisons} 次，不一致 {mismatches} 个；" +
            $"重复构造不是同一个项 {notInterned} 个；重建后不是自己 {unstable} 个；池内项数 {pool.Count}");
        return mismatches + notInterned + unstable == 0 ? 0 : 1;
    }
}
