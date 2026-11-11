using System.Collections.Immutable;
using System.Numerics;
using System.Runtime.CompilerServices;
using static Cpp2CS.Native.Terms.CoreOperation;

[assembly: InternalsVisibleTo("Cpp2CS.Tests")]

namespace Cpp2CS.Native.Terms;

/// <summary>
/// 规则按位精化；删除依赖的恒等式必须对未定义位的任意取值成立。
/// 终止方向：运算降为位片，片向子项下推，拼接展平合并；不把位片升回搬运运算。
/// 算术改写向取反、取负、减法和严格小于归一；常量结合减少运算节点，排序只做一次。
/// </summary>
public sealed partial class TermTable
{
    private readonly Dictionary<(Term Source, int Low, int Width), Term> slices = new();
    // 限制分段产生的节点数量；17 段沿用位搬运规则的成本预算，不影响正确性。
    private const int MaximumMaskSegments = 17;
    // 只在至少减半算术位宽时主动拆开零片，避免为少量零位扩大图。
    private const int LowZeroWidthReduction = 2;
    private Term Op(CoreOperation op, int width, params ReadOnlySpan<Term> args) => Apply(new CoreOperator(op), width, args);
    private static bool Is(Term term, CoreOperation op) => term.Operator is CoreOperator core && core.Operation == op;
    private static BigInteger Mask(int width) => TermEvaluator.Mask(width);
    private Term Number(BigInteger value, int width) => Constant(value & Mask(width), width);

    private Term NormalizeOperation(CoreOperator core, int width, ImmutableArray<Term> args)
    {
        var op = core.Operation;
        var a = args[0];
        var b = args.Length > 1 ? args[1] : a;
        // select(1,x,y)=x，select(0,x,y)=y。检查：select-constant。
        if (op == Select && a.ConstantValue is { } condition) return args[condition.IsZero ? 2 : 1];
        var allConstants = true;
        foreach (var arg in args) allConstants &= arg.Kind == TermKind.Constant;
        // op(常量...) 按核心语义求值。检查：constant-fold、undefined-fold。
        if (allConstants)
        {
            var folded = TermEvaluator.EvaluateCore(op, width, a.Width, args.Select(t => t.ConstantValue!.Value).ToArray());
            if (folded.Status == EvaluationStatus.Defined) return Constant(folded.Bits, width);
            if (folded.Status == EvaluationStatus.Undefined) return Undefined(width);
        }
        // 交换律：常量在右，其余按驻留序号排序。检查：operand-order、constant-order。
        if (op is Add or Multiply or And or Or or Xor or Equal)
        {
            var constantFirst = a.Kind == TermKind.Constant && b.Kind != TermKind.Constant;
            var reverseOrder = a.Kind != TermKind.Constant && b.Kind != TermKind.Constant && a.Order > b.Order;
            if (constantFirst || reverseOrder)
            {
                (a, b) = (b, a);
                args = [a, b];
            }
        }
        var result = NormalizeSameOperands(op, width, a, b) ?? (op switch
        {
            ZeroExtend or SignExtend or Truncate => NormalizeExtensions(op, width, a, b, args),
            Select => NormalizeSelection(op, width, a, b, args),
            Not or Negate => NormalizeBoolean(op, width, a, b, args),
            Add or Subtract or Multiply => NormalizeBoolean(op, width, a, b, args)
                ?? NormalizeArithmetic(op, width, a, b, args),
            Equal or NotEqual or SignedLess or UnsignedLess or SignedLessEqual or UnsignedLessEqual =>
                NormalizeBoolean(op, width, a, b, args) ?? NormalizeComparisons(op, width, a, b, args),
            ShiftLeft or LogicalShiftRight or ArithmeticShiftRight or RotateRight => NormalizeShifts(op, width, a, b, args),
            And or Or or Xor => CombineConstants(op, width, a, b) ?? NormalizeBitOperations(op, width, a, b, args),
            _ => null
        });
        if (result is not null) return result;
        // op(U, ...) = U；选择只读取条件。检查：undefined-operation。
        foreach (var arg in args)
        {
            if (arg.Kind == TermKind.Undefined) return Undefined(width);
            if (op == Select) break;
        }
        return Intern(TermKind.Operation, width, core, args);
    }

    private Term? NormalizeExtensions(CoreOperation op, int width, Term a, Term b, ImmutableArray<Term> args)
    {
        // zext(x)=concat(x,0)。检查：zero-extend。
        if (op == ZeroExtend) return Concat(a, Constant(0, width - a.Width));
        // trunc(x)=slice(x,0,w)。检查：truncate。
        if (op == Truncate) return Slice(a, 0, width);
        if (op == SignExtend)
        {
            // sext(sext(x))=sext(x)。检查：nested-sign。
            if (Is(a, SignExtend)) return Op(SignExtend, width, a.Operands[0]);
            // sext(concat(...,c))：最高一段是常量时符号位已知，高位填全 0 或全 1。检查：sign-known-top。
            if (a.Kind == TermKind.Concat && a.Operands[^1].ConstantValue is { } top)
            {
                var negative = top.TestBit(a.Operands[^1].Width - 1);
                var fill = width - a.Width;
                return Concat(a, Constant(negative ? Mask(fill) : 0, fill));
            }
            // sext(concat(0,x))=concat(0,sext(x))。检查：sign-low-zero。
            if (a.Kind == TermKind.Concat && a.Operands[0].ConstantValue == 0)
            {
                var padding = a.Operands[0].Width;
                return Concat(a.Operands[0], Op(SignExtend, width - padding, Slice(a, padding, a.Width - padding)));
            }
        }
        return null;
    }

    private Term? NormalizeSelection(CoreOperation op, int width, Term a, Term b, ImmutableArray<Term> args)
    {
        if (op == Select)
        {
            // select(c,x,x)=x，包括未定义条件。检查：select-same、undefined-select。
            if (ReferenceEquals(b, args[2])) return b;
            // select(c,1,0)=zext(c)，反向分支取反。检查：select-bit、select-inverted-bit。
            if (b.ConstantValue is { } yes && args[2].ConstantValue is { } no && yes + no == 1)
            {
                var bit = yes == 1 ? a : Op(Not, 1, a);
                return width == 1 ? bit : Op(ZeroExtend, width, bit);
            }
        }
        return null;
    }

    private Term? NormalizeBoolean(CoreOperation op, int width, Term a, Term b, ImmutableArray<Term> args)
    {
        // 一位加减为 xor，一位乘法为 and。检查：bit-add、bit-subtract、bit-multiply。
        if (width == 1 && op is Add or Subtract or Multiply)
            return Op(op == Multiply ? And : Xor, width, a, b);
        // ~~x=x，-(-x)=x。检查：double-not、double-negate。
        if (op is Not or Negate && Is(a, op)) return a.Operands[0];
        // x!=y=~(x==y)。检查：not-equal。
        if (op == NotEqual) return Op(Not, 1, Op(Equal, 1, a, b));
        // x<=y=~(y<x)。检查：signed-nonstrict、unsigned-nonstrict。
        if (op is SignedLessEqual or UnsignedLessEqual)
            return Op(Not, 1, Op(op == SignedLessEqual ? SignedLess : UnsignedLess, 1, b, a));
        return null;
    }

    private Term? NormalizeSameOperands(CoreOperation op, int width, Term a, Term b)
    {
        // x&x=x，x|x=x；相同引用不需要给未定义位赋值。检查：same-and、same-or。
        if (ReferenceEquals(a, b) && op is And or Or) return a;
        // x^x=x-x=0，x==x=1，x<x=0；子图不含 U。检查：same-xor/subtract/equal/signed/unsigned。
        if (ReferenceEquals(a, b) && !a.ContainsUndefined)
        {
            if (op is Xor or Subtract or SignedLess or UnsignedLess) return Constant(0, width);
            if (op == Equal) return Constant(1, width);
        }
        return null;
    }

    private Term? NormalizeComparisons(CoreOperation op, int width, Term a, Term b, ImmutableArray<Term> args)
    {
        // zext(bit)==1 为 bit，==0 为 ~bit。检查：equal-bit-zero、equal-bit-one。
        if (op == Equal && b.ConstantValue is { } boolean && boolean >= 0 && boolean <= 1 && Bit(a) is { } bitValue)
            return boolean.IsZero ? Op(Not, 1, bitValue) : bitValue;
        if (op is Equal or SignedLess or UnsignedLess)
        {
            // 比较同宽零扩展等于无符号比较原值。检查：compare-zero-extends。
            var pairedConcat = a.Kind == TermKind.Concat && b.Kind == TermKind.Concat &&
                a.Operands.Length == 2 && b.Operands.Length == 2;
            if (pairedConcat)
            {
                var matchingLowWidths = a.Operands[0].Width == b.Operands[0].Width;
                var zeroHighParts = a.Operands[1].ConstantValue == 0 && b.Operands[1].ConstantValue == 0;
                if (matchingLowWidths && zeroHighParts)
                    return Op(op == SignedLess ? UnsignedLess : op, 1, a.Operands[0], b.Operands[0]);
            }
            // 比较同宽符号扩展等于比较原值。检查：compare-sign-extends。
            if (Is(a, SignExtend) && Is(b, SignExtend) && a.Operands[0].Width == b.Operands[0].Width)
                return Op(op, 1, a.Operands[0], b.Operands[0]);
        }
        // x <u 0 = 0，x <u 1 = (x==0)。检查：unsigned-zero、unsigned-one。
        if (op == UnsignedLess && b.ConstantValue == 0) return Constant(0, 1);
        if (op == UnsignedLess && b.ConstantValue == 1) return Op(Equal, 1, a, Constant(0, a.Width));
        // x <s min = 0。检查：signed-minimum。
        if (op == SignedLess && b.ConstantValue == (BigInteger.One << (a.Width - 1))) return Constant(0, 1);
        // (a-b)==0、(a^b)==0 均为 a==b。检查：equal-subtract、equal-xor。
        if (op == Equal && b.ConstantValue == 0 && (Is(a, Subtract) || Is(a, Xor)))
            return Op(Equal, 1, a.Operands[0], a.Operands[1]);
        // (a+~b)==全一 等于 a==b，按相同位宽的模算术。检查：equal-complement-add。
        if (op == Equal && b.ConstantValue == Mask(a.Width) && Is(a, Add))
        {
            if (Is(a.Operands[0], Not)) return Op(Equal, 1, a.Operands[0].Operands[0], a.Operands[1]);
            if (Is(a.Operands[1], Not)) return Op(Equal, 1, a.Operands[0], a.Operands[1].Operands[0]);
        }
        // (a+c1)==c2 = a==(c2-c1)，常量按位宽取模。检查：equal-add。
        if (op == Equal && b.ConstantValue is { } target && Is(a, Add) && a.Operands[1].ConstantValue is { } offset)
            return Op(Equal, 1, a.Operands[0], Number(target - offset, a.Width));
        // max<x=0；其余 c<x=~(x<c+1)。检查：compare-constant-max、compare-constant-left。
        if (op is SignedLess or UnsignedLess && a.ConstantValue is { } bound)
        {
            var maximum = op == SignedLess ? (BigInteger.One << (a.Width - 1)) - 1 : Mask(a.Width);
            if (bound == maximum)
            {
                return Constant(0, 1);
            }
            else return Op(Not, 1, Op(op, 1, b, Number(bound + 1, a.Width)));
        }
        return null;
    }

    private Term? NormalizeShifts(CoreOperation op, int width, Term a, Term b, ImmutableArray<Term> args)
    {
        // 常量移位化为切片拼接或符号扩展。检查：shift-left/right/signed、rotate、shift-zero/invalid。
        if (op is ShiftLeft or LogicalShiftRight or ArithmeticShiftRight or RotateRight && b.ConstantValue is { } amount)
        {
            if (op != RotateRight && amount >= width) return Undefined(width);
            var shift = (int)(amount % width);
            if (shift == 0) return a;
            return op switch
            {
                ShiftLeft => Concat(Constant(0, shift), Slice(a, 0, width - shift)),
                LogicalShiftRight => Concat(Slice(a, shift, width - shift), Constant(0, shift)),
                ArithmeticShiftRight => Op(SignExtend, width, Slice(a, shift, width - shift)),
                _ => Concat(Slice(a, shift, width - shift), Slice(a, 0, shift))
            };
        }
        return null;
    }

    private Term? CombineConstants(CoreOperation op, int width, Term a, Term b)
    {
        // (x op c1) op c2=x op (c1 op c2)。检查：combine-add/multiply/and/or/xor。
        if (op is Add or Multiply or And or Or or Xor && b.ConstantValue is { } outer && Is(a, op) && a.Operands[1].ConstantValue is { } inner)
        {
            var combined = TermEvaluator.EvaluateCore(op, width, width, new[] { inner, outer });
            return Op(op, width, a.Operands[0], Constant(combined.Bits, width));
        }
        return null;
    }

    private Term? NormalizeArithmetic(CoreOperation op, int width, Term a, Term b, ImmutableArray<Term> args)
    {
        // x+0=x，x*1=x，x*0=0。检查：add-zero、multiply-one、multiply-zero。
        if (b.ConstantValue == 0 && op == Add) return a;
        if (b.ConstantValue == 1 && op == Multiply) return a;
        if (b.ConstantValue == 0 && op == Multiply) return Constant(0, width);
        // 0-x=-x。检查：zero-subtract。
        if (op == Subtract && a.ConstantValue == 0) return Op(Negate, width, b);
        // x+(-y)=(-y)+x=x-y。检查：add-negate、negate-add。
        if (op == Add && Is(b, Negate)) return Op(Subtract, width, a, b.Operands[0]);
        if (op == Add && Is(a, Negate)) return Op(Subtract, width, b, a.Operands[0]);
        // x-(-y)=x+y。检查：subtract-negate。
        if (op == Subtract && Is(b, Negate)) return Op(Add, width, a, b.Operands[0]);
        // x-c=x+(-c)，常量按位宽取模。检查：subtract-constant。
        if (op == Subtract && b.ConstantValue is { } subtract) return Op(Add, width, a, Number(-subtract, width));
        if (CombineConstants(op, width, a, b) is { } combined) return combined;
        // concat(0,x) ± concat(0,y)=concat(0,x±y)。检查：add-low-zeros、subtract-low-zeros。
        if (op is Add or Subtract)
        {
            var zeros = Math.Min(LowZeros(a), LowZeros(b));
            var worthwhile = zeros >= (width + LowZeroWidthReduction - 1) / LowZeroWidthReduction;
            if (zeros > 0 && zeros < width && worthwhile)
                return Concat(Constant(0, zeros), Op(op, width - zeros, Slice(a, zeros, width - zeros), Slice(b, zeros, width - zeros)));
        }
        // x*2^k=x<<k。检查：multiply-power。
        if (op == Multiply && b.ConstantValue is { } power && power > 1 && (power & (power - 1)) == 0)
            return Op(ShiftLeft, width, a, Constant(power.GetBitLength() - 1, width));
        return null;
    }

    private Term? NormalizeBitOperations(CoreOperation op, int width, Term a, Term b, ImmutableArray<Term> args)
    {
        // x|0=x^0=x。检查：or-zero、xor-zero。
        if (b.ConstantValue == 0 && op is Or or Xor) return a;
        // x^全1=~x。检查：xor-ones、xor-bit-one。
        if (b.ConstantValue == Mask(width) && op == Xor) return Op(Not, width, a);
        // x&全1=x。检查：and-ones。
        if (b.ConstantValue == Mask(width) && op == And) return a;
        // x&0=0，包括未定义输入。检查：and-zero、undefined-and-zero。
        if (b.ConstantValue == 0 && op == And) return Constant(0, width);
        // x|全1=全1，包括未定义输入。检查：or-ones、undefined-or-ones。
        if (b.ConstantValue == Mask(width) && op == Or) return b;
        // 按边界分片应用位恒等式。检查：mask、insert、undefined-mask。
        if (op is And or Or or Xor && Bitwise(op, a, b, width) is { } bits) return bits;
        return null;
    }

    private static Term? Bit(Term t) => t.Width == 1 ? t :
        t.Kind == TermKind.Concat && t.Operands[0].Width == 1 && t.Operands.Skip(1).All(p => p.ConstantValue == 0) ? t.Operands[0] : null;

    private int LowZeros(Term t)
    {
        if (t.ConstantValue is { } value)
        {
            var zeros = 0;
            while (zeros < t.Width && !value.TestBit(zeros)) zeros++;
            return zeros;
        }
        if (t.Kind != TermKind.Concat) return 0;
        var count = 0;
        foreach (var part in t.Operands)
        {
            var n = LowZeros(part);
            count += n;
            if (n != part.Width) break;
        }
        return count;
    }

    private Term NormalizeSlice(Term source, int low, int width)
    {
        var key = (source, low, width);
        if (slices.TryGetValue(key, out var known)) return known;
        // 低位算术链按后序处理；共享子项的同一切片只计算一次。
        var pending = new Stack<(Term Source, bool Ready)>();
        pending.Push((source, false));
        while (pending.TryPop(out var item))
        {
            var request = (item.Source, low, width);
            if (slices.ContainsKey(request)) continue;
            var arithmetic = low == 0 && item.Source.Width > width &&
                item.Source.Operator is CoreOperator { Operation: Add or Subtract or Multiply or And or Or or Xor };
            if (!item.Ready && arithmetic)
            {
                pending.Push((item.Source, true));
                foreach (var child in item.Source.Operands) pending.Push((child, false));
                continue;
            }
            slices[request] = NormalizeSliceCore(item.Source, low, width);
        }
        return slices[key];
    }

    private Term NormalizeSliceCore(Term source, int low, int width)
    {
        // slice(x,0,width(x))=x。检查：slice-full。
        if (low == 0 && width == source.Width) return source;
        // slice(c,l,w)=(c>>l) mod 2^w。检查：slice-constant。
        if (source.ConstantValue is { } value) return Number(value >> low, width);
        // slice(U,l,w)=U:w。检查：slice-undefined。
        if (source.Kind == TermKind.Undefined) return Undefined(width);
        // slice(slice(x,a,b),l,w)=slice(x,a+l,w)。检查：slice-slice。
        if (source.Kind == TermKind.Slice) return Slice(source.Operands[0], low + source.SliceLow!.Value, width);
        // slice(concat(...)) 只保留相交片段。检查：slice-concat、undefined-slice。
        if (source.Kind == TermKind.Concat)
        {
            var at = 0;
            var pieces = new List<Term>();
            foreach (var part in source.Operands)
            {
                var from = Math.Max(low, at);
                var to = Math.Min(low + width, at + part.Width);
                if (from < to) pieces.Add(Slice(part, from - at, to - from));
                at += part.Width;
            }
            return Concat(pieces.ToArray());
        }
        // slice(sext(x)) 按原值、跨界、符号位三段处理。检查：slice-sign-low/cross/high。
        if (Is(source, SignExtend))
        {
            var original = source.Operands[0];
            if (low + width <= original.Width) return Slice(original, low, width);
            if (low < original.Width) return Op(SignExtend, width, Slice(original, low, original.Width - low));
            var sign = Slice(original, original.Width - 1, 1);
            return width == 1 ? sign : Op(SignExtend, width, sign);
        }
        if (source.Operator is CoreOperator core)
        {
            var op = core.Operation;
            // 位运算任意片、算术低片、无低位进借位的加减高片可下推。检查：slice-bitwise/low-arithmetic/high-add/high-subtract。
            var bitwise = op is And or Or or Xor;
            var lowArithmetic = low == 0 && op is Add or Subtract or Multiply;
            var highArithmetic = low > 0 && op is Add or Subtract &&
                (LowZeros(source.Operands[1]) >= low || op == Add && LowZeros(source.Operands[0]) >= low);
            if (bitwise || lowArithmetic || highArithmetic)
                return Op(op, width, Slice(source.Operands[0], low, width), Slice(source.Operands[1], low, width));
            // slice(~x)=~slice(x)，低片(-x)=-低片(x)。检查：slice-not、slice-negate。
            if (op == Not || low == 0 && op == Negate) return Op(op, width, Slice(source.Operands[0], low, width));
            // slice(select(c,x,y))=select(c,slice(x),slice(y))。检查：slice-select。
            if (op == Select) return Op(Select, width, source.Operands[0], Slice(source.Operands[1], low, width), Slice(source.Operands[2], low, width));
        }
        return Intern(TermKind.Slice, width, low, [source]);
    }

    private Term NormalizeConcat(ImmutableArray<Term> values)
    {
        var parts = new List<Term>();
        void Append(Term part)
        {
            // concat(...concat(...)...)=concat(...)。检查：concat-flat。
            if (part.Kind == TermKind.Concat)
            {
                foreach (var p in part.Operands) Append(p);
                return;
            }
            if (parts.Count > 0)
            {
                var last = parts[^1];
                Term? merged = null;
                // concat(c1,c2)=c1|(c2<<width(c1))。检查：concat-constants。
                if (last.ConstantValue is { } a && part.ConstantValue is { } b) merged = Constant(a | (b << last.Width), checked(last.Width + part.Width));
                // concat(U,U)=U。检查：concat-undefined。
                else if (last.Kind == TermKind.Undefined && part.Kind == TermKind.Undefined) merged = Undefined(checked(last.Width + part.Width));
                // 同源相邻片拼成一片。检查：concat-adjacent。
                else if (last.Kind == TermKind.Slice && part.Kind == TermKind.Slice)
                {
                    var sameSource = ReferenceEquals(last.Operands[0], part.Operands[0]);
                    var adjacent = last.SliceLow + last.Width == part.SliceLow;
                    if (sameSource && adjacent)
                        merged = Slice(last.Operands[0], last.SliceLow!.Value, checked(last.Width + part.Width));
                }
                if (merged is not null)
                {
                    parts.RemoveAt(parts.Count - 1);
                    Append(merged);
                    return;
                }
            }
            parts.Add(part);
        }
        foreach (var value in values) Append(value);
        // concat(x)=x。检查：concat-single。
        return parts.Count == 1 ? parts[0] : Intern(TermKind.Concat, checked(parts.Sum(p => p.Width)), null, [.. parts]);
    }

    private Term? Bitwise(CoreOperation op, Term a, Term b, int width)
    {
        if (a.Kind != TermKind.Concat && b.Kind != TermKind.Concat && b.Kind != TermKind.Constant) return null;
        var bounds = new SortedSet<int> { 0, width };
        foreach (var side in new[] { a, b })
        {
            if (side.Kind == TermKind.Concat)
            {
                var at = 0;
                foreach (var part in side.Operands)
                {
                    at += part.Width;
                    bounds.Add(at);
                }
            }
        }
        if (b.ConstantValue is { } mask)
            for (var i = 1; i < width; i++)
                if (mask.TestBit(i) != mask.TestBit(i - 1)) bounds.Add(i);
        if (bounds.Count <= 2 || bounds.Count - 1 > MaximumMaskSegments) return null;
        var points = bounds.ToArray();
        var parts = new List<Term>();
        for (var i = 0; i + 1 < points.Length; i++)
        {
            var size = points[i + 1] - points[i];
            var x = Slice(a, points[i], size);
            var y = Slice(b, points[i], size);
            Term? part = op switch
            {
                And when x.ConstantValue == 0 || y.ConstantValue == 0 => Constant(0, size),
                And when x.ConstantValue == Mask(size) => y,
                And when y.ConstantValue == Mask(size) => x,
                Or or Xor when x.ConstantValue == 0 => y,
                Or or Xor when y.ConstantValue == 0 => x,
                _ => null
            };
            if (part is null) return null;
            parts.Add(part);
        }
        return Concat(parts.ToArray());
    }
}
