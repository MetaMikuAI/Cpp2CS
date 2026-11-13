using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>模板词汇解释到调用方的项表；相等只由公共项规范化给出。</summary>
internal sealed class AccessorTerms(TermTable terms, Func<int, Term?> parameter,
    Func<FieldRef, Term?, Term?> read)
{
    public Term? Read(ManagedValue value)
    {
        if (value.Width <= 0 || value.Width > 64) return null;
        if (value is ArgumentValue a) return parameter(a.Index) is { } input ? Resize(input, a.Width, ManagedTypes.IsSigned(a.Type)) : null;
        if (value is ConstantValue k) return terms.Constant(new System.Numerics.BigInteger(k.Bits) & ((System.Numerics.BigInteger.One << k.Width) - 1), k.Width);
        if (value is FieldValue f && Read(f.Receiver) is { } receiver)
            return read(f.Field, receiver) is { } instanceField ? Resize(instanceField, f.Width, ManagedTypes.IsSigned(f.Type)) : null;
        if (value is StaticFieldValue s) return read(s.Field, null) is { } staticField ? Resize(staticField, s.Width, ManagedTypes.IsSigned(s.Type)) : null;
        if (value is ConversionValue c && Read(c.Operand) is { } operand)
            return c.Kind is ConversionKind.ZeroExtend or ConversionKind.SignExtend or ConversionKind.Truncate
                ? Resize(operand, c.Width, c.Kind == ConversionKind.SignExtend) : null;
        if (value is UnaryValue u && Read(u.Operand) is { } unary)
        {
            CoreOperation? op = u.Op switch { UnaryOperator.Negate => CoreOperation.Negate, UnaryOperator.Not => CoreOperation.Not, _ => null };
            return op is null ? null : terms.Apply(new CoreOperator(op.Value), u.Width, Resize(unary, u.Width, ManagedTypes.IsSigned(u.Operand.Type)));
        }
        if (value is BinaryValue b && Read(b.Left) is { } left && Read(b.Right) is { } right)
        {
            CoreOperation? op = b.Op switch
            {
                BinaryOperator.Add => CoreOperation.Add, BinaryOperator.Subtract => CoreOperation.Subtract,
                BinaryOperator.Multiply => CoreOperation.Multiply, BinaryOperator.And => CoreOperation.And,
                BinaryOperator.Or => CoreOperation.Or, BinaryOperator.Xor => CoreOperation.Xor,
                BinaryOperator.ShiftLeft => CoreOperation.ShiftLeft, BinaryOperator.ShiftRightSigned => CoreOperation.ArithmeticShiftRight,
                BinaryOperator.ShiftRightUnsigned => CoreOperation.LogicalShiftRight, _ => null,
            };
            if (op is null) return null;
            left = Resize(left, b.Width, ManagedTypes.IsSigned(b.Left.Type));
            bool shift = b.Op is BinaryOperator.ShiftLeft or BinaryOperator.ShiftRightSigned or BinaryOperator.ShiftRightUnsigned;
            if (shift)
                right = Resize(terms.Apply(new CoreOperator(CoreOperation.And), right.Width, right, terms.Constant(b.Width == 64 ? 63 : 31, right.Width)), b.Width);
            else right = Resize(right, b.Width, ManagedTypes.IsSigned(b.Right.Type));
            return terms.Apply(new CoreOperator(op.Value), b.Width, left, right);
        }
        if (value is ComparisonValue cmp && Read(cmp.Left) is { } aLeft && Read(cmp.Right) is { } aRight)
        {
            int width = Math.Max(aLeft.Width, aRight.Width);
            aLeft = Resize(aLeft, width, ManagedTypes.IsSigned(cmp.Left.Type));
            aRight = Resize(aRight, width, ManagedTypes.IsSigned(cmp.Right.Type));
            bool reverse = cmp.Condition is ComparisonKind.SignedGreater or ComparisonKind.SignedGreaterOrEqual
                or ComparisonKind.UnsignedGreater or ComparisonKind.UnsignedGreaterOrEqual;
            CoreOperation? op = cmp.Condition switch
            {
                ComparisonKind.Equal => CoreOperation.Equal, ComparisonKind.NotEqual => CoreOperation.NotEqual,
                ComparisonKind.SignedLess or ComparisonKind.SignedGreater => CoreOperation.SignedLess,
                ComparisonKind.SignedLessOrEqual or ComparisonKind.SignedGreaterOrEqual => CoreOperation.SignedLessEqual,
                ComparisonKind.UnsignedLess or ComparisonKind.UnsignedGreater => CoreOperation.UnsignedLess,
                ComparisonKind.UnsignedLessOrEqual or ComparisonKind.UnsignedGreaterOrEqual => CoreOperation.UnsignedLessEqual, _ => null,
            };
            if (op is null) return null;
            var result = terms.Apply(new CoreOperator(op.Value), 1, reverse ? aRight : aLeft, reverse ? aLeft : aRight);
            return Resize(result, cmp.Width, false);
        }
        return null;
    }
    /// <summary>只投影已知零高位；补回原位宽后必须仍是同一个项。</summary>
    public Term Result(Term value)
    {
        if (value.Kind != TermKind.Concat || value.Operands[^1].ConstantValue is not { IsZero: true }) return value;
        var low = terms.Concat(value.Operands.SkipLast(1).ToArray());
        return Resize(low, value.Width) == value ? low : value;
    }
    public Term Resize(Term value, int width, bool signed = false) => value.Width == width ? value
        : value.Width > width ? terms.Slice(value, 0, width)
        : terms.Apply(new CoreOperator(signed ? CoreOperation.SignExtend : CoreOperation.ZeroExtend), width, value);
}
