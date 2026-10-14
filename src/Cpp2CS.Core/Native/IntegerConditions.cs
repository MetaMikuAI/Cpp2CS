namespace Cpp2CS.Native;

// 两条源码恢复路径共用整数 NZCV 条件；输入必须覆盖机器操作数的全部有效位。
public static class IntegerConditions
{
    public static Expression? Project(string operation, int condition, NativeValue left, NativeValue right)
    {
        var width = left.Bits.Width;
        if (operation is not ("compare" or "compare-add" or "compare-and") || condition is < 1 or > 14 ||
            width is not (32 or 64) || right.Bits.Width != width ||
            IntegerProjection.Bits(left) is not { } a || IntegerProjection.Bits(right) is not { } b) return null;
        var signed = "int" + width + "_t";
        var unsigned = "uint" + width + "_t";
        Expression Cast(Expression value, bool sign) => new OperationExpression(ValueOperation.IntegerCast, sign ? signed : unsigned, [value]);
        Expression Binary(string op, Expression x, Expression y) => new BinaryExpression(op, x, y);
        Expression Not(Expression value) => Binary("==", value, new NameExpression("false"));
        Expression Numeric(ValueOperation op, Expression x, Expression y) => new OperationExpression(op, signed, [x, y]);
        if (operation == "compare" && condition is 1 or 2 or 3 or 4 or 9 or 10 or 11 or 12 or 13 or 14)
        {
            var sign = condition is not (3 or 4 or 9 or 10);
            return Binary(condition switch { 1 => "==", 2 => "!=", 3 or 11 => ">=", 4 or 12 => "<", 9 or 13 => ">", _ => "<=" }, Cast(a, sign), Cast(b, sign));
        }
        var result = Numeric(operation == "compare-add" ? ValueOperation.Add : operation == "compare-and" ? ValueOperation.BitAnd : ValueOperation.Subtract, a, b);
        var zero = Binary("==", result, new ConstantExpression(0));
        var negative = Binary("<", result, new ConstantExpression(0));
        Expression carry = operation == "compare-and" ? new NameExpression("false") :
            Binary(operation == "compare-add" ? "<" : ">=", Cast(operation == "compare-add" ? result : a, false), Cast(operation == "compare-add" ? a : b, false));
        Expression overflow = operation == "compare-and" ? new NameExpression("false") : Binary("<",
            Numeric(ValueOperation.BitAnd, Numeric(ValueOperation.BitXor, a, operation == "compare-add" ? result : b), Numeric(ValueOperation.BitXor, operation == "compare-add" ? b : a, result)),
            new ConstantExpression(0));
        return condition switch
        {
            1 => zero, 2 => Not(zero), 3 => carry, 4 => Not(carry), 5 => negative, 6 => Not(negative), 7 => overflow, 8 => Not(overflow),
            9 => Binary("&&", carry, Not(zero)), 10 => Binary("||", Not(carry), zero),
            11 => Binary("==", negative, overflow), 12 => Binary("!=", negative, overflow),
            13 => Binary("&&", Not(zero), Binary("==", negative, overflow)),
            _ => Binary("||", zero, Binary("!=", negative, overflow))
        };
    }
}
