using System.Collections.Immutable;
using Cpp2CS.Kernel.Facts;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;
using Cpp2CS.Spec.Runtime;

namespace Cpp2CS.Discovery;

internal sealed partial class TemplateSearch
{
    private Binding? BindCheck(TemplateStep step, ConditionalThrow check, Binding bound) =>
        check.Exception != step.Exception ? null :
        Match(step.Values[0], check.Polarity ? check.Condition : Terms.Not(check.Condition), bound);

    private Binding? MatchRow(ImmutableArray<TemplateValue> patterns, ImmutableArray<Term> values, Binding bound)
    {
        if (patterns.Length != values.Length) return null;
        for (int i = 0; i < patterns.Length; i++)
        {
            if (Match(patterns[i], values[i], bound) is not { } next) return null;
            bound = next;
        }
        return bound;
    }

    /// <summary>从原生项反向绑定模板表达式。一个谓词拆成短路分支时，单个分支只给出它实际测试的部分。</summary>
    private Binding? Match(TemplateValue pattern, Term value, Binding bound)
    {
        var args = pattern.Arguments;
        switch (pattern.Op)
        {
            case ValueOp.Operand: return bound.Operand(pattern.A, value);
            case ValueOp.Step: return bound.Result(pattern.A, value);
            case ValueOp.Literal: return value.Kind == TermKind.Entity && value.Entity.Kind == EntityKind.String ? bound.WithEntity(value.Entity) : null;
            case ValueOp.Null: return value.IsZero && value.Width == facts.Layout.PointerBits ? bound : null;
            case ValueOp.ToStorage:
                if (bound.Subject is { Kind: StackKind.Int32 } && value.Width < 32)
                    value = value is { Kind: TermKind.Slice, Offset: 0 } && value.Operands[0].Width >= 32
                        ? Terms.Slice(value.Operands[0], 0, 32) : Terms.ZeroExtend(value, 32);
                return Match(args[0], value, bound);
            case ValueOp.FromStorage:
                if (args[0].Op == ValueOp.FieldOfValue) return MatchFieldValue(args[0], value, bound);
                return Match(args[0], value, bound);
            case ValueOp.FieldOfValue:
                return MatchFieldValue(pattern, value, bound);
            case ValueOp.Named:
                return MatchNamed(pattern, value, bound);
            case ValueOp.IsMinimum:
            case ValueOp.IsAllOnes:
                if (value is not { Op: Op.Eq, Operands: [var number, { IsConstant: true } bits] }) return null;
                var limit = pattern.Op == ValueOp.IsMinimum ? UInt128.One << (number.Width - 1) : UInt128.MaxValue;
                return Terms.Bits(limit, number.Width) == bits ? Match(args[0], number, bound) : null;
            case ValueOp.Undefined:
                return value.Kind is TermKind.Undefined or TermKind.Arbitrary ? bound : null;
            case ValueOp.IsZero:
                if (value is { Op: Op.Eq, Operands: [var tested, { IsZero: true }] }) return Match(args[0], tested, bound);
                // IsInstSealed 的失败臂比较对象头中的类与指令的类型实体。
                if (args[0] is { Op: ValueOp.Named, Function: RuntimeFunction.IsInstance, Arguments.Length: 1 } instance &&
                    value is { Op: Op.Not, Operands: [{ Op: Op.Eq } comparison] })
                {
                    return ClassTest(comparison, instance.Arguments[0], bound, null);
                }
                return null;
            case ValueOp.Both:
                if (value.Op == Op.And && MatchBinary(args, value, bound, true) is { } both) return both;
                return Match(args[1], value, bound) ?? Match(args[0], value, bound);
            case ValueOp.Not:
                return value.Width == 1 ? Match(args[0], Terms.Not(value), bound) : null;
            case ValueOp.SignedDivide:
                // 后端可以用选择项规定除数为零时的机器结果，模板的检查单独绑定。
                if (value.Kind == TermKind.Select)
                    return Match(pattern, value.Operands[1], bound) ?? Match(pattern, value.Operands[2], bound);
                break;
            case ValueOp.SignedRemainder:
                // a % b 的指令选择也可写成 a - b * (a / b)。
                if (value is { Op: Op.Sub, Operands: [var dividend, { Op: Op.Mul } product] })
                    foreach (var factor in product.Operands)
                        if (Match(args[0], dividend, bound) is { } left && Match(args[1], factor, left) is { } pair &&
                            Match(new(ValueOp.SignedDivide, args), product.Operands[product.Operands[0] == factor ? 1 : 0], pair) is { } matched)
                            return matched;
                break;
            case ValueOp.Select:
                if (value.Kind == TermKind.Select && MatchRow(args, value.Operands, bound) is { } selection) return selection;
                // 有定义条件成立时选择项只剩有定义的一臂。
                return args[2].Op == ValueOp.Undefined ? Match(args[1], value, bound) : null;
            case ValueOp.Resize:
                if (value.Width != pattern.B) return null;
                var low = LowPart(value);
                if (low is { Kind: TermKind.Slice, Offset: 0 } && low.Width == Math.Min(pattern.A, pattern.B))
                    return Match(args[0], low.Operands[0], bound);
                return null;
            case ValueOp.Flag:
                return LowPart(value) is { Width: 1 } flag ? Match(args[0], flag, bound) : null;
            case ValueOp.FloatToDouble when value.Width == 64 && value.Op != Op.FConvert:
                // 已经是 double 的实参不需要转换。
                return types.TryGetValue(value, out var type) && type.Kind == StackKind.Float64 ? Match(args[0], value, bound) : null;
        }

        Op op = pattern.Op switch
        {
            ValueOp.Add => Op.Add, ValueOp.Sub => Op.Sub, ValueOp.Mul => Op.Mul, ValueOp.Negate => Op.Neg,
            ValueOp.And => Op.And, ValueOp.Xor => Op.Xor, ValueOp.Equal => Op.Eq,
            ValueOp.SignedLess => Op.Slt, ValueOp.UnsignedLess => Op.Ult,
            ValueOp.SignedDivide => Op.SDiv, ValueOp.SignedRemainder => Op.SRem,
            ValueOp.ShiftLeft => Op.Shl, ValueOp.ShiftRightSigned => Op.AShr, ValueOp.ShiftRightUnsigned => Op.LShr,
            ValueOp.FloatAdd => Op.FAdd, ValueOp.FloatSubtract => Op.FSub, ValueOp.FloatMultiply => Op.FMul, ValueOp.FloatDivide => Op.FDiv,
            ValueOp.FloatToDouble => Op.FConvert, ValueOp.SignedToDouble => Op.SToF, ValueOp.UnsignedToDouble => Op.UToF,
            _ => Op.None,
        };
        if (op == Op.None || op != value.Op) return null;
        return args.Length == 2 ? MatchBinary(args, value, bound, op is Op.Add or Op.Mul or Op.And or Op.Xor or Op.Eq)
            : MatchRow(args, value.Operands, bound);
    }

    private Binding? MatchBinary(ImmutableArray<TemplateValue> args, Term value, Binding bound, bool commutes) =>
        MatchRow(args, value.Operands, bound) ?? (commutes ? MatchRow(args, [value.Operands[1], value.Operands[0]], bound) : null);

    private static Term LowPart(Term value) => value switch
    {
        { Op: Op.SignExtend } => value.Operands[0],
        { Kind: TermKind.Concat, Operands: [var low, { IsZero: true }] } => low,
        _ => value,
    };

    private Binding? MatchFieldValue(TemplateValue pattern, Term value, Binding bound)
    {
        foreach (var (whole, type) in types)
        {
            if (type.Kind != StackKind.Value) continue;
            // 聚合体拆成 ABI 槽后，从整值按字段布局取切片，项池会还原到相应的槽。
            foreach (var member in type.Members)
            {
                if (member.OffsetBits % 8 != 0 || Field(type, member.OffsetBits / 8) is not { } field ||
                    field.OffsetBits < 0 || field.OffsetBits + field.Type.StorageBits > whole.Width) continue;
                var piece = Terms.Slice(whole, field.OffsetBits, field.Type.StorageBits);
                if (OnStack(piece, field.Type) != value) continue;
                if (bound.WithEntity(field.Entity) is { } named &&
                    Match(pattern.Arguments[0], whole, named with { Subject = field.Type }) is { } match) return match;
            }
        }
        return null;
    }

    // 密封类的 IsInstSealed 用对象头的类相等测试，在成功臂给出原对象。
    private Binding? ClassTest(Term condition, TemplateValue operand, Binding bound, Term? success)
    {
        if (condition is not { Op: Op.Eq, Operands: [var left, var right] }) return null;
        var (entity, klass) = left.Kind == TermKind.Entity ? (left, right) : (right, left);
        if (entity.Kind != TermKind.Entity || entity.Entity.Kind != EntityKind.Type || bound.WithEntity(entity.Entity) is not { } named ||
            Read(klass) is not { } read || read.Width != facts.Layout.PointerBits) return null;
        var (obj, offset) = BaseOffset(read.Address!);
        return offset == facts.Layout.ObjectClassOffset && (success is null || success == obj)
            ? Match(operand, obj, named.WithRead(read)) : null;
    }

    private static bool Align(Term pattern, Term value, Term formal, ref Term? input)
    {
        if (pattern == formal)
        {
            if (input is not null && input != value) return false;
            input = value;
            return true;
        }
        if (pattern.Kind != value.Kind || pattern.Op != value.Op || pattern.Operands.Length != value.Operands.Length) return false;
        for (int i = 0; i < pattern.Operands.Length; i++)
            if (!Align(pattern.Operands[i], value.Operands[i], formal, ref input)) return false;
        return true;
    }

    private Binding? MatchNamed(TemplateValue pattern, Term value, Binding bound)
    {
        var args = pattern.Arguments;
        if (value.Kind == TermKind.Attribute && value.Attribute.Value == (int)pattern.Function)
        {
            var values = value.Operands;
            if (values.Length == args.Length + 1 && values[^1].Kind == TermKind.Entity)
            {
                if (bound.WithEntity(values[^1].Entity) is not { } named) return null;
                bound = named;
                values = values[..^1];
            }
            return MatchRow(args, values, bound);
        }

        if (pattern.Function == RuntimeFunction.IsInstance && args.Length == 1 && value.Kind == TermKind.Select)
        {
            var condition = value.Operands[0];
            if (value.Operands[2].IsZero) return ClassTest(condition, args[0], bound, value.Operands[1]);
            if (value.Operands[1].IsZero) return ClassTest(Terms.Not(condition), args[0], bound, value.Operands[2]);
        }

        // 目标定义可以与具名项出现在同一个索引里。按定义的项树取可能的实参，常量、位宽与有定义条件由证明核对。
        foreach (var definition in RuntimeTargetDefinitions.Entries)
        {
            if (definition.Function != pattern.Function || args.Length != 1) continue;
            Term? input = null;
            if (!Align(definition.Value, value, definition.Argument, ref input) || input is null) continue;
            if (args[0].Op == ValueOp.FloatToDouble && input.Width == 32)
                input = Terms.Operation(Op.FConvert, 64, input);
            if (Match(args[0], input, bound) is { } match) return match;
        }

        if (pattern.Function == RuntimeFunction.FieldAddress)
        {
            var (root, offset) = BaseOffset(value);
            if (types.TryGetValue(root, out var type) && type.Kind == StackKind.ByRef &&
                Field(type, offset) is { } field && bound.WithEntity(field.Entity) is { } named)
                return Match(args[0], root, named);
            return null;
        }

        var raw = value is { Kind: TermKind.Slice, Offset: 0 } ? value.Operands[0] : value;
        if (Read(raw) is not { } read) return null;
        var (baseTerm, displacement) = BaseOffset(read.Address!);
        var layout = facts.Layout;
        bool fits = pattern.Function switch
        {
            RuntimeFunction.ArrayLength or RuntimeFunction.ArrayLengthNative =>
                displacement == layout.ArrayLengthOffset &&
                value.Width == (pattern.Function == RuntimeFunction.ArrayLength ? layout.ArrayLengthBits : layout.ArrayLengthStorageBits) &&
                types.TryGetValue(baseTerm, out var array) && array.Kind == StackKind.Object && facts.Metadata.ElementOf(array.Entity) is not null,
            RuntimeFunction.ClassOf => displacement == layout.ObjectClassOffset && read.Width == layout.PointerBits,
            RuntimeFunction.ElementClass => displacement == layout.ClassElementOffset && read.Width == layout.PointerBits,
            _ => false,
        };
        return fits ? Match(args[0], baseTerm, bound.WithRead(read)) : null;
    }
}
