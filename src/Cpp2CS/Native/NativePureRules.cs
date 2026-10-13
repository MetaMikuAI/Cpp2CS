using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Ir;

namespace Cpp2CS.Native;

public sealed record NativePureReduction(string Rule, NativeValue? Alias, NativeNode? Replacement);

// 规则仅处理全定义的整数位向量；浮点、choice 与状态操作保留原节点。
public static class NativePureRules
{
    public const string Version = "native-integer-rules/1";
    private static readonly MachineState FoldState = new();

    public static NativePureReduction? TryReduce(NativeNode node, IReadOnlyDictionary<ValueId, NativeNode> definitions)
    {
        if (!IntegerShape(node) || node.Code == OpCode.Constant) return null;
        var result = node.Result!.Value;
        var width = Width(result);
        var inputs = node.Inputs;
        var a = inputs[0];
        var b = inputs.Length > 1 ? inputs[1] : default;
        var hasA = Constant(a, definitions, out var av);
        var bv = BigInteger.Zero;
        var hasB = inputs.Length > 1 && Constant(b, definitions, out bv);
        NativePureReduction Alias(string rule, NativeValue value)
        {
            if (value.Type != result.Type) throw new InvalidOperationException("Pure reduction changed its result type");
            return new(rule, value, null);
        }
        NativePureReduction Replace(string rule, OpCode code, ImmutableArray<NativeValue> values, OperationPayload? payload = null) =>
            new(rule, null, node with { Code = code, Inputs = values, Payload = payload ?? NoPayload.Instance });
        NativePureReduction Bits(string rule, BigInteger value) =>
            Replace(rule, OpCode.Constant, [], new ImmediatePayload(value & MirOperationEvaluator.Mask(width)));
        NativePureReduction Slice(string rule, NativeValue value, int offset) => offset == 0 && value.Type == result.Type
            ? Alias(rule, value) : Replace(rule, OpCode.Extract, [value], new ImmediatePayload(offset));

        var third = BigInteger.Zero;
        if (hasA && (inputs.Length == 1 || hasB) &&
            (inputs.Length < 3 || Constant(inputs[2], definitions, out third)))
        {
            BigInteger[] constantInputs = inputs.Length switch { 1 => [av], 2 => [av, bv], _ => [av, bv, third] };
            var operation = new Operation(node.Code, new Value(result.Id.Id, width),
                inputs.Select(value => new Value(value.Id.Id, Width(value))).ToImmutableArray(), node.Payload);
            var evaluated = MirOperationEvaluator.Evaluate(Architecture.Arm64, operation, constantInputs,
                FoldState, node.Source.Origin, node.Source.OperationIndex);
            if (evaluated.Stop is not null || evaluated.Choices != 0)
                throw new InvalidOperationException("Integer constant evaluation produced a state effect");
            return Bits("integer.constant", evaluated.Bits);
        }

        var mask = MirOperationEvaluator.Mask(width);
        switch (node.Code)
        {
            case OpCode.Add:
                if (hasA && av.IsZero) return Alias("add.zero-left", b);
                if (hasB && bv.IsZero) return Alias("add.zero-right", a);
                if (Definition(a, definitions) is { Code: OpCode.Sub } subtractA && subtractA.Inputs[1] == b)
                    return Alias("add.cancel-subtract-left", subtractA.Inputs[0]);
                if (Definition(b, definitions) is { Code: OpCode.Sub } subtractB && subtractB.Inputs[1] == a)
                    return Alias("add.cancel-subtract-right", subtractB.Inputs[0]);
                break;
            case OpCode.Sub:
                if (hasB && bv.IsZero) return Alias("subtract.zero", a);
                if (a == b) return Bits("subtract.self", 0);
                if (Definition(a, definitions) is { Code: OpCode.Add } add)
                {
                    if (add.Inputs[0] == b) return Alias("subtract.cancel-add-left", add.Inputs[1]);
                    if (add.Inputs[1] == b) return Alias("subtract.cancel-add-right", add.Inputs[0]);
                }
                if (Definition(b, definitions) is { Code: OpCode.Sub } subtract && subtract.Inputs[0] == a)
                    return Alias("subtract.cancel-subtract", subtract.Inputs[1]);
                break;
            case OpCode.Mul:
                if (hasA && av.IsZero || hasB && bv.IsZero) return Bits("multiply.zero", 0);
                if (hasA && av.IsOne) return Alias("multiply.one-left", b);
                if (hasB && bv.IsOne) return Alias("multiply.one-right", a);
                break;
            case OpCode.And:
                if (hasA && av.IsZero || hasB && bv.IsZero) return Bits("and.zero", 0);
                if (a == b) return Alias("and.self", a);
                if (hasA && av == mask) return Alias("and.mask-left", b);
                if (hasB && bv == mask) return Alias("and.mask-right", a);
                break;
            case OpCode.Or:
                if (hasA && av == mask || hasB && bv == mask) return Bits("or.mask", mask);
                if (a == b) return Alias("or.self", a);
                if (hasA && av.IsZero) return Alias("or.zero-left", b);
                if (hasB && bv.IsZero) return Alias("or.zero-right", a);
                break;
            case OpCode.Xor:
                if (a == b) return Bits("xor.self", 0);
                if (hasA && av.IsZero) return Alias("xor.zero-left", b);
                if (hasB && bv.IsZero) return Alias("xor.zero-right", a);
                if (Definition(a, definitions) is { Code: OpCode.Xor } xorA)
                {
                    if (xorA.Inputs[0] == b) return Alias("xor.cancel-left", xorA.Inputs[1]);
                    if (xorA.Inputs[1] == b) return Alias("xor.cancel-right", xorA.Inputs[0]);
                }
                break;
            case OpCode.Not:
                if (Definition(a, definitions) is { Code: OpCode.Not } not) return Alias("not.double", not.Inputs[0]);
                break;
            case OpCode.Shl:
            case OpCode.Shr:
            case OpCode.Sar:
                if (hasB && bv.IsZero) return Alias("shift.zero-count", a);
                if (hasA && av.IsZero) return Bits("shift.zero-value", 0);
                if (hasB && bv >= width && node.Code != OpCode.Sar) return Bits("shift.overshift", 0);
                if (hasA && av == mask && node.Code == OpCode.Sar) return Bits("arithmetic-shift.minus-one", mask);
                break;
            case OpCode.UDiv:
            case OpCode.SDiv:
                if (hasB && bv.IsZero || hasA && av.IsZero) return Bits("divide.zero", 0);
                if (hasB && bv.IsOne) return Alias("divide.one", a);
                break;
            case OpCode.Eq:
            case OpCode.Ult:
            case OpCode.Slt:
                if (a == b) return Bits("compare.self", node.Code == OpCode.Eq ? 1 : 0);
                if (node.Code == OpCode.Ult && hasB && bv.IsZero) return Bits("unsigned-less.zero", 0);
                if (node.Code == OpCode.Eq)
                {
                    if (hasA && av.IsZero && Definition(b, definitions) is { Code: OpCode.Sub or OpCode.Xor } differenceRight)
                        return Replace("equal.zero-difference-left", OpCode.Eq, differenceRight.Inputs);
                    if (hasB && bv.IsZero && Definition(a, definitions) is { Code: OpCode.Sub or OpCode.Xor } differenceLeft)
                        return Replace("equal.zero-difference-right", OpCode.Eq, differenceLeft.Inputs);
                }
                if (node.Code == OpCode.Eq && Width(a) == 1)
                {
                    if (hasA) return av.IsZero ? Replace("boolean-equal.zero-left", OpCode.Not, [b]) : Alias("boolean-equal.one-left", b);
                    if (hasB) return bv.IsZero ? Replace("boolean-equal.zero-right", OpCode.Not, [a]) : Alias("boolean-equal.one-right", a);
                }
                break;
            case OpCode.Select:
                if (hasA) return Alias("select.constant-condition", av.IsZero ? inputs[2] : b);
                if (b == inputs[2]) return Alias("select.same-arms", b);
                if (width == 1 && hasB && Constant(inputs[2], definitions, out var cv))
                {
                    if (bv.IsOne && cv.IsZero) return Alias("select.boolean", a);
                    if (bv.IsZero && cv.IsOne) return Replace("select.boolean-not", OpCode.Not, [a]);
                }
                break;
            case OpCode.Extract:
            {
                var offset = (int)((ImmediatePayload)node.Payload).Value;
                if (offset == 0 && a.Type == result.Type) return Alias("extract.whole", a);
                var source = Definition(a, definitions);
                if (source is { Code: OpCode.Extract, Payload: ImmediatePayload innerOffset })
                    return Slice("extract.nested", source.Inputs[0], offset + (int)innerOffset.Value);
                if (source is { Code: OpCode.Concat })
                {
                    var lowWidth = Width(source.Inputs[1]);
                    if (offset + width <= lowWidth) return Slice("extract.concat-low", source.Inputs[1], offset);
                    if (offset >= lowWidth) return Slice("extract.concat-high", source.Inputs[0], offset - lowWidth);
                }
                if (source is { Code: OpCode.Zext or OpCode.Sext })
                {
                    var inner = source.Inputs[0];
                    if (offset + width <= Width(inner)) return Slice("extract.extension-low", inner, offset);
                    if (source.Code == OpCode.Zext && offset >= Width(inner)) return Bits("extract.zero-extension-high", 0);
                    if (offset == 0) return Replace("extract.extension-prefix", source.Code, [inner]);
                }
                break;
            }
            case OpCode.Zext:
            case OpCode.Sext:
                if (Definition(a, definitions) is { Code: OpCode.Zext or OpCode.Sext } extension &&
                    (extension.Code == node.Code || extension.Code == OpCode.Zext))
                    return Replace("extension.nested", extension.Code, [extension.Inputs[0]]);
                break;
            case OpCode.Concat:
                if (hasA && av.IsZero) return Replace("concat.zero-high", OpCode.Zext, [b]);
                if (Definition(a, definitions) is { Code: OpCode.Extract, Payload: ImmediatePayload highOffset } high &&
                    Definition(b, definitions) is { Code: OpCode.Extract, Payload: ImmediatePayload lowOffset } low &&
                    high.Inputs[0] == low.Inputs[0] && highOffset.Value == lowOffset.Value + Width(b))
                    return Slice("concat.adjacent-extracts", high.Inputs[0], (int)lowOffset.Value);
                break;
        }
        return null;
    }

    private static int Width(NativeValue value) => ((BitsType)value.Type).Width;

    private static NativeNode? Definition(NativeValue value, IReadOnlyDictionary<ValueId, NativeNode> definitions) =>
        definitions.TryGetValue(value.Id, out var definition) && definition.Result == value && IntegerShape(definition)
            ? definition : null;

    private static bool Constant(NativeValue value, IReadOnlyDictionary<ValueId, NativeNode> definitions, out BigInteger bits)
    {
        if (Definition(value, definitions) is { Code: OpCode.Constant, Payload: ImmediatePayload constant })
        { bits = constant.Value; return true; }
        bits = BigInteger.Zero;
        return false;
    }

    private static bool IntegerShape(NativeNode node)
    {
        if (node.Result is not { Type: BitsType { Width: >= 1 and <= 4096 } } result || node.Flow is not null ||
            !OperationSpecs.TryGet(node.Code, out var spec) || spec.Effects != OperationEffects.None ||
            node.Inputs.IsDefault || node.Inputs.Length != spec.Arity || node.Payload?.GetType() != spec.PayloadType ||
            node.Inputs.Any(value => value.Type is not BitsType { Width: >= 1 and <= 4096 })) return false;
        var width = Width(result);
        var a = node.Inputs.Length > 0 ? Width(node.Inputs[0]) : 0;
        var b = node.Inputs.Length > 1 ? Width(node.Inputs[1]) : 0;
        return node.Code switch
        {
            OpCode.Constant => ((ImmediatePayload)node.Payload).Value >= 0 && ((ImmediatePayload)node.Payload).Value <= MirOperationEvaluator.Mask(width),
            OpCode.Extract => ((ImmediatePayload)node.Payload).Value >= 0 && ((ImmediatePayload)node.Payload).Value + width <= a,
            OpCode.Concat => width == a + b,
            OpCode.Zext or OpCode.Sext => width > a,
            OpCode.Not => width == a,
            OpCode.Eq or OpCode.Ult or OpCode.Slt => a == b && width == 1,
            OpCode.Select => a == 1 && b == Width(node.Inputs[2]) && width == b,
            OpCode.Shl or OpCode.Shr or OpCode.Sar => width == a,
            OpCode.Add or OpCode.Sub or OpCode.Mul or OpCode.And or OpCode.Or or OpCode.Xor or OpCode.UDiv or OpCode.SDiv => width == a && a == b,
            _ => false
        };
    }
}
