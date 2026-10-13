using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Ir;
using Cpp2CS.Native;

namespace Cpp2CS.Validation;

public static class NativePureRuleChecks
{
    private static readonly IReadOnlyDictionary<ValueId, BigInteger> EmptyEnvironment = new Dictionary<ValueId, BigInteger>();

    public static int Run()
    {
        var checks = 0;
        void Check(bool condition, string reason) { CoreChecks.Require(condition, reason); checks++; }
        foreach (var architecture in Enum.GetValues<Architecture>())
        {
            var shape = new Operation(OpCode.Add, new Value(900, 8), [new(-10, 8), new(700, 8)],
                NoPayload.Instance, new(new(-5), new(100)));
            Check(MirValidator.ValidateOperation(architecture, shape).Count == 0,
                "standalone operation validation leaves value IDs and state flow to the enclosing IR");
            Check(MirValidator.ValidateOperation(architecture, shape with { Result = new Value(900, 0) }).Count != 0,
                "standalone operation validation rejects zero-width results");
            Check(MirValidator.ValidateOperation(architecture, shape with { Inputs = [new(0, 4097), new(1, 8)] }).Count != 0,
                "standalone operation validation rejects oversized inputs");
            Check(MirValidator.ValidateOperation(architecture, shape with { Payload = new ImmediatePayload(0) }).Count != 0,
                "standalone operation validation enforces the shared payload contract");
            var floating = new Operation(OpCode.Float, new Value(0, 44), [new(1, 32), new(2, 32), new(3, 32)],
                new FloatPayload(new(FloatKind.Add, 32, 32)));
            Check(MirValidator.ValidateOperation(architecture, floating).Count == 0 &&
                MirValidator.ValidateOperation(architecture, floating with { Result = new Value(0, 32) }).Count != 0,
                "standalone float validation preserves flags and trap-bit result width");
            var fixture = new Fixture(architecture);
            var x = fixture.Input(8);
            var y = fixture.Input(8);
            var condition = fixture.Input(1);
            var zero = fixture.Constant(8, 0);
            var one = fixture.Constant(8, 1);
            var ones = fixture.Constant(8, 255);
            var falseValue = fixture.Constant(1, 0);
            var trueValue = fixture.Constant(1, 1);
            var singleVariable = new List<NativeNode>();
            NativeValue N(OpCode code, int width, params NativeValue[] inputs) => fixture.Node(code, width, inputs).Result!.Value;
            void Add(OpCode code, int width, params NativeValue[] inputs) => singleVariable.Add(fixture.Node(code, width, inputs));
            foreach (var code in new[] { OpCode.Add, OpCode.Mul, OpCode.And, OpCode.Or, OpCode.Xor })
            {
                var constant = code switch { OpCode.Mul => one, OpCode.And => ones, _ => zero };
                Add(code, 8, x, constant);
                Add(code, 8, constant, x);
            }
            foreach (var code in new[] { OpCode.Mul, OpCode.And })
            {
                Add(code, 8, x, zero);
                Add(code, 8, zero, x);
            }
            Add(OpCode.Or, 8, x, ones);
            Add(OpCode.Or, 8, ones, x);
            Add(OpCode.Sub, 8, x, zero);
            foreach (var code in new[] { OpCode.Sub, OpCode.And, OpCode.Or, OpCode.Xor }) Add(code, 8, x, x);
            foreach (var code in new[] { OpCode.Eq, OpCode.Ult, OpCode.Slt }) Add(code, 1, x, x);
            Add(OpCode.Ult, 1, x, zero);
            Add(OpCode.Not, 8, N(OpCode.Not, 8, x));
            foreach (var code in new[] { OpCode.Shl, OpCode.Shr, OpCode.Sar })
            {
                Add(code, 8, x, zero);
                Add(code, 8, zero, x);
                if (code != OpCode.Sar) Add(code, 8, x, fixture.Constant(8, 8));
            }
            Add(OpCode.Sar, 8, ones, x);
            foreach (var code in new[] { OpCode.UDiv, OpCode.SDiv })
            {
                Add(code, 8, x, zero);
                Add(code, 8, zero, x);
                Add(code, 8, x, one);
            }
            Add(OpCode.Select, 8, falseValue, zero, x);
            Add(OpCode.Select, 8, trueValue, x, zero);
            Add(OpCode.Select, 8, condition, x, x);
            Add(OpCode.Eq, 1, condition, trueValue);
            Add(OpCode.Eq, 1, falseValue, condition);
            Add(OpCode.Select, 1, condition, trueValue, falseValue);
            Add(OpCode.Select, 1, condition, falseValue, trueValue);
            singleVariable.Add(fixture.Extract(x, 0, 8));
            singleVariable.Add(fixture.Extract(fixture.Extract(x, 1, 6).Result!.Value, 2, 3));
            var concat = N(OpCode.Concat, 16, x, x);
            singleVariable.Add(fixture.Extract(concat, 0, 8));
            singleVariable.Add(fixture.Extract(concat, 8, 8));
            singleVariable.Add(fixture.Extract(concat, 2, 3));
            singleVariable.Add(fixture.Extract(concat, 9, 5));
            foreach (var code in new[] { OpCode.Zext, OpCode.Sext })
            {
                var extended = N(code, 24, x);
                singleVariable.Add(fixture.Extract(extended, 0, 8));
                singleVariable.Add(fixture.Extract(extended, 2, 4));
                singleVariable.Add(fixture.Extract(extended, 0, 16));
                Add(code, 32, extended);
            }
            singleVariable.Add(fixture.Extract(N(OpCode.Zext, 24, x), 8, 8));
            Add(OpCode.Sext, 32, N(OpCode.Zext, 16, x));
            Add(OpCode.Concat, 16, zero, x);
            Add(OpCode.Concat, 8, fixture.Extract(x, 4, 4).Result!.Value, fixture.Extract(x, 0, 4).Result!.Value);
            Add(OpCode.Concat, 6, fixture.Extract(x, 4, 3).Result!.Value, fixture.Extract(x, 1, 3).Result!.Value);

            foreach (var node in singleVariable)
            {
                var reduction = RequireReduction(node, fixture, Check);
                for (var value = 0; value < 256; value++)
                {
                    var environment = new Dictionary<ValueId, BigInteger> { [x.Id] = value, [condition.Id] = value & 1 };
                    Check(fixture.Evaluate(node, environment) == fixture.Evaluate(reduction, environment),
                        $"{architecture}: exhaustive byte equivalence: {reduction.Rule}, value {value}");
                }
            }

            NativeNode[] twoVariables =
            [
                fixture.Node(OpCode.Add, 8, [N(OpCode.Sub, 8, x, y), y]),
                fixture.Node(OpCode.Add, 8, [y, N(OpCode.Sub, 8, x, y)]),
                fixture.Node(OpCode.Sub, 8, [N(OpCode.Add, 8, x, y), y]),
                fixture.Node(OpCode.Sub, 8, [N(OpCode.Add, 8, y, x), y]),
                fixture.Node(OpCode.Sub, 8, [x, N(OpCode.Sub, 8, x, y)]),
                fixture.Node(OpCode.Xor, 8, [N(OpCode.Xor, 8, x, y), y]),
                fixture.Node(OpCode.Xor, 8, [N(OpCode.Xor, 8, y, x), y]),
                fixture.Node(OpCode.Eq, 1, [N(OpCode.Sub, 8, x, y), zero]),
                fixture.Node(OpCode.Eq, 1, [zero, N(OpCode.Sub, 8, x, y)]),
                fixture.Node(OpCode.Eq, 1, [N(OpCode.Xor, 8, x, y), zero]),
                fixture.Node(OpCode.Eq, 1, [zero, N(OpCode.Xor, 8, x, y)])
            ];
            foreach (var node in twoVariables)
            {
                var reduction = RequireReduction(node, fixture, Check);
                for (var left = 0; left < 256; left++)
                for (var right = 0; right < 256; right++)
                {
                    var environment = new Dictionary<ValueId, BigInteger> { [x.Id] = left, [y.Id] = right };
                    Check(fixture.Evaluate(node, environment) == fixture.Evaluate(reduction, environment),
                        $"{architecture}: exhaustive byte pair equivalence: {reduction.Rule}, values {left}, {right}");
                }
            }

            foreach (var width in new[] { 1, 8, 32, 64, 128, 4096 })
            {
                var wide = new Fixture(architecture);
                var parameter = wide.Input(width);
                var mask = (BigInteger.One << width) - 1;
                var sign = BigInteger.One << (width - 1);
                var values = new[] { BigInteger.Zero, BigInteger.One, sign - 1, sign, mask };
                foreach (var value in values)
                {
                    foreach (var code in new[] { OpCode.Add, OpCode.Sub, OpCode.Mul, OpCode.And, OpCode.Or, OpCode.Xor,
                                 OpCode.UDiv, OpCode.SDiv, OpCode.Eq, OpCode.Ult, OpCode.Slt, OpCode.Shl, OpCode.Shr, OpCode.Sar })
                    foreach (var other in values)
                    {
                        var resultWidth = code is OpCode.Eq or OpCode.Ult or OpCode.Slt ? 1 : width;
                        var constantNode = wide.Node(code, resultWidth, [wide.Constant(width, value), wide.Constant(width, other)]);
                        var reduced = RequireReduction(constantNode, wide, Check);
                        Check(reduced.Replacement is { Code: OpCode.Constant }, "all integer constant inputs become a constant");
                        Check(wide.Evaluate(constantNode, EmptyEnvironment) == wide.Evaluate(reduced, EmptyEnvironment), "wide constant folding agrees with shared operation semantics");
                    }
                }
                var env = new Dictionary<ValueId, BigInteger> { [parameter.Id] = sign };
                var byZero = wide.Node(OpCode.SDiv, width, [parameter, wide.Constant(width, 0)]);
                Check(wide.Evaluate(RequireReduction(byZero, wide, Check), env) == 0, "signed division by zero is the MIR total-function result");
                var minByMinusOne = wide.Node(OpCode.SDiv, width, [wide.Constant(width, sign), wide.Constant(width, mask)]);
                Check(wide.Evaluate(RequireReduction(minByMinusOne, wide, Check), EmptyEnvironment) == sign, "signed minimum divided by minus one wraps to minimum");
                var byOne = wide.Node(OpCode.SDiv, width, [parameter, wide.Constant(width, 1)]);
                Check(wide.Evaluate(RequireReduction(byOne, wide, Check), env) == sign, "division identity also holds for one-bit signed arithmetic");
                var hugeCount = wide.Constant(64, ulong.MaxValue);
                foreach (var code in new[] { OpCode.Shl, OpCode.Shr })
                {
                    var shift = wide.Node(code, width, [parameter, hugeCount]);
                    Check(wide.Evaluate(RequireReduction(shift, wide, Check), env) == 0, "huge shift counts produce zero without narrowing the count");
                }
            }

            void Keep(NativeNode node, string reason) => Check(NativePureRules.TryReduce(node, fixture.Definitions) is null, reason);
            Keep(fixture.Node(OpCode.SDiv, 8, [x, x]), "x divided by itself is not one at zero");
            Keep(fixture.Node(OpCode.UDiv, 8, [x, x]), "unsigned x divided by itself is not one at zero");
            Keep(fixture.Node(OpCode.Eq, 1, [N(OpCode.Sub, 8, x, y), one]), "a nonzero subtraction comparison cannot become operand equality");
            Keep(fixture.Node(OpCode.Eq, 1, [one, N(OpCode.Xor, 8, x, y)]), "a nonzero xor comparison cannot become operand equality");
            Keep(fixture.Node(OpCode.Sar, 8, [x, fixture.Constant(8, 8)]), "arithmetic overshift depends on the sign bit");
            Keep(fixture.Node(OpCode.Zext, 32, [N(OpCode.Sext, 16, x)]), "zero extension after sign extension cannot become a single extension");
            Keep(fixture.Extract(concat, 4, 8), "extract across the concat boundary is retained");
            Keep(fixture.Node(OpCode.Concat, 8, [fixture.Extract(x, 0, 4).Result!.Value,
                fixture.Extract(x, 4, 4).Result!.Value]), "reversed concat slices are not mistaken for an identity");
            Keep(fixture.Node(OpCode.Add, 8, [x, y]), "unrelated operands are not arbitrarily reduced");
            var addZero = fixture.Node(OpCode.Add, 8, [x, zero]);
            Keep(addZero with { Result = addZero.Result!.Value with { Type = new BitsType(16) } }, "mismatched result widths are rejected");
            Keep(addZero with { Inputs = [x] }, "wrong arity is rejected");
            Keep(addZero with { Inputs = [x, new(new(-1), WorldType.Instance)] }, "World is never an integer operand");
            Keep(addZero with { Payload = new ImmediatePayload(0) }, "wrong payload is rejected");
            Keep(addZero with { Flow = new(new(new(-2), WorldType.Instance), new(new(-3), WorldType.Instance)) }, "state-bearing nodes cannot be reduced as pure");
            Keep(fixture.Node(OpCode.Undefined, 8, [], new ChoicePayload("test choice")), "choice without a state flow is still not pure");
            Keep(fixture.Node(OpCode.LoadIf, 8, [falseValue, fixture.Constant(64, 0)]), "inactive conditional memory keeps its World node");
            Keep(fixture.Node(OpCode.Float, 44, [fixture.Constant(32, 0), fixture.Constant(32, 0), fixture.Constant(32, 0)],
                new FloatPayload(new(FloatKind.Add, 32, 32))), "floating constants preserve architecture control, flags and trap bits");
            Keep(fixture.Node(OpCode.Qarma5, 64, [fixture.Constant(64, 0), fixture.Constant(64, 0), fixture.Constant(128, 0)]),
                "QARMA stays outside the integer normalization rule set");
            var mismatchedDefinition = new Dictionary<ValueId, NativeNode>(fixture.Definitions)
                { [zero.Id] = fixture.Definitions[zero.Id] with { Result = new NativeValue(zero.Id, new BitsType(16)) } };
            Check(NativePureRules.TryReduce(addZero, mismatchedDefinition) is null, "a constant definition with a mismatched type is not trusted");
            var negativeDefinition = new Dictionary<ValueId, NativeNode>(fixture.Definitions)
                { [zero.Id] = fixture.Definitions[zero.Id] with { Payload = new ImmediatePayload(-1) } };
            Check(NativePureRules.TryReduce(addZero, negativeDefinition) is null, "noncanonical constant bits are not trusted");
        }
        return checks;
    }

    private static NativePureReduction RequireReduction(NativeNode node, Fixture fixture, Action<bool, string> check)
    {
        var reduction = NativePureRules.TryReduce(node, fixture.Definitions);
        check(reduction is not null, $"expected a pure reduction for {node.Code}");
        check((reduction!.Alias is null) != (reduction.Replacement is null), "reduction has exactly one replacement kind");
        if (reduction.Alias is { } alias) check(alias.Type == node.Result!.Value.Type, "aliases preserve exact bit width");
        if (reduction.Replacement is { } replacement)
            check(replacement.Result == node.Result && replacement.Source == node.Source && replacement.Flow is null,
                "replacement preserves value identity, original phase and purity");
        return reduction;
    }

    private sealed class Fixture(Architecture architecture)
    {
        private int next;
        private readonly InstructionOrigin origin = new("fixture:native-pure-rules", 0x1000, 0, new byte[] { 0, 0, 0, 0 });
        private readonly MachineState state = new();
        public Dictionary<ValueId, NativeNode> Definitions { get; } = [];
        public NativeValue Input(int width) => new(new(next++), new BitsType(width));
        public NativeValue Constant(int width, BigInteger value) => Node(OpCode.Constant, width, [], new ImmediatePayload(value)).Result!.Value;
        public NativeNode Extract(NativeValue value, int offset, int width) => Node(OpCode.Extract, width, [value], new ImmediatePayload(offset));
        public NativeNode Node(OpCode code, int width, NativeValue[] inputs, OperationPayload? payload = null)
        {
            var value = Input(width);
            var node = new NativeNode(code, value, inputs.ToImmutableArray(), payload ?? NoPayload.Instance, null, new(origin, next));
            Definitions.Add(value.Id, node);
            return node;
        }
        public BigInteger Evaluate(NativePureReduction reduction, IReadOnlyDictionary<ValueId, BigInteger> environment) =>
            reduction.Alias is { } alias ? Evaluate(alias, environment) : Evaluate(reduction.Replacement!, environment);
        public BigInteger Evaluate(NativeNode node, IReadOnlyDictionary<ValueId, BigInteger> environment)
        {
            var values = node.Inputs.Select(value => Evaluate(value, environment)).ToArray();
            var operation = new Operation(node.Code, new Value(node.Result!.Value.Id.Id, ((BitsType)node.Result.Value.Type).Width),
                node.Inputs.Select(value => new Value(value.Id.Id, ((BitsType)value.Type).Width)).ToImmutableArray(), node.Payload);
            return MirOperationEvaluator.Evaluate(architecture, operation, values, state, node.Source.Origin, node.Source.OperationIndex).Bits;
        }
        private BigInteger Evaluate(NativeValue value, IReadOnlyDictionary<ValueId, BigInteger> environment) =>
            environment.TryGetValue(value.Id, out var bits) ? bits : Evaluate(Definitions[value.Id], environment);
    }
}
