using System.Collections.Immutable;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    private sealed record MathDefinition(string Rewrite, BoundValue[] Inputs, MethodRef[] Methods, LocalValue[] Results);
    private readonly Dictionary<CallIdentity, MathDefinition> mathCalls = [];

    private void PrepareMathCall(Call call, ClassifiedCall classified)
    {
        if (classified.Binding is not { } binding || classified.Function?.MathRewrite is not { } rewrite)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "数学导入缺少原型绑定", code: "lowering.Math.Binding"); return; }
        string[] methods = rewrite switch
        {
            "TruncateOutput" => ["Truncate"], "SinCos" => ["Sin", "Cos"], "Power" or "Exp2" => ["Pow"], _ => [],
        };
        var targets = methods.Select(name => RuntimeManagedMethods.Find(types.Model, new("System.Math", name,
            Enumerable.Repeat(new RuntimeManagedType("System.Double"), name == "Pow" ? 2 : 1).ToImmutableArray(),
            new("System.Double"), [], "Math"), [])).ToArray();
        if (targets.Any(m => m is null || !m.Method.IsStatic || !m.Method.ReturnType.Equals(types.Double)))
        { Fail<object>(LoweringFailureKind.RuntimeCall, "核心库中没有匹配的数学方法", code: "lowering.Math.Method"); return; }
        if (targets.Any(target => target is not null && target.Equals(method)))
        { Fail<object>(LoweringFailureKind.RuntimeCall, "数学导入的托管写法会引入自身递归", code: "lowering.Math.Recursive"); return; }
        int width = binding.Arguments[0].Type.Size * 8;
        var locals = Enumerable.Range(0, Math.Max(1, targets.Length)).Select(_ => new LocalValue(new(nextLocal++),
            rewrite == "Remainder" ? FloatType(width) : types.Double, rewrite == "Remainder" ? width : 64)).ToArray();
        var inputs = binding.Arguments.Where((_, i) => !classified.Function.Operation.PointerEffects.Any(e => e.Input == classified.Function.Arguments[i])).ToArray();
        mathCalls.Add(call.Identity, new(rewrite, inputs, targets.Select(m => m!).ToArray(), locals));
        if (rewrite is "TruncateOutput" or "SinCos")
        {
            var outputs = context.Get(new MathOutputQuery(state, calls!, frameAddressUses, binder, signature, dispatch), call.Identity);
            if (!outputs.IsSuccess)
            { Fail<object>(LoweringFailureKind.RuntimeCall, outputs.Why!.Message, outputs.Why.Cause, outputs.Why.Code); return; }
            foreach (var output in outputs.Value)
            {
                int resultIndex = rewrite == "SinCos" ? output.Name == "sin" ? 0 : 1 : 0;
                ManagedValue value = rewrite == "SinCos" ? new ConversionValue(ConversionKind.FloatToFloat, locals[resultIndex], types.Single, 32) : locals[resultIndex];
                foreach (var read in output.Reads)
                {
                    var contents = context.Get(state.Read, read.Identity);
                    if (!contents.IsSuccess) { Fail<object>(LoweringFailureKind.State, "数学输出读取没有状态身份", contents.Why); return; }
                    var definition = new ReadDefinition(read) { Constant = value };
                    if (readValues.TryGetValue(contents.Value, out var existing)) definition = existing;
                    else readValues.Add(contents.Value, definition);
                    readDefinitions.Add(read.Identity, definition);
                }
            }
        }
        else if (classified.Result?.Source is TermSource result)
            values.Add(result.Term, rewrite is "Power" or "Exp2" ? new ConversionValue(ConversionKind.FloatToFloat, locals[0], types.Single, 32) : locals[0]);
    }

    private IReadOnlyList<ManagedStatement>? LowerMathCall(Call call, Point point)
    {
        var definition = mathCalls[call.Identity];
        var arguments = definition.Inputs.Select(input => CallArgument(input, FloatType(input.Type.Size * 8), point)).ToArray();
        if (arguments.Any(v => v is null)) return null;
        if (definition.Rewrite == "Remainder")
            return [new ManagedAssignment(position, definition.Results[0], new BinaryValue(BinaryOperator.SignedRemainder,
                arguments[0]!, arguments[1]!, definition.Results[0].Type, definition.Results[0].Width))];
        if (definition.Rewrite == "Power" && arguments.Any(v => v is not ConstantValue))
            return Fail<IReadOnlyList<ManagedStatement>>(LoweringFailureKind.RuntimeCall,
                "powf 的输入域未证明避开 Math::Pow 的特殊值差异", code: "lowering.Math.PowDomain");
        if (definition.Rewrite == "Power" && arguments.Select(v => BitConverter.UInt32BitsToSingle((uint)((ConstantValue)v!).Bits)).ToArray() is var domain
            && (!float.IsFinite(domain[0]) || domain[0] <= 0 || !float.IsFinite(domain[1])))
            return Fail<IReadOnlyList<ManagedStatement>>(LoweringFailureKind.RuntimeCall,
                "powf 的常量输入不在已证明的正底数、有限指数域内", code: "lowering.Math.PowDomain");
        var expanded = arguments.Select(v => v!.Width == 32
            ? (ManagedValue)new ConversionValue(ConversionKind.FloatToFloat, v!, types.Double, 64) : v!).ToArray();
        if (definition.Rewrite == "Exp2") expanded = [new ConstantValue(BitConverter.DoubleToUInt64Bits(2), types.Double, 64), expanded[0]];
        return definition.Methods.Select((target, i) => (ManagedStatement)new ManagedCall(position,
            new(target, null, expanded, false), definition.Results[i])).ToArray();
    }
}
