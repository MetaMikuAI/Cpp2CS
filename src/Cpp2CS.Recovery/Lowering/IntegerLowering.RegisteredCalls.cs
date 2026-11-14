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
    private void PrepareRegisteredCall(Call call, ClassifiedCall classified, RuntimeManagedMethod registration)
    {
        string prefix = "lowering." + registration.DiagnosticName;
        if (locations is null || classified.Binding is null)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "运行时托管写法缺少位置查询或调用绑定", code: prefix + ".Location"); return; }
        var arguments = RuntimeManagedMethods.TypeArguments(context, classified, locations, registration);
        if (!arguments.IsSuccess)
        { Fail<object>(LoweringFailureKind.RuntimeCall, arguments.Why!.Message, arguments.Why, prefix + ".Location"); return; }
        var target = RuntimeManagedMethods.Find(types.Model, registration, arguments.Value);
        if (target is null)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "核心库中没有唯一匹配登记身份与形参形状的方法", code: prefix + ".Method"); return; }
        if (classified.Binding.Arguments.Length != target.Method.Parameters.Count)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "运行时输入与托管形参数量不一致", code: prefix + ".Method"); return; }
        // C 层没有方法信息参数；现有绑定恰好包含托管方法的显式形参。
        var definition = new CallDefinition(target, classified.Binding) { Registration = registration, MathContraction = classified.Function?.MathContraction is not null };
        callDefinitions.Add(call.Identity, definition);
        if (classified.Result?.Source is TermSource output) callResults.Add(output.Term, definition);
    }

    private bool CheckRegisteredArgument(BoundValue bound, TypeRef target, Point point, RuntimeManagedMethod registration)
    {
        if (registration.TypeArguments.IsEmpty) return true;
        var term = BoundTerm(bound.Source, point);
        if (term is null) return false;
        var resolved = context.Get(state.Resolve, term);
        if (!resolved.IsSuccess)
        { Fail<object>(LoweringFailureKind.State, "运行时托管实参状态查询失败", resolved.Why); return false; }
        if (resolved.Value.ConstantValue is { IsZero: true }) return true;
        var value = Value(resolved.Value);
        if (value is null) return false;
        if (types.IsAssignable(value.Type, target)) return true;
        Fail<object>(LoweringFailureKind.RuntimeCall, "新值或比较值的静态类型不能赋给位置元素类型：" + value.Type + " → " + target,
            code: "lowering." + registration.DiagnosticName + ".Type");
        return false;
    }
}
