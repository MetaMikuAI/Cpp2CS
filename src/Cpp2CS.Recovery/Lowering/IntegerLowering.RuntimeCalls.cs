using System.Collections.Immutable;
using Cpp2CS.Managed;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Checks;
using Cpp2CS.Recovery.Dispatch;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    private sealed class CheckedDispatchReceiver(DispatchQuery dispatch) : Query<CallIdentity, Term?>
    {
        public override Outcome<Term?> Compute(QueryContext c, CallIdentity key)
        {
            var result = c.Get(dispatch, key);
            return result.IsSuccess ? Outcome<Term?>.Success(result.Value.Kind == DispatchKind.Unresolved ? null : result.Value.Receiver)
                : result.Propagate<Term?>();
        }
    }
    private CheckQueries? runtimeChecks;
    private readonly Dictionary<CallIdentity, (BoundValue Value, MethodRef Exception)> nullChecks = [];

    private void PrepareNullCheck(Call call, ClassifiedCall classified)
    {
        if (classified.Inputs?.GetValueOrDefault("value") is not { } input)
        { Fail<object>(LoweringFailureKind.Binding, "判空调用没有绑定的输入", code: "lowering.NullCheck.Binding"); return; }
        if (locations is not null)
        {
            runtimeChecks ??= new(state, calls!, locations, dispatch is null ? null : new CheckedDispatchReceiver(dispatch));
            var check = context.Get(runtimeChecks.NullChecks, call.Identity);
            if (check.IsSuccess && check.Value.CanAbsorb) { interfaceLookups.Add(call.Identity); return; }
        }
        var exception = types.CorlibMethod("System.NullReferenceException", ".ctor");
        if (exception is null)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "判空异常缺少无参构造函数", code: "lowering.NullCheck.Exception"); return; }
        nullChecks.Add(call.Identity, (input, exception));
    }

    private ManagedStatement? LowerNullCheck(Call call, Point point)
    {
        var definition = nullChecks[call.Identity];
        var input = BoundTerm(definition.Value.Source, point);
        if (input is null) return null;
        var value = Value(input);
        if (value is null) return null;
        return new ManagedCheck(position, new ComparisonValue(ComparisonKind.Equal, value,
            new ConstantValue(0, value.Type, value.Width), types.Boolean), definition.Exception);
    }

    private MethodRef? RuntimeMethod(ClassifiedCall call, string input)
    {
        if (valueNames is null || call.Inputs?.GetValueOrDefault(input)?.Source is not TermSource term) return null;
        var named = context.Get(valueNames, term.Term);
        return named.IsSuccess ? named.Value.Name switch
        {
            EntityName { Entity: MethodEntity entity } => entity.Method,
            ParameterName { MethodInformation: true } => method,
            _ => null,
        } : null;
    }

    private void PrepareProfileException(Call call, ClassifiedCall classified)
    {
        Fail<object>(LoweringFailureKind.RuntimeCall,
            "运行时 profile 桩替换了原托管实现及异常；当前不能把该替代桩作为已恢复的托管方法体",
            code: "lowering.Profile.Unavailable");
    }

    private void PrepareGenericVirtual(Call resolver)
    {
        if (dispatch is null)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "泛型虚解析缺少分派查询", code: "lowering.ResolveGenericVirtual.Query"); return; }
        int consumers = 0; Reason? reason = null;
        foreach (var call in function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => c.Target is ComputedTarget))
        {
            var found = context.Get(dispatch, call.Identity);
            if (found.IsSuccess && found.Value.Kind != DispatchKind.Unresolved && found.Value.GenericResolution == resolver.Identity) consumers++;
            else if (found.IsSuccess && found.Value.GenericResolution == resolver.Identity)
                reason ??= found.Value.Why;
        }
        if (consumers != 1)
        { Fail<object>(LoweringFailureKind.RuntimeCall, consumers == 0 ? "泛型虚解析没有唯一可吸收的随后间接调用" : "泛型虚解析被多次调用消费",
            reason, reason?.Code.Replace("dispatch.generic-", "lowering.ResolveGenericVirtual.", StringComparison.Ordinal)
                ?? "lowering.ResolveGenericVirtual.Use"); return; }
        interfaceLookups.Add(resolver.Identity);
    }

    private void PrepareGetType(Call call, ClassifiedCall classified)
    {
        var target = RuntimeMethod(classified, "target");
        var caller = RuntimeMethod(classified, "caller");
        if (caller is null || caller.Method.Owner.Assembly != method.Method.Owner.Assembly)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "类型查找的提示程序集与当前输出调用位置不一致或未命名", code: "lowering.GetType.Caller"); return; }
        if (target is null || target.Method.Owner is not { Assembly: "mscorlib.dll", FullName: "System.Type" }
            || !target.Method.IsStatic || target.Method.Name != "GetType" || target.Method.GenericParameters.Count != 0
            || target.Method.Parameters.Count is < 1 or > 3 || target.Method.ReturnType is not DefinitionRef { Definition.FullName: "System.Type" }
            || target.Method.Parameters.Where((p, i) => p.Type is not DefinitionRef d
                || d.Definition.Assembly != "mscorlib.dll" || d.Definition.FullName != (i == 0 ? "System.String" : "System.Boolean")).Any()
            || classified.Binding is not { } binding || binding.Arguments.Length != target.Method.Parameters.Count + 2)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "类型查找目标不是与运行时输入一致的 System.Type.GetType 重载", code: "lowering.GetType.Method"); return; }
        int count = target.Method.Parameters.Count;
        var signature = binder.Classify(binding.Signature.Signature with
            { Parameters = binding.Signature.Signature.Parameters.Take(count).ToImmutableArray() });
        if (signature.Value is not { } classifiedSignature)
        { Fail<object>(LoweringFailureKind.Binding, signature.Failure!.Detail, code: "lowering.GetType.Binding"); return; }
        var bound = binding with { Signature = classifiedSignature, Arguments = binding.Arguments.Take(count).ToImmutableArray() };
        var definition = new CallDefinition(target, bound);
        callDefinitions.Add(call.Identity, definition);
        if (bound.Result.Source is TermSource output) callResults.Add(output.Term, definition);
    }

    private UncheckedUnboxQuery? uncheckedUnboxEvidence;
    private void PrepareUncheckedUnbox(Call call, ClassifiedCall classified)
    {
        if (classified.Inputs?.GetValueOrDefault("object") is not { Source: TermSource input } obj
            || classified.Result?.Source is not TermSource output)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "无检查拆箱的对象或结果没有完整绑定", code: "lowering.UnboxUnchecked.Binding"); return; }
        if (calls is null || valueNames is null)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "无检查拆箱没有类型命名查询", code: "lowering.UnboxUnchecked.Type"); return; }
        var evidence = context.Get(uncheckedUnboxEvidence ??= new(state, calls, valueNames), call.Identity);
        if (!evidence.IsSuccess)
        { Fail<object>(LoweringFailureKind.RuntimeCall, evidence.Why!.Message, evidence.Why,
            evidence.Why.Code == "check.unbox.nonnull" ? "lowering.UnboxUnchecked.NonNull"
                : evidence.Why.Code == "check.unbox.success" ? "lowering.UnboxUnchecked.Success" : "lowering.UnboxUnchecked.Type"); return; }
        var type = evidence.Value.Type;
        if (BoxedScalar(type, "UnboxUnchecked") is null) return;
        unboxes.Add(call.Identity, new(obj, type, output.Term, new(new(nextLocal++), type, types.Size(type) * 8)));
    }
}
