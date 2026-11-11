using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Dispatch;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    private sealed class CallDefinition(MethodRef method, BoundCall binding)
    {
        public MethodRef Method { get; } = method;
        public BoundCall Binding { get; } = binding;
        public LocalValue? Local { get; set; }
        public Term? Receiver { get; init; }
        public bool Virtual { get; init; }
    }
    private readonly Dictionary<CallIdentity, MethodRef> throws = [];
    private readonly CallNamingQuery? calls;
    private readonly BoundSourceQuery boundSources;
    private readonly Dictionary<CallIdentity, CallDefinition> callDefinitions = [];
    private readonly Dictionary<Term, CallDefinition> callResults = [];
    private readonly Dictionary<ManagedCall, CallDefinition> callStatements = new(ReferenceEqualityComparer.Instance);

    private void PrepareCall(Call call)
    {
        if (calls is null) { Fail<object>(LoweringFailureKind.UnknownCall, "没有调用分类来源"); return; }
        var classified = context.Get(calls, call.Identity);
        if (!classified.IsSuccess) { Fail<object>(LoweringFailureKind.Call, "调用分类失败", classified.Why); return; }
        var c = classified.Value;
        if (call.Unwind is not null) { Fail<object>(LoweringFailureKind.Exception, "调用的异常边尚未下降"); return; }
        if (c.Operation is { DoesNotReturn: true, Termination: RuntimeTermination.Throw, FixedThrownException: { } exception })
        {
            var constructor = types.CorlibMethod(exception, ".ctor");
            if (constructor is null) { Fail<object>(LoweringFailureKind.RuntimeCall, "固定异常缺少无参构造函数：" + exception); return; }
            throws.Add(call.Identity, constructor); return;
        }
        if (c.Kind == CallKind.Indirect && dispatch is not null)
        {
            var result = context.Get(dispatch, call.Identity);
            if (!result.IsSuccess || result.Value.Kind == DispatchKind.Unresolved)
            { var why = result.IsSuccess ? result.Value.Why : result.Why; Fail<object>(LoweringFailureKind.IndirectCall, "分派未解析", why, why?.Code); return; }
            var d = result.Value;
            var dispatched = new CallDefinition(d.Method!, d.Binding!) { Receiver = d.Receiver, Virtual = true };
            callDefinitions.Add(call.Identity, dispatched);
            if (d.Binding!.Result.Source is TermSource output) callResults.Add(output.Term, dispatched);
            return;
        }
        if (c.Kind != CallKind.Managed)
        {
            var kind = c.Kind switch { CallKind.Runtime => LoweringFailureKind.RuntimeCall,
                CallKind.System => LoweringFailureKind.SystemCall, CallKind.Indirect => LoweringFailureKind.IndirectCall,
                _ => LoweringFailureKind.UnknownCall };
            Fail<object>(kind, $"尚未下降：{c.Operation?.Name ?? c.Function?.ToString() ?? c.Kind.ToString()}", c.Why,
                c.Kind == CallKind.Runtime && c.Operation is { } operation ? "lowering.RuntimeCall." + operation.Name : null); return;
        }
        var candidates = c.Candidates!.Candidates;
        if (candidates.Length != 1)
        {
            var methods = candidates.Select(x => x.Entry.Method).ToArray();
            bool same = methods.Length > 1 && methods.All(m => m is not null) && methods.Skip(1).All(m =>
                m!.Method.IsStatic == methods[0]!.Method.IsStatic &&
                m.Method.GenericParameters.Count == methods[0]!.Method.GenericParameters.Count &&
                (m.Method.IsStatic || Equals(m.DeclaringType, methods[0]!.DeclaringType)) &&
                Equals(m.Concrete(m.Method.ReturnType), methods[0]!.Concrete(methods[0]!.Method.ReturnType)) &&
                m.Method.Parameters.Select(p => m.Concrete(p.Type)).SequenceEqual(methods[0]!.Method.Parameters.Select(p => methods[0]!.Concrete(p.Type))));
            Fail<object>(same ? LoweringFailureKind.FoldedCall : LoweringFailureKind.AmbiguousCall,
                same ? "相同代码折叠：多个托管签名相同的候选，身份未确定" : "多个候选的托管签名不同或不可用"); return;
        }
        if (call.DoesNotReturn)
        { Fail<object>(LoweringFailureKind.NonReturningCall, "托管方法体尚无不返回调用终结契约"); return; }
        var candidate = candidates[0];
        if (candidate.Binding.Value is not { } binding || candidate.Entry.Method is not { } method)
        { Fail<object>(LoweringFailureKind.Binding, candidate.Binding.Failure?.Detail ?? "调用没有托管身份"); return; }
        if (call.Unwind is not null) { Fail<object>(LoweringFailureKind.Exception, "调用的异常边尚未下降"); return; }
        var definition = new CallDefinition(method, binding);
        callDefinitions.Add(call.Identity, definition);
        if (binding.Result.Source is TermSource source) callResults.Add(source.Term, definition);
    }

    private ManagedValue? CallResult(CallDefinition definition)
    {
        if (definition.Local is { } local) return ReferenceType(local.Type) || IsFloat(local.Type) ? local : Mask(local, definition.Binding.Result.Type.Size * 8);
        var type = definition.Method.Concrete(definition.Method.Method.ReturnType);
        if (!IntegerType(type) && !IsFloat(type) && !ReferenceType(type)) return Fail<ManagedValue>(TypeFailure(type), "调用结果类型尚未下降");
        definition.Local = new(new(nextLocal++), type, StackWidth(definition.Binding.Result.Type.Size * 8));
        return ReferenceType(type) || IsFloat(type) ? definition.Local : Mask(definition.Local, definition.Binding.Result.Type.Size * 8);
    }

    private ManagedStatement? LowerCall(Call call, Point point)
    {
        if (throws.TryGetValue(call.Identity, out var constructor)) return new ManagedThrow(position, new NewObjectValue(constructor, [], types.PointerSize * 8));
        var d = callDefinitions[call.Identity];
        var args = new List<ManagedValue>();
        for (int i = 0; i < d.Binding.Parameters.Length; i++)
        {
            var value = CallArgument(d.Binding.Parameters[i], d.Method.Concrete(d.Method.Method.Parameters[i].Type), point);
            if (value is null) return null;
            args.Add(value);
        }
        var receiver = d.Receiver is { } target ? Value(target) : d.Binding.This is { } self ? CallArgument(self, d.Method.DeclaringType, point) : null;
        if (d.Binding.This is not null && receiver is null) return null;
        var statement = new ManagedCall(position, new(d.Method, receiver, args, d.Virtual), null);
        callStatements.Add(statement, d);
        return statement;
    }

    private ManagedValue? CallArgument(BoundValue bound, TypeRef type, Point point)
    {
        var term = BoundTerm(bound.Source, point);
        if (term is null) return null;
        var resolved = context.Get(state.Resolve, term);
        if (!resolved.IsSuccess) return Fail<ManagedValue>(LoweringFailureKind.State, "实参状态查询失败", resolved.Why);
        if (ReferenceType(type))
        {
            var reference = Value(resolved.Value);
            return reference is null ? null : Coerce(reference, type);
        }
        if (IsFloat(type))
        {
            var number = Value(resolved.Value, true);
            return number is null ? null : FloatBits(number, bound.Type.Size * 8);
        }
        if (!IntegerType(type)) return Fail<ManagedValue>(TypeFailure(type), "实参缺少托管类型的值定义");
        var value = Value(resolved.Value);
        return value is null ? null : new ConversionValue(ManagedTypes.IsSigned(type) ? ConversionKind.SignExtend : ConversionKind.ZeroExtend,
            value, type, bound.Type.Size * 8);
    }

    private Term? BoundTerm(BoundSource? source, Point point)
    {
        var result = context.Get(boundSources, new(source, point));
        if (result.IsSuccess) return result.Value;
        var why = result.Why!;
        return Fail<Term>(why.Code == "binding.source" ? LoweringFailureKind.Binding : LoweringFailureKind.State, why.Message, why.Cause);
    }
}
