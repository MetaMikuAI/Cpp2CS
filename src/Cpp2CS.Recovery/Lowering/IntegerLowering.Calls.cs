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
    private readonly HashSet<CallIdentity> interfaceLookups = [];
    private readonly CallNamingQuery? calls;
    private readonly BoundSourceQuery boundSources;
    private SharedCallQuery? sharedCalls;
    private readonly Dictionary<CallIdentity, CallDefinition> callDefinitions = [];
    private readonly Dictionary<Term, CallDefinition> callResults = [];
    private readonly Dictionary<ManagedCall, CallDefinition> callStatements = new(ReferenceEqualityComparer.Instance);

    private void PrepareCall(Call call, Point point)
    {
        if (calls is null) { Fail<object>(LoweringFailureKind.UnknownCall, "没有调用分类来源"); return; }
        var classified = context.Get(calls, call.Identity);
        if (!classified.IsSuccess) { Fail<object>(LoweringFailureKind.Call, "调用分类失败", classified.Why); return; }
        var c = classified.Value;
        if (c.Kind is CallKind.Runtime or CallKind.System && c.Binding is { } external)
            for (int i = 0; i < external.Arguments.Length; i++)
            {
                var bound = external.Arguments[i];
                var input = context.Get(boundSources, new(bound.Source, point));
                // Pointee 是登记过的内容读取，不把装箱等读取缓冲区的地址当作逃逸的值。
                var name = c.Function?.Arguments.ElementAtOrDefault(i);
                bool contents = c.Operation?.Inputs.Any(v => v.Name == name && v.Use == RuntimeInputUse.Pointee) == true;
                if (input.IsSuccess && RejectAddressUse([input.Value], "运行时或系统函数的实参", contents)) return;
            }
        if (call.Unwind is not null) { Fail<object>(LoweringFailureKind.Exception, "调用的异常边尚未下降"); return; }
        if (c.Kind == CallKind.Runtime && c.Operation is { Result.Kind: RuntimeValueKind.InvokeData })
        { interfaceLookups.Add(call.Identity); return; }
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
        if (c.Kind == CallKind.Runtime && c.Operation is { Il.Name: "NewObject" }) { PrepareAllocation(call, c); return; }
        if (c.Kind == CallKind.Runtime && c.Operation is { Il.Name: "NewArray" }) { PrepareVector(call, c); return; }
        if (c.Kind == CallKind.Runtime && c.Operation is { Il.Name: "IsInst" or "CastClass" }) { PrepareTypeCheck(call, c); return; }
        if (c.Kind == CallKind.Runtime && c.Operation is { Il.Name: "Box" }) { PrepareBox(call, c); return; }
        if (c.Kind == CallKind.Runtime && c.Operation is { Il.Name: "Unbox" }) { PrepareUnbox(call, c); return; }
        if (c.Kind == CallKind.Runtime && c.Operation is { DoesNotReturn: true, Termination: RuntimeTermination.Throw, FixedThrownException: null, Il.Name: "Throw" })
        { PrepareThrow(call, c); return; }
        if (c.Kind != CallKind.Managed)
        {
            var kind = c.Kind switch { CallKind.Runtime => LoweringFailureKind.RuntimeCall,
                CallKind.System => LoweringFailureKind.SystemCall, CallKind.Indirect => LoweringFailureKind.IndirectCall,
                _ => LoweringFailureKind.UnknownCall };
            // 没认出的目标写明是谁，报告才能按目标归并。
            var unknown = c.Kind != CallKind.Unknown ? null : call.Target switch
            {
                ImageFunction image => $"映像函数 0x{image.EntryOffset:x}",
                ImportedTarget import => "导入 " + import.Symbol.Name,
                _ => null,
            };
            Fail<object>(kind, unknown is not null ? "目标没有托管身份或目录对应：" + unknown
                : $"尚未下降：{c.Operation?.Name ?? c.Function?.ToString() ?? c.Kind.ToString()}", c.Why,
                c.Kind == CallKind.Runtime && c.Operation is { } operation ? "lowering.RuntimeCall." + operation.Name : null); return;
        }
        var candidates = c.Candidates!.Candidates;
        if (candidates.Any(x => x.Entry.Kind == BindingEntryKind.SharedGeneric))
        {
            var shared = context.Get(sharedCalls ??= new(binder, calls, valueNames, boundSources), call.Identity);
            if (shared.IsSuccess)
            {
                var resolved = new CallDefinition(shared.Value.Method, shared.Value.Binding);
                callDefinitions.Add(call.Identity, resolved);
                if (resolved.Binding.Result.Source is TermSource output) callResults.Add(output.Term, resolved);
                return;
            }
            // 混合折叠只有见证成立才消歧；否则沿用原有的多候选失败。
            if (candidates.All(x => x.Entry.Kind == BindingEntryKind.SharedGeneric))
            {
                var reason = shared.Why;
                var code = reason?.Code switch
                {
                    "binding.shared-call.signature" => "lowering.SharedCall.Signature",
                    "binding.shared-call.mismatch" => "lowering.SharedCall.Mismatch",
                    _ => "lowering.SharedCall.Witness",
                };
                Fail<object>(LoweringFailureKind.Call, reason?.Message ?? "方法信息实参没有命名来源。", reason, code);
                return;
            }
        }
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
        if (definition.Local is { } local) return Opaque(local.Type) || ReferenceType(local.Type) || IsFloat(local.Type) || types.Kind(local.Type) == TypeKind.Struct ? local : Mask(local, definition.Binding.Result.Type.Size * 8);
        var type = definition.Method.Concrete(definition.Method.Method.ReturnType);
        if (GenericStruct(type)) return GenericFailure<ManagedValue>("Struct", "含类型参数的值类型调用结果尚未下降");
        if (!Scalar(type) && types.Kind(type) != TypeKind.Struct) return Fail<ManagedValue>(TypeFailure(type), "调用结果类型尚未下降");
        definition.Local = new(new(nextLocal++), type, types.Kind(type) == TypeKind.Struct ? 0 : StackWidth(definition.Binding.Result.Type.Size * 8));
        return Opaque(type) || ReferenceType(type) || IsFloat(type) || types.Kind(type) == TypeKind.Struct ? definition.Local : Mask(definition.Local, definition.Binding.Result.Type.Size * 8);
    }

    private ManagedStatement? LowerCall(Call call, Point point)
    {
        if (throws.TryGetValue(call.Identity, out var constructor)) return new ManagedThrow(position, new NewObjectValue(constructor, [], types.PointerSize * 8));
        if (typeChecks.ContainsKey(call.Identity)) return LowerTypeCheck(call, point);
        if (boxes.ContainsKey(call.Identity)) return LowerBox(call, point);
        if (unboxes.ContainsKey(call.Identity)) return LowerUnbox(call, point);
        if (vectors.ContainsKey(call.Identity) || thrown.ContainsKey(call.Identity)) return LowerRuntimeStatement(call, point);
        var d = callDefinitions[call.Identity];
        var args = new List<ManagedValue>();
        constructions.TryGetValue(call.Identity, out var created);
        constructing = created;
        for (int i = 0; i < d.Binding.Parameters.Length; i++)
        {
            var value = CallArgument(d.Binding.Parameters[i], d.Method.Concrete(d.Method.Method.Parameters[i].Type), point);
            if (value is null) return null;
            args.Add(value);
        }
        constructing = null;
        if (created is not null) return new ManagedAssignment(position, created.Local!, new NewObjectValue(d.Method, args, types.PointerSize * 8));
        TypeRef receiverType = d.Method.Method.Owner.IsValueType ? new ByRefRef(d.Method.DeclaringType) : d.Method.DeclaringType;
        var receiver = d.Receiver is { } target
            ? receiverType is ByRefRef byref ? AddressArgument(target, byref.Element) : Value(target)
            : d.Binding.This is { } self ? CallArgument(self, receiverType, point, true) : null;
        if (receiver is not null && Opaque(receiver.Type)) return GenericFailure<ManagedStatement>("Receiver", "类型参数值作为调用接收者需要 constrained. 语义");
        if (receiver is not null) receiver = Coerce(receiver, receiverType);
        if (d.Binding.This is not null && receiver is null) return null;
        var statement = new ManagedCall(position, new(d.Method, receiver, args, d.Virtual), null);
        callStatements.Add(statement, d);
        return statement;
    }

    private ManagedValue? CallArgument(BoundValue bound, TypeRef type, Point point, bool receiver = false)
    {
        if (GenericStruct(type)) return GenericFailure<ManagedValue>("Struct", "含类型参数的值类型实参尚未下降");
        if (types.Kind(type) == TypeKind.Struct)
        {
            var bits = context.Get(boundSources, new(bound.Source, point));
            if (bits.IsSuccess && RejectAddressUse([bits.Value], "非按引用的结构体形参")) return null;
            return bound.Source is { } source ? StructValue(source, type, point)
                : Fail<ManagedValue>(LoweringFailureKind.Binding, "结构体实参没有绑定来源", code: "lowering.Struct.Binding");
        }
        var term = BoundTerm(bound.Source, point);
        if (term is null) return null;
        var resolved = context.Get(state.Resolve, term);
        if (!resolved.IsSuccess) return Fail<ManagedValue>(LoweringFailureKind.State, "实参状态查询失败", resolved.Why);
        if (type is ByRefRef addressType) return AddressArgument(resolved.Value, addressType.Element);
        if (RejectAddressUse([resolved.Value], type is PointerRef ? "非托管指针形参" : "非按引用形参")) return null;
        var knownType = StaticType(resolved.Value);
        if (receiver && knownType is not null && Opaque(knownType)) return GenericFailure<ManagedValue>("Receiver", "类型参数值作为调用接收者需要 constrained. 语义");
        if (Opaque(type) || knownType is not null && Opaque(knownType))
        {
            var opaque = Value(resolved.Value);
            return opaque is null ? null : Coerce(opaque, type);
        }
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
        if (!IntegerType(type))
        {
            var shape = type switch
            {
                ByRefRef => "按引用传递的实参", PointerRef => "非托管指针实参", GenericParameterRef => "类型参数实参",
                DefinitionRef { Definition.IsValueType: true } => "结构体实参", _ => "其他类型的实参",
            };
            return Fail<ManagedValue>(TypeFailure(type), "实参缺少托管类型的值定义：" + shape);
        }
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
