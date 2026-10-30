using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;
using Cpp2CS.Idioms;

namespace Cpp2CS.Recovery;

internal static class DelegatesRules
{
    internal static void NormalizeDelegateChoices(this RecoveryScope ctx)
    {
        var definitions = ctx.function.Blocks.SelectMany(b => b.Statements.OfType<Define>()).ToDictionary(d => d.Target, d => d.Value);
        Expr ExpandIdentity(Expr expression)
        {
            var seen = new HashSet<Variable>();
            while (expression is Use use && seen.Add(use.Variable) && definitions.TryGetValue(use.Variable, out var value))
                expression = value;
            return expression;
        }

        bool Constructor(Call call) => call is { Op: null, Kind: CallKind.Direct, Target: Const target } && ctx.facts.EntriesAt(target.Value).Any(e => e.Method is { Method.Name: ".ctor", DeclaringType: DefinitionRef type } && DelegateFacts.IsDelegate(type));
        bool GenericIdentity(Call call, int argument, MethodRef target) => call.Target is Const address && argument < call.Sources.Length && ctx.owner.abi.Classify(target, out _)?.MethodInfo?.Register == call.Sources[argument] && ctx.facts.EntriesAt(address.Value).Any(e => e.Method?.Method == target.Method);
        bool ObjectConstructor(Call call, DefinitionRef type) => !DelegateFacts.IsDelegate(type) && call.Target is Const target && ctx.facts.EntriesAt(target.Value).Any(e => e.Method is { Method: { Name: ".ctor", IsStatic: false } method } && method.Owner == type.Definition);
        if (CallIdentityChoices.Split(ctx.function, Constructor, ExpandIdentity) | CallIdentityChoices.SplitGeneric(ctx.function, GenericIdentity, ExpandIdentity) | CallIdentityChoices.SplitIndirect(ctx.function) | CallIdentityChoices.SplitStores(ctx.function) | MergedAllocations.Run(ctx.function, ObjectConstructor))
            Cpp2CS.Machine.Ssa.Propagate.Run(ctx.function, ctx.Dominators);
    }

    internal static void DelegateAllocation(this RecoveryScope ctx, Block block, int index, Call allocation, DefinitionRef type, Variable created)
    {
        bool Constructor(Call call) => call.Op is { Kind: OpKind.CallMethodPointer, Operand: MethodRef { Method: { Name: ".ctor", IsStatic: false } pointerCtor } } && pointerCtor.Owner == type.Definition || call is { Op: null, Kind: CallKind.Direct, Target: Const target } && ctx.facts.EntriesAt(target.Value).Any(e => e.Method is { Method: { Name: ".ctor", IsStatic: false } m } && m.Owner == type.Definition);
        var constructors = ctx.blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => Constructor(c) && ConstructionRules.Receiver(c) is Use u && u.Variable == created).ToArray();
        if (constructors.Length == 2 && ctx.BranchConstructors(block, index, allocation, type, created))
        {
            foreach (var branchConstructor in constructors)
                ctx.State.Construction.delegateCreations[branchConstructor] = type;
            return;
        }

        void Reject(string reason)
        {
            var hole = ctx.Hole(allocation.Address, "委托 " + reason, rule: "DelegateAllocation");
            ctx.ledger.Block(allocation, hole);
        }

        if (constructors.Length != 1)
        {
            Reject(constructors.Length > 1 ? "同一分配有多个构造候选" : ctx.phiUses.ContainsKey(created) ? "φ 汇合后构造尚未支持" : "分配没有唯一构造候选");
            return;
        }

        var constructor = constructors[0];
        var middle = new List<Stmt>();
        Block? destination = null;
        foreach (var (current, statement) in AllocationPairing.Following(block, index))
        {
            if (ReferenceEquals(statement, constructor))
            {
                destination = current;
                break;
            }

            middle.Add(statement);
        }

        if (destination is null)
        {
            Reject("分配与构造不在唯一直线块链，时序未证明");
            return;
        }

        var lookup = ctx.State.Calls.virtualDelegates.GetValueOrDefault(constructor);
        bool LookupStep(Stmt statement) => lookup is not null && (statement is Define d && lookup.Metadata.Contains(d.Target) || statement is Call { Op.Kind: OpKind.NullCheck, Arguments: [var receiver] } && receiver == lookup.Receiver);
        // IL2CPP 将 new Action(receiver.Virtual) 拆为分配、判空、虚表查询、构造。
        // 只吸收此委托自身的查询；其他副作用与异常保护域仍由配对检查约束。
        if (AllocationPairing.MotionProblem(ctx.function.Range, block, allocation, destination, constructor, middle.Where(s => !LookupStep(s)), created) is { } problem)
        {
            Reject(problem);
            return;
        }

        foreach (var statement in middle.Where(LookupStep))
            ctx.State.Lowering.dropped.Add(statement);
        ctx.State.Lowering.dropped.Add(allocation);
        ctx.State.Construction.constructed[constructor] = created;
        ctx.State.Construction.delegateCreations[constructor] = type;
    }

    [InvocationRule(10)]
    internal static RecoveryResult<bool> LowerDelegateCreation(this LoweringScope ctx, Call call, List<ManagedStatement> output)
    {
        if (!ctx.State.Construction.delegateCreations.ContainsKey(call))
            return false;
        if (ctx.Values.CreateDelegate(call, output) is { } failure)
            return failure;
        return true;
    }

    internal static RecoveryFailure? CreateDelegate(this RecoveryScope ctx, Call call, List<ManagedStatement> output)
    {
        var address = call.Address;
        var type = ctx.State.Construction.delegateCreations[call];
        var registers = CallResolution.ArgumentsOf(call);
        if (DelegateFacts.Constructor(type) is null || DelegateFacts.Invoke(type) is not { } invoke)
            return RecoveryDiagnostics.Fail(address, "委托 具体分配类型没有标准构造与唯一 Invoke", rule: "CreateDelegate");
        if (!registers.TryGetValue(Storage.Gpr(1), out var target))
            return RecoveryDiagnostics.Fail(address, "委托 构造缺少绑定对象", rule: "CreateDelegate");
        var lookup = ctx.State.Calls.virtualDelegates.GetValueOrDefault(call);
        var targetMethod = lookup is not null ? ctx.VirtualDelegateMethod(lookup) : registers.TryGetValue(Storage.Gpr(2), out var identity) && ctx.Expand(identity) is Symbol { Kind: SymbolKind.Method, Value: MethodRef direct } ? direct : null;
        if (targetMethod is null)
            return RecoveryDiagnostics.Fail(address, "委托 方法身份或虚表槽位未确定", rule: "CreateDelegate");
        if (!ctx.Bound(targetMethod.DeclaringType) || targetMethod.MethodArguments.Any(t => !ctx.Bound(t)) || targetMethod.Method.GenericParameters.Count != targetMethod.MethodArguments.Count)
            return RecoveryDiagnostics.Fail(address, "委托 目标方法含未确定的泛型参数", rule: "CreateDelegate");
        if (targetMethod.Method.Owner.IsValueType)
            return RecoveryDiagnostics.Fail(address, "委托 值类型目标尚未支持", rule: "CreateDelegate");
        if (lookup is null && targetMethod.Method.IsAbstract)
            return RecoveryDiagnostics.Fail(address, "委托 直接符号指向抽象方法", rule: "CreateDelegate");
        var parameters = invoke.Method.Parameters.Select(p => CallResolution.Concrete(invoke, p.Type)).ToArray();
        var accepts = targetMethod.Method.Parameters.Select(p => CallResolution.Concrete(targetMethod, p.Type)).ToArray();
        var result = CallResolution.Concrete(targetMethod, targetMethod.Method.ReturnType);
        var returns = CallResolution.Concrete(invoke, invoke.Method.ReturnType);
        bool Compatible(TypeRef from, TypeRef to) => from.Equals(to) || ctx.types.IsAssignable(from, to);
        if (parameters.Length != accepts.Length || !parameters.Zip(accepts).All(p => Compatible(p.First, p.Second)) || !Compatible(result, returns))
            return RecoveryDiagnostics.Fail(address, "委托 目标方法与 Invoke 签名不兼容（开放绑定或绑定静态首参尚未支持）", rule: "CreateDelegate");
        ManagedValue receiver;
        var binding = lookup is not null ? DelegateBinding.VirtualInstance : targetMethod.Method.IsStatic ? DelegateBinding.Static : DelegateBinding.ClosedInstance;
        if (binding == DelegateBinding.Static)
        {
            if (ctx.Expand(target) is not Const { Value: 0 })
                return RecoveryDiagnostics.Fail(address, "委托 静态绑定对象不是 null", rule: "CreateDelegate");
            receiver = new ConstantValue(0, ctx.types.Object, 64);
        }
        else
        {
            if (ctx.Expand(target) is Const { Value: 0 })
                return RecoveryDiagnostics.Fail(address, "委托 闭合实例目标为 null", rule: "CreateDelegate");
            if (!ctx.RecoverAs(target, targetMethod.DeclaringType, address).TryGet(out receiver, out var failure))
                return failure;
        }

        return ctx.Assign(address, ctx.State.Construction.constructed[call], () => new DelegateValue(type, receiver, targetMethod, binding), output);
    }

    internal static bool Bound(this RecoveryScope ctx, TypeRef type) => type switch
    {
        GenericParameterRef parameter => ctx.SharedDefinition && ctx.method.TypeArguments.Concat(ctx.method.MethodArguments).Contains(parameter),
        DefinitionRef d => d.Arguments.Count == d.Definition.GenericParameters.Count && d.Arguments.All(ctx.Bound),
        ArrayRef a => ctx.Bound(a.Element),
        ByRefRef b => ctx.Bound(b.Element),
        PointerRef p => ctx.Bound(p.Element),
        _ => true,
    };
}
