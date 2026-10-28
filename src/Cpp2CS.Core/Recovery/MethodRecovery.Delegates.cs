using Cpp2CS.Recovery.Analysis;
using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private readonly Dictionary<Call, DefinitionRef> delegateCreations = new(ReferenceEqualityComparer.Instance);

        private void NormalizeDelegateChoices()
        {
            var definitions = function.Blocks.SelectMany(b => b.Statements.OfType<Define>()).ToDictionary(d => d.Target, d => d.Value);
            Expr ExpandIdentity(Expr expression)
            {
                var seen = new HashSet<Variable>();
                while (expression is Use use && seen.Add(use.Variable) && definitions.TryGetValue(use.Variable, out var value)) expression = value;
                return expression;
            }
            bool Constructor(Call call) => call is { Op: null, Kind: CallKind.Direct, Target: Const target }
                && facts.EntriesAt(target.Value).Any(e => e.Method is { Method.Name: ".ctor", DeclaringType: DefinitionRef type }
                    && DelegateFacts.IsDelegate(type));
            if (DelegateConstructorChoices.Split(function, Constructor, ExpandIdentity))
                Ssa.Propagate.Run(function, Ssa.Dominators.Compute(function));
        }

        private void DelegateAllocation(Block block, int index, Call allocation, DefinitionRef type, Variable created)
        {
            bool Constructor(Call call) => call.Op is { Kind: OpKind.CallMethodPointer, Operand: MethodRef { Method: { Name: ".ctor", IsStatic: false } pointerCtor } }
                    && pointerCtor.Owner == type.Definition
                || call is { Op: null, Kind: CallKind.Direct, Target: Const target }
                    && facts.EntriesAt(target.Value).Any(e => e.Method is { Method: { Name: ".ctor", IsStatic: false } m } && m.Owner == type.Definition);
            var constructors = blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => Constructor(c) && Receiver(c) is Use u && u.Variable == created).ToArray();
            if (constructors.Length == 2 && BranchConstructors(block, index, allocation, type, created))
            {
                foreach (var branchConstructor in constructors) delegateCreations[branchConstructor] = type;
                return;
            }
            void Reject(string reason)
            {
                var hole = Hole(allocation.Address, "委托 " + reason);
                ledger.Block(allocation, hole);
            }
            if (constructors.Length != 1)
            {
                Reject(constructors.Length > 1 ? "同一分配有多个构造候选" : phiUses.ContainsKey(created) ? "φ 汇合后构造尚未支持" : "分配没有唯一构造候选");
                return;
            }
            var constructor = constructors[0];
            var middle = new List<Stmt>();
            Block? destination = null;
            foreach (var (current, statement) in AllocationPairing.Following(block, index))
            {
                if (ReferenceEquals(statement, constructor)) { destination = current; break; }
                middle.Add(statement);
            }
            if (destination is null) { Reject("分配与构造不在唯一直线块链，时序未证明"); return; }
            var lookup = virtualDelegates.GetValueOrDefault(constructor);
            bool LookupStep(Stmt statement) => lookup is not null && (statement is Define d && lookup.Metadata.Contains(d.Target)
                || statement is Call { Op.Kind: OpKind.NullCheck, Arguments: [var receiver] } && receiver == lookup.Receiver);
            // IL2CPP 将 new Action(receiver.Virtual) 拆为分配、判空、虚表查询、构造。
            // 只吸收此委托自身的查询；其他副作用与异常保护域仍由配对检查约束。
            if (AllocationPairing.MotionProblem(function.Range, block, allocation, destination, constructor, middle.Where(s => !LookupStep(s)), created) is { } problem)
            { Reject(problem); return; }
            foreach (var statement in middle.Where(LookupStep)) dropped.Add(statement);
            dropped.Add(allocation);
            constructed[constructor] = created;
            delegateCreations[constructor] = type;
        }

        [InvocationRule(10)]
        private RecoveryResult<bool> LowerDelegateCreation(Call call, List<ManagedStatement> output)
        {
            if (!delegateCreations.ContainsKey(call)) return false;
            if (CreateDelegate(call, output) is { } failure) return failure;
            return true;
        }

        private RecoveryFailure? CreateDelegate(Call call, List<ManagedStatement> output)
        {
            var address = call.Address;
            var type = delegateCreations[call];
            var registers = ArgumentsOf(call);
            if (DelegateFacts.Constructor(type) is null || DelegateFacts.Invoke(type) is not { } invoke)
                return Fail(address, "委托 具体分配类型没有标准构造与唯一 Invoke");
            if (!registers.TryGetValue(Storage.Gpr(1), out var target)) return Fail(address, "委托 构造缺少绑定对象");
            var lookup = virtualDelegates.GetValueOrDefault(call);
            var targetMethod = lookup is not null ? VirtualDelegateMethod(lookup)
                : registers.TryGetValue(Storage.Gpr(2), out var identity) && Expand(identity) is Symbol { Kind: SymbolKind.Method, Value: MethodRef direct } ? direct : null;
            if (targetMethod is null) return Fail(address, "委托 方法身份或虚表槽位未确定");
            if (!Bound(targetMethod.DeclaringType) || targetMethod.MethodArguments.Any(t => !Bound(t))
                || targetMethod.Method.GenericParameters.Count != targetMethod.MethodArguments.Count)
                return Fail(address, "委托 目标方法含未确定的泛型参数");
            if (targetMethod.Method.Owner.IsValueType) return Fail(address, "委托 值类型目标尚未支持");
            if (lookup is null && targetMethod.Method.IsAbstract) return Fail(address, "委托 直接符号指向抽象方法");
            var parameters = invoke.Method.Parameters.Select(p => Concrete(invoke, p.Type)).ToArray();
            var accepts = targetMethod.Method.Parameters.Select(p => Concrete(targetMethod, p.Type)).ToArray();
            var result = Concrete(targetMethod, targetMethod.Method.ReturnType);
            var returns = Concrete(invoke, invoke.Method.ReturnType);
            bool Compatible(TypeRef from, TypeRef to) => from.Equals(to) || types.IsAssignable(from, to);
            if (parameters.Length != accepts.Length || !parameters.Zip(accepts).All(p => Compatible(p.First, p.Second)) || !Compatible(result, returns))
                return Fail(address, "委托 目标方法与 Invoke 签名不兼容（开放绑定或绑定静态首参尚未支持）");
            ManagedValue receiver;
            var binding = lookup is not null ? DelegateBinding.VirtualInstance : targetMethod.Method.IsStatic ? DelegateBinding.Static : DelegateBinding.ClosedInstance;
            if (binding == DelegateBinding.Static)
            {
                if (Expand(target) is not Const { Value: 0 }) return Fail(address, "委托 静态绑定对象不是 null");
                receiver = new ConstantValue(0, types.Object, 64);
            }
            else
            {
                if (Expand(target) is Const { Value: 0 }) return Fail(address, "委托 闭合实例目标为 null");
                if (!RecoverAs(target, targetMethod.DeclaringType, address).TryGet(out receiver, out var failure)) return failure;
            }
            return Assign(address, constructed[call], () => new DelegateValue(type, receiver, targetMethod, binding), output);
        }

        private bool Bound(TypeRef type) => type switch
        {
            GenericParameterRef parameter => SharedDefinition && method.TypeArguments.Concat(method.MethodArguments).Contains(parameter),
            DefinitionRef d => d.Arguments.Count == d.Definition.GenericParameters.Count && d.Arguments.All(Bound),
            ArrayRef a => Bound(a.Element), ByRefRef b => Bound(b.Element), PointerRef p => Bound(p.Element), _ => true,
        };
    }
}
