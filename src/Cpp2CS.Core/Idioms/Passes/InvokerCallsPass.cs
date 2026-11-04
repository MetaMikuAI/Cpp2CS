using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery;

namespace Cpp2CS.Idioms;

/// <summary>MethodInfo.invoker_method 的参数数组拆为独立实参，保留值参数与返回值的存储地址。</summary>
internal static class InvokerCallsPass
{
    internal static bool InvokerCalls(this IdiomState state)
    {
        var changed = false;
        foreach (var block in state.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call { Op: null, Kind: CallKind.Indirect } call
                    || state.defs.Expand(call.Target) is not Load { Width: 64 } target
                    || SplitPass.Split(target.Address) is not (Symbol { Kind: SymbolKind.Method, Value: MethodRef method } entity, RuntimeLayout.MethodInvoker)) continue;
                Expr? Input(int register) => call.ArgumentIndex(Storage.Gpr(register)) is var index && index >= 0
                    ? state.defs.Expand(call.Arguments[index]) : null;
                if (Input(0) != new Load(entity, 64) || Input(1) != entity
                    || Input(2) is not { } receiver || Input(3) is not { } arguments || Input(4) is not { } output) continue;
                var native = state.self is { } self ? (MethodRef)GenericContext.Instantiate(method, self)! : method;
                var signature = state.owner.abi.Invoker(native);
                if (ManagedAbi.SharedValue(native.Concrete(native.Method.ReturnType))
                    || signature.Indirections.Any(a => a.Size <= 0 && !ManagedAbi.SharedValue(a.Type))) continue;
                Expr Offset(Expr value, int offset) => offset == 0 ? value : Fold.Simplify(new Binary(BinOp.Add, value, Expr.C((ulong)offset, 64), 64));
                var inputs = new List<Expr>();
                var proofs = new List<SharedInvokerArguments.Proof>();
                var valid = true;
                if (!method.Method.IsStatic) inputs.Add(receiver);
                for (var parameter = 0; parameter < method.Method.Parameters.Count; parameter++)
                {
                    if (ManagedAbi.SharedValue(native.Concrete(native.Method.Parameters[parameter].Type)))
                    {
                        var proof = SharedInvokerArguments.Prove(state, block, call, arguments, parameter, method.Concrete(method.Method.Parameters[parameter].Type));
                        if (proof is null) { valid = false; break; }
                        proofs.Add(proof);
                        inputs.Add(proof.Value);
                    }
                    else inputs.Add(new Load(Offset(arguments, parameter * 8), 64));
                }
                if (!valid) continue;
                inputs.Add(entity);
                if (!ManagedTypes.IsVoid(method.Method.ReturnType)) inputs.Add(output);
                var replacement = call with
                {
                    Op = new(OpKind.InvokeGeneric, method),
                    Target = entity,
                    Arguments = inputs.ToArray(),
                    Sources = Enumerable.Range(0, inputs.Count).Select(Storage.Gpr).ToArray(),
                    Results = [],
                    Defines = [],
                    StackPointer = null,
                };
                var statements = new List<Stmt> { replacement };
                // invoker 自身返回 void，原保守 clobber 不能冒充目标方法的返回寄存器。
                statements.AddRange(call.Defines.OfType<Variable>().Select(v => new Define(call.Address, v, new Unknown("invoker 未定义返回寄存器", v.Width))));
                block.Statements.RemoveAt(i);
                block.Statements.InsertRange(i, statements);
                foreach (var proof in proofs)
                {
                    foreach (var owner in state.function.Blocks)
                        for (var at = 0; at < owner.Statements.Count; at++)
                            if (ReferenceEquals(owner.Statements[at], proof.Copy)) owner.Statements[at] = new Nop(proof.Copy.Address, "共享泛型实参副本");
                            else if (ReferenceEquals(owner.Statements[at], proof.Argument)) owner.Statements[at] = proof.Argument with { Value = proof.Value };
                    var branch = (Branch)proof.Head.Statements[^1];
                    var next = proof.Head.NormalSuccessors.Single(b => b != proof.Reference);
                    proof.Head.Statements[^1] = new Jump(branch.Address, next.Start);
                    MachineFunction.RemoveEdge(proof.Head, proof.Reference);
                }
                i += statements.Count - 1;
                changed = true;
            }
        return changed;
    }
}
