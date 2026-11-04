using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery;

namespace Cpp2CS.Idioms;

/// <summary>MethodInfo.invoker_method 的参数数组拆为独立实参，保留值参数与返回值的存储地址；数组槽的内容由帧内存转发。</summary>
internal static class InvokerCallsPass
{
    internal static bool InvokerCalls(this IdiomState state)
    {
        foreach (var block in state.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call { Op: null, Kind: CallKind.Indirect } call
                    || state.defs.Expand(call.Target) is not Load { Width: 64 } target
                    || SplitPass.Split(target.Address) is not (Symbol { Kind: SymbolKind.Method, Value: MethodRef method } entity, RuntimeLayout.MethodInvoker)) continue;
                Expr? Actual(int register) => call.ArgumentIndex(Storage.Gpr(register)) is var index && index >= 0 ? call.Arguments[index] : null;
                Expr? Input(int register) => Actual(register) is { } input ? state.defs.Expand(input) : null;
                if (Input(0) != new Load(entity, 64) || Input(1) != entity
                    || Input(2) is null || Actual(3) is not { } arguments || Actual(4) is not { } output) continue;
                var native = state.self is { } self ? (MethodRef)GenericContext.Instantiate(method, self)! : method;
                if (state.owner.abi.Invoker(native).Indirections.Any(a => a.Size <= 0 && !ManagedAbi.SharedValue(a.Type)))
                {
                    state.Reject("invoker.signature", call.Address, "按址实参的大小未知");
                    continue;
                }
                Expr Offset(Expr value, int offset) => offset == 0 ? value : Fold.Simplify(new Binary(BinOp.Add, value, Expr.C((ulong)offset, 64), 64));
                var inputs = new List<Expr>();
                if (!method.Method.IsStatic) inputs.Add(Actual(2)!);
                for (var parameter = 0; parameter < method.Method.Parameters.Count; parameter++)
                    inputs.Add(new Load(Offset(arguments, parameter * 8), 64));
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
                return true;
            }
        return false;
    }
}
