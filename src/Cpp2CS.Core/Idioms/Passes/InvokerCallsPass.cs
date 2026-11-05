using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery;
using Cpp2CS.Recovery.Calls;

namespace Cpp2CS.Idioms;

/// <summary>
/// MethodInfo.invoker_method 的参数数组拆为独立实参，保留值参数与返回值的存储地址；数组槽的内容由帧内存转发。
/// 完全共享代码只能经 invoker 调用签名含可变大小值的方法：invoker(指针, MethodInfo, 接收者, 参数数组, 返回存储)。
/// MethodInfo 可以是元数据实体，也可以是分派查找的结果；后者的指针取 virtualMethodPointer，是一次 callvirt。
/// </summary>
internal static class InvokerCallsPass
{
    internal static bool InvokerCalls(this IdiomState state) => Run(state.function, state.defs, state.self, state.owner.abi, IsConstrainedCall(state.owner), state.Reject);

    /// <summary>路径拆分之后 MethodInfo 才成为单一实体的调用；规则与 L2 相同，实体已代入当前实例。</summary>
    internal static void AfterSplitting(MachineFunction function, MethodRef self, IdiomRewriter rewriter)
    {
        while (Run(function, new IdiomRewriter.Defs(function), self, rewriter.abi, IsConstrainedCall(rewriter), null)) { }
    }

    private static Func<Call, bool> IsConstrainedCall(IdiomRewriter owner) => call => owner.HelperOf(call)?.Kind == HelperKind.ConstrainedCall;

    private static bool Run(MachineFunction function, IdiomRewriter.Defs defs, MethodRef? self, ManagedAbi abi, Func<Call, bool> isConstrained, Action<string, ulong, string>? reject)
    {
        Dictionary<Variable, Call>? lookups = null;
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call { Op: null } call) continue;
                Expr? Actual(int register) => call.ArgumentIndex(Storage.Gpr(register)) is var index && index >= 0 ? call.Arguments[index] : null;
                Expr? Input(int register) => Actual(register) is { } input ? defs.Expand(input) : null;
                Call? replacement = null;
                if (call.Kind == CallKind.Direct)
                {
                    // il2cpp_codegen_runtime_constrained_call(klass, 约束项, boxBuffer, objBuffer, args, ret)；boxBuffer 只服务于运行时的装箱路径。
                    if (!isConstrained(call) || Input(1) is not Symbol { Kind: SymbolKind.Constrained, Value: ValueTuple<TypeRef, MethodRef> constrained }
                        || Input(0) is not Symbol { Kind: SymbolKind.Class, Value: TypeRef klass } || !klass.Equals(constrained.Item1)
                        || Actual(3) is not { } location || Actual(4) is not { } slots || Actual(5) is not { } buffer) continue;
                    var signature = abi.ConstrainedInvoker(self is not null ? (TypeRef)GenericContext.Instantiate(constrained.Item1, self)! : constrained.Item1,
                        self is not null ? (MethodRef)GenericContext.Instantiate(constrained.Item2, self)! : constrained.Item2);
                    if (Unsized(signature))
                    {
                        reject?.Invoke("invoker.signature", call.Address, "按址实参的大小未知");
                        continue;
                    }
                    replacement = Unpacked(call, new(OpKind.InvokeConstrainedGeneric, constrained), constrained.Item2, location, slots, buffer);
                }
                else if (call.Kind == CallKind.Indirect && defs.Expand(call.Target) is Load { Width: 64 } target
                    && SplitPass.Split(target.Address) is (var info, RuntimeLayout.MethodInvoker)
                    && Input(1) == info && Input(2) is { } receiver && Actual(3) is { } arguments && Actual(4) is { } output)
                {
                    MethodRef? method;
                    var dispatched = false;
                    if (info is Symbol { Kind: SymbolKind.Method, Value: MethodRef direct })
                    {
                        if (Input(0) != new Load(info, 64)) continue;
                        method = direct;
                    }
                    else
                    {
                        if (Input(0) != new Load(Offset(info, RuntimeLayout.MethodVirtualPointer), 64)) continue;
                        lookups ??= function.Blocks.SelectMany(b => b.Statements).OfType<Call>()
                            .Where(c => c.Op?.Kind is OpKind.InterfaceInvokeData or OpKind.ResolveGenericVirtual && c.Defines.Length > 0 && c.Defines[0] is not null)
                            .ToDictionary(c => c.Defines[0]);
                        method = Dispatched(info, receiver, defs, lookups);
                        dispatched = true;
                        if (method is null) continue;
                    }
                    if (Unsized(abi.Invoker(self is not null ? (MethodRef)GenericContext.Instantiate(method, self)! : method)))
                    {
                        reject?.Invoke("invoker.signature", call.Address, "按址实参的大小未知");
                        continue;
                    }
                    replacement = Unpacked(call, new(dispatched ? OpKind.InvokeVirtualGeneric : OpKind.InvokeGeneric, method), method, Actual(2)!, arguments, output);
                }
                if (replacement is null) continue;
                var statements = new List<Stmt> { replacement };
                // invoker 自身返回 void，原保守 clobber 不能冒充目标方法的返回寄存器。
                statements.AddRange(call.Defines.OfType<Variable>().Select(v => new Define(call.Address, v, new Unknown("invoker 未定义返回寄存器", v.Width))));
                block.Statements.RemoveAt(i);
                block.Statements.InsertRange(i, statements);
                return true;
            }
        return false;
    }

    private static bool Unsized(MachineSignature signature) => signature.Indirections.Any(a => a.Size <= 0 && !ManagedAbi.SharedValue(a.Type is ByRefRef byRef ? byRef.Element : a.Type));

    /// <summary>参数数组拆成逐槽读取；结果写入返回存储，方法实体占 MethodInfo 的位置。</summary>
    private static Call Unpacked(Call call, RuntimeOp op, MethodRef method, Expr receiver, Expr arguments, Expr output)
    {
        var entity = new Symbol(SymbolKind.Method, method);
        var inputs = new List<Expr>();
        if (!method.Method.IsStatic) inputs.Add(receiver);
        for (var parameter = 0; parameter < method.Method.Parameters.Count; parameter++)
            inputs.Add(new Load(Offset(arguments, parameter * 8), 64));
        inputs.Add(entity);
        if (!ManagedTypes.IsVoid(method.Method.ReturnType)) inputs.Add(output);
        return call with
        {
            Op = op,
            Target = entity,
            Arguments = inputs.ToArray(),
            Sources = Enumerable.Range(0, inputs.Count).Select(Storage.Gpr).ToArray(),
            Results = [],
            Defines = [],
            StackPointer = null,
        };
    }

    /// <summary>
    /// 分派查找得到的方法：接口槽 VirtualInvokeData.method，或泛型虚方法的解析结果（其声明槽来自接口查找或接收者类的虚表）。
    /// 查找的对象必须就是接收者：invoker 不重新分派，接收者换了对象就不是这次查找的方法。
    /// </summary>
    private static MethodRef? Dispatched(Expr info, Expr receiver, IdiomRewriter.Defs defs, Dictionary<Variable, Call> lookups)
    {
        Call? InterfaceLookup(Expr slot) => slot is Load { Width: 64 } load && SplitPass.Split(load.Address) is (Use data, RuntimeLayout.VirtualInvokeDataMethod)
            && lookups.TryGetValue(data.Variable, out var lookup) && lookup.Op!.Kind == OpKind.InterfaceInvokeData && defs.Expand(lookup.Arguments[0]) == receiver ? lookup : null;
        if (InterfaceLookup(info) is { Op.Operand: ValueTuple<object?, int> { Item1: DefinitionRef owner } operand })
            return DispatchResolution.Slot(owner, operand.Item2, interfaceOnly: true);
        if (info is not Use resolved || !lookups.TryGetValue(resolved.Variable, out var generic)
            || generic.Op is not { Kind: OpKind.ResolveGenericVirtual, Operand: MethodRef method }) return null;
        var declared = defs.Expand(generic.Arguments[0]);
        var fromVtable = declared is Load { Width: 64 } entry && SplitPass.Split(entry.Address) is (Load { Width: 64, Address: var klassOwner }, _) && klassOwner == receiver;
        return fromVtable || InterfaceLookup(declared) is not null ? method : null;
    }

    private static Expr Offset(Expr value, int offset) => offset == 0 ? value : Fold.Simplify(new Binary(BinOp.Add, value, Expr.C((ulong)offset, 64), 64));
}
