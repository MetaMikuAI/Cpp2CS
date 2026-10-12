namespace Cpp2CS.Native;

public sealed record FinallyLoop(ulong Header, ulong Cleanup, ulong Continuation, long StorageOffset, string StorageType, ulong[] ProtectedCalls, ulong[] HandlerNodes);

// 仅收缩已证明的循环清理协议；普通业务处理器仍保留为未恢复。
public static class FinallyLoops
{
    public static FinallyLoop? Recover(NativeGraph graph, SsaSemantics semantics, NativeAbi abi, RuntimeProfile runtime, Action<string>? diagnose = null)
    {
        FinallyLoop? Reject(string reason) { diagnose?.Invoke("清理区域：" + reason); return null; }
        if (runtime.ManagedExceptionRtti is null) return Reject("托管异常载荷类型未确认");
        var loops = new NaturalLoops(graph);
        if (!loops.Reducible || loops.Loops.Length != 1) return Reject("需要单个可归约循环");
        var loop = loops.Loops[0];
        var flow = semantics.Program.Flow;
        if (flow.Problems.Length != 0 || semantics.Program.Problems.Length != 0) return null;
        var nodes = flow.Nodes.ToDictionary(n => n.Instruction.Address);
        var calls = semantics.Calls().ToDictionary(c => c.Address);
        var normal = graph.Blocks.Values.SelectMany(b => b.Instructions).Select(i => i.Address).ToHashSet();
        bool Terminal(ulong address) => graph.Blocks[address].Successors.Length == 0 && graph.Blocks[address].Instructions.Last() is { Mnemonic: "bl" } i && runtime.NoReturn(NativeGraph.Target(i));
        var exits = loop.Nodes.SelectMany(n => graph.Blocks[n].Successors).Where(n => !loop.Nodes.Contains(n)).Distinct().ToArray();
        var ordinary = exits.Where(n => !Terminal(n)).ToArray();
        if (ordinary.Length != 1) return Reject("普通出口不唯一");
        var exitCalls = graph.Blocks[ordinary[0]].Instructions.Where(i => calls.ContainsKey(i.Address)).ToArray();
        if (exitCalls.Length == 0 || calls[exitCalls[0].Address] is not { Kind: "managed", ReturnType: "void" } cleanup) return Reject("普通出口没有唯一清理调用");
        var effects = semantics.CallStorage(cleanup.Value);
        if (effects is not [{ Kind: "mutable-receiver" } effect] || SsaSemantics.AddressParts(effect.Address) is not { Root.Kind: "stack" } storage) return Reject("清理接收者不是唯一值类型栈存储");
        var type = effect.Value.Type!;
        var instructionValues = semantics.Program.Instructions.ToDictionary(i => i.Address);
        bool SafeSetup(SemanticTerm value) => value.Kind is "metadata" or "metadata-slot" or "stack" or "constant" || value.Kind == "address" && SafeSetup(value.Inputs[0]);
        if (graph.Blocks[ordinary[0]].Instructions.TakeWhile(i => i.Address != cleanup.Address)
            .Any(i => instructionValues[i.Address].Effects.Any(e => !SafeSetup(semantics.Resolve(e))))) return Reject("清理调用前存在额外效果或可抛出的读取");
        if (!abi.Managed.Implements(semantics.TargetMethod(cleanup.Value)!.Name.Split("$$")[0], "System.IDisposable") ||
            !cleanup.Name.EndsWith("$$Dispose") || cleanup.Arguments.Length != 2) return Reject("未证明 IDisposable 合约");
        var protectedPcs = loop.Nodes.Concat(exits.Where(Terminal)).SelectMany(n => graph.Blocks[n].Instructions).Select(i => i.Address).ToHashSet();
        var protectedCalls = calls.Values.Where(c => protectedPcs.Contains(c.Address)).ToArray();
        if (protectedCalls.Length == 0) return null;
        if (protectedCalls.Any(c => c.Arguments.Where(a => SsaSemantics.AddressParts(a).Root.Kind == "stack").Any(a => a.Key != effect.Address.Key)))
            return Reject("循环内存在其他栈地址参数");
        var pads = new HashSet<ulong>();
        foreach (var call in protectedCalls)
        {
            var edges = nodes[call.Address].Edges.Where(e => e.Kind.StartsWith("exception-")).ToArray();
            if (edges.Length != 1 || edges[0].Target is not { } pad || edges[0].Region is not { } region ||
                !region.Actions.Any(a => a.Kind == "cleanup") ||
                region.Actions.Any(a => a.Kind != "cleanup" && (a.Kind != "typed-catch" || a.TypeInfo != runtime.ManagedExceptionRtti))) return Reject($"0x{call.Address:x} 的异常出口不匹配托管清理协议");
            pads.Add(pad);
        }
        if (nodes.Values.Where(n => normal.Contains(n.Instruction.Address) && !protectedPcs.Contains(n.Instruction.Address))
            .Any(n => n.Edges.Any(e => e.Kind.StartsWith("exception-") && e.Target is not null))) return Reject("存在未覆盖的普通业务处理区");
        var continuation = cleanup.Address + 4;
        bool SameCleanup(SsaManagedCall call) => call.Name == cleanup.Name && call.Arguments.Select(a => a.Key).SequenceEqual(cleanup.Arguments.Select(a => a.Key));
        bool ExceptionSource(SemanticTerm value) => value.Kind == "phi" ? value.Inputs.All(ExceptionSource) : value.Kind == "exception" &&
            protectedCalls.Any(c => value.Name == $"exception_{c.Address:x}");
        var catches = calls.Values.Where(c => c.Kind == "runtime" && c.Name == "CxxBeginCatch" && c.Arguments.Length == 1 && ExceptionSource(c.Arguments[0])).Select(c => c.Value).ToHashSet();
        bool Payload(SemanticTerm value) => value is { Kind: "load", Width: 64, Inputs: [{ Kind: "call-result" } producer] } && catches.Contains(producer.Name);
        bool Rethrown(SemanticTerm value) => Payload(value) || value.Kind == "phi" && value.Inputs.Any(Payload) && value.Inputs.All(v => Payload(v) || v is { Kind: "constant", Offset: 0 });
        var visited = new HashSet<(ulong Pc, int Count)>();
        var pending = new Stack<(ulong Pc, int Count)>();
        foreach (var pad in pads) pending.Push((pad, 0));
        var writes = semantics.Stores().Select(s => s.Address).ToHashSet();
        var completed = false;
        while (pending.TryPop(out var item))
        {
            if (!visited.Add(item)) continue;
            if (item.Pc == continuation) { if (item.Count != 1) return Reject("继续执行前未清理一次"); continue; }
            if (normal.Contains(item.Pc) || !nodes.TryGetValue(item.Pc, out var node) || writes.Contains(item.Pc)) return Reject($"0x{item.Pc:x} 处理器含存储或越出区域");
            var count = item.Count;
            if (calls.TryGetValue(item.Pc, out var call))
            {
                if (SameCleanup(call)) { if (++count != 1) return Reject("重复清理"); }
                else if (call.Kind != "runtime" || call.Name is not ("CxxBeginCatch" or "CxxEndCatch" or "RethrowException" or "UnwindResume")) return Reject($"0x{call.Address:x} 处理器含未解释调用");
                if (call.Name is "RethrowException" or "UnwindResume")
                {
                    if (count != 1 || call.Name == "RethrowException" && (call.Arguments.Length != 1 || !Rethrown(call.Arguments[0]))) return Reject("异常出口未保留原异常或清理次数不匹配");
                    if (call.Name == "UnwindResume" && (call.Arguments.Length != 1 || !Unwound(call.Arguments[0]))) return Reject("展开出口未保留原异常载荷");
                    completed = true; continue;
                }
                if (call.Name == "CxxBeginCatch" && !catches.Contains(call.Value)) return Reject("捕获入口不是受保护调用的异常");
                foreach (var edge in node.Edges)
                {
                    if (edge.Kind.StartsWith("exception-"))
                    {
                        if (SameCleanup(call) || call.Name == "CxxBeginCatch") continue;
                        if (edge.Target is null) return null;
                    }
                    if (edge.Target is { } target) pending.Push((target, count));
                    else return null;
                }
            }
            else
            {
                if (node.Edges.Length == 0) return null;
                foreach (var edge in node.Edges)
                    if (edge.Target is { } target)
                    {
                        if (target == continuation)
                        {
                            var condition = instructionValues[item.Pc].Condition;
                            if (condition is null || semantics.Resolve(condition) is not { Kind: "zero", Inputs: [var payload] } || !Payload(payload) || edge.Kind != "taken")
                                return Reject("异常路径的继续执行出口不是空载荷保护");
                        }
                        pending.Push((target, count));
                    }
                    else return null;
            }
        }
        var handler = visited.Select(v => v.Pc).Where(pc => pc != continuation).Distinct().ToHashSet();
        var degrees = handler.ToDictionary(pc => pc, _ => 0);
        foreach (var pc in handler) foreach (var edge in nodes[pc].Edges.Where(e => e.Target is { } t && handler.Contains(t))) degrees[edge.Target!.Value]++;
        var ready = new Queue<ulong>(degrees.Where(p => p.Value == 0).Select(p => p.Key));
        var ordered = 0;
        while (ready.TryDequeue(out var pc)) { ordered++; foreach (var edge in nodes[pc].Edges.Where(e => e.Target is { } t && handler.Contains(t))) if (--degrees[edge.Target!.Value] == 0) ready.Enqueue(edge.Target.Value); }
        if (ordered != handler.Count) return Reject("异常清理处理器含循环");
        return completed ? new(loop.Header, cleanup.Address, continuation, storage.Offset, type,
            protectedCalls.Select(c => c.Address).ToArray(), handler.ToArray()) : null;
        bool Unwound(SemanticTerm value) => value.Kind == "phi" ? value.Inputs.All(Unwound) : ExceptionSource(value) || value.Kind == "exception" &&
            calls.Values.Any(c => c.Kind == "runtime" && c.Name == "CxxEndCatch" && value.Name == $"exception_{c.Address:x}");
    }
}
