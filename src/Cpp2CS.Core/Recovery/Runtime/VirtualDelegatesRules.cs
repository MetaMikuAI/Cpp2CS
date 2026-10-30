using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal static class VirtualDelegatesRules
{
    internal static void MarkVirtualDelegateLoads(this RecoveryScope ctx)
    {
        var statements = ctx.blocks.SelectMany(b => b.Statements).ToArray();
        var users = new UseIndex(statements.Where(s => s is not Phi));
        foreach (var call in statements.OfType<Call>())
        {
            if (call is not { Op: null, Kind: CallKind.Direct, Target: Const entry } || !ctx.facts.EntriesAt(entry.Value).Any(e => e.Method is { Method: { Name: ".ctor", IsStatic: false } } m && DelegateFacts.IsDelegate(m.DeclaringType)))
                continue;
            var registers = CallResolution.ArgumentsOf(call);
            if (!registers.TryGetValue(Storage.Gpr(1), out var receiver) || !registers.TryGetValue(Storage.Gpr(2), out var identity) || identity is not Use { Width: 64 } methodInfo || !ctx.values.TryGetValue(methodInfo.Variable, out var methodLoad) || methodLoad is not Load { Width: 64, Address: Binary { Op: BinOp.Add, Left: Use { Width: 64 } klass, Right: Const offset } } || !ctx.values.TryGetValue(klass.Variable, out var classLoad) || classLoad is not Load { Width: 64, Address: var instance } || instance != receiver)
                continue;
            var start = (ulong)RuntimeLayout.VtableMethodInfo(0);
            if (offset.Value < start || (offset.Value - start) % RuntimeLayout.VirtualInvokeDataSize != 0 || (offset.Value - start) / RuntimeLayout.VirtualInvokeDataSize > int.MaxValue)
                continue;
            HashSet<Variable> metadata = [klass.Variable, methodInfo.Variable];
            // 运行时指针只服务于此查询；任意额外使用不能借此删除。
            if (metadata.Any(v => ctx.phis.Values.Any(p => p.Sources.Contains(v)) || users[v].Any(s => s is Define d ? !metadata.Contains(d.Target) : !ReferenceEquals(s, call))))
                continue;
            ctx.State.Calls.virtualDelegates[call] = new(receiver, (int)((offset.Value - start) / RuntimeLayout.VirtualInvokeDataSize), metadata);
            ctx.State.Runtime.runtime.UnionWith(metadata);
        }
    }

    internal static MethodRef? VirtualDelegateMethod(this RecoveryScope ctx, VirtualDelegate lookup)
    {
        if (ctx.TypeOfValue(lookup.Receiver) is not DefinitionRef receiver || receiver.Definition.IsValueType || lookup.Slot >= receiver.Definition.VTable.Count || receiver.Definition.VTable[lookup.Slot] is not { } entry || entry.Method.IsStatic || !entry.Method.IsVirtual || entry.Method.GenericParameters.Count != 0)
            return null;
        return CallResolution.Instantiation(receiver, entry.Method.Owner) is { } arguments ? entry with
        {
            TypeArguments = arguments
        }

        : null;
    }
}
