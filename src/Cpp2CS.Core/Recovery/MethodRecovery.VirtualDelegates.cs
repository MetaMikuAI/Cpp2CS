using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private sealed record VirtualDelegate(Expr Receiver, int Slot, HashSet<Variable> Metadata);
        private readonly Dictionary<Call, VirtualDelegate> virtualDelegates = new(ReferenceEqualityComparer.Instance);

        private void MarkVirtualDelegateLoads()
        {
            var statements = blocks.SelectMany(b => b.Statements).ToArray();
            var users = statements.SelectMany(s => ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>()
                .Select(u => (u.Variable, Statement: s))).ToLookup(p => p.Variable, p => p.Statement);
            foreach (var call in statements.OfType<Call>())
            {
                if (call is not { Op: null, Kind: CallKind.Direct, Target: Const entry }
                    || !facts.EntriesAt(entry.Value).Any(e => e.Method is { Method: { Name: ".ctor", IsStatic: false } } m
                        && DelegateFacts.IsDelegate(m.DeclaringType))) continue;
                var registers = ArgumentsOf(call);
                if (!registers.TryGetValue(Storage.Gpr(1), out var receiver)
                    || !registers.TryGetValue(Storage.Gpr(2), out var identity)
                    || identity is not Use { Width: 64 } methodInfo || !values.TryGetValue(methodInfo.Variable, out var methodLoad)
                    || methodLoad is not Load { Width: 64, Address: Binary { Op: BinOp.Add, Left: Use { Width: 64 } klass, Right: Const offset } }
                    || !values.TryGetValue(klass.Variable, out var classLoad)
                    || classLoad is not Load { Width: 64, Address: var instance } || instance != receiver) continue;
                var start = (ulong)RuntimeLayout.VtableMethodInfo(0);
                if (offset.Value < start || (offset.Value - start) % RuntimeLayout.VirtualInvokeDataSize != 0
                    || (offset.Value - start) / RuntimeLayout.VirtualInvokeDataSize > int.MaxValue) continue;
                HashSet<Variable> metadata = [klass.Variable, methodInfo.Variable];
                // 运行时指针只服务于此查询；任意额外使用不能借此删除。
                if (metadata.Any(v => phis.Values.Any(p => p.Sources.Contains(v))
                    || users[v].Any(s => s is Define d ? !metadata.Contains(d.Target) : !ReferenceEquals(s, call)))) continue;
                virtualDelegates[call] = new(receiver, (int)((offset.Value - start) / RuntimeLayout.VirtualInvokeDataSize), metadata);
                runtime.UnionWith(metadata);
            }
        }

        private MethodRef? VirtualDelegateMethod(VirtualDelegate lookup)
        {
            if (TypeOfValue(lookup.Receiver) is not DefinitionRef receiver || receiver.Definition.IsValueType
                || lookup.Slot >= receiver.Definition.VTable.Count || receiver.Definition.VTable[lookup.Slot] is not { } entry
                || entry.Method.IsStatic || !entry.Method.IsVirtual || entry.Method.GenericParameters.Count != 0) return null;
            return Instantiation(receiver, entry.Method.Owner) is { } arguments ? entry with { TypeArguments = arguments } : null;
        }
    }
}
