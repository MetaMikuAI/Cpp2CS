using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private readonly HashSet<Call> genericResolvers = new(ReferenceEqualityComparer.Instance);

        /// <summary>泛型虚调用的类、虚表与实例化方法指针只承担分派；托管 callvirt 保留接收者和方法实参。</summary>
        private void MarkGenericVirtualLoads()
        {
            foreach (var call in blocks.SelectMany(b => b.Statements).OfType<Call>())
            {
                if (call.Op is not { Kind: OpKind.CallGenericVirtual, Operand: MethodRef generic }
                    || call.Target is not Use pointer || !values.TryGetValue(pointer.Variable, out var pointerValue)
                    || pointerValue is not Load { Width: 64, Address: Binary { Op: BinOp.Add, Left: Use info, Right: Const pointerOffset } }
                    || pointerOffset.Value != RuntimeLayout.MethodVirtualPointer
                    || !results.TryGetValue(info.Variable, out var result)
                    || result.Call is not { Op: { Kind: OpKind.ResolveGenericVirtual, Operand: MethodRef resolved }, Arguments: [Use entry, _] } resolver
                    || !resolved.Equals(generic) || !values.TryGetValue(entry.Variable, out var entryValue)
                    || entryValue is not Load { Width: 64, Address: Binary { Op: BinOp.Add, Left: Use klass, Right: Const slotOffset } }
                    || slotOffset.Value != (ulong)RuntimeLayout.VtableMethodInfo(generic.Method.Slot)
                    || !values.TryGetValue(klass.Variable, out var klassValue)
                    || klassValue is not Load { Width: 64, Address: var receiver }
                    || call.Arguments.Length == 0 || Expand(receiver) != Expand(call.Arguments[0])) continue;
                genericResolvers.Add(resolver);
                runtime.UnionWith([pointer.Variable, info.Variable, entry.Variable, klass.Variable]);
            }
        }
    }
}
