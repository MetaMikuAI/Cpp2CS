using Cpp2CS.Recovery.Analysis;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        /// <summary>完整值类型的定长复制先保存源值，再写入目标，保留 memmove 的重叠语义。</summary>
        [CallRule(22)]
        private RecoveryResult<bool> CopyStructValue(Call call, List<ManagedStatement> output)
        {
            if (call is not { Kind: CallKind.Direct, Op: { Kind: OpKind.Import, Operand: "memcpy" or "memmove" },
                    Arguments: [var destination, var source, Const { Value: > 0 and <= 4096 } count] }
                || TypeOfAddressBase(AddressExpression(source)) is not ByRefRef reference
                || types.Kind(reference.Element) != TypeKind.Struct || (ulong)types.Size(reference.Element) != count.Value) return false;
            var used = blocks.SelectMany(b => b.Statements).SelectMany(s => s is Phi phi ? phi.Sources
                : ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable)).ToHashSet();
            if (call.Defines.Any(used.Contains)) return false;
            if (!StructAddress(source, reference.Element).TryGet(out var from, out _)
                || !StructAddress(destination, reference.Element).TryGet(out var to, out _)) return false;
            var snapshot = StructLocal(reference.Element, 0);
            output.Add(new ManagedAssignment(call.Address, snapshot,
                from is AddressValue sourceAddress ? sourceAddress.Target : new IndirectValue(from, reference.Element)));
            output.Add(new ManagedStore(call.Address,
                to is AddressValue targetAddress ? targetAddress.Target : new IndirectValue(to, reference.Element), snapshot));
            return true;
        }
    }
}
