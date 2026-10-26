using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private readonly Dictionary<ulong, LocalValue> mergedBoxValues = [];
        private readonly Dictionary<Store, LocalValue> boxArgumentStores = [];

        /// <summary>标量写进临时栈槽后跨块装箱：在原写入处保存值，不把栈地址当托管值。</summary>
        [Analysis("汇合装箱", 23, After = ["标量栈实参"])]
        private void PrepareMergedBoxArguments()
        {
            var changed = false;
            foreach (var block in blocks)
            foreach (var call in block.Statements.OfType<Call>().ToArray())
            {
                if (call is not { Op: { Kind: OpKind.Box, Operand: TypeRef type }, Arguments: [_, var data] }
                    || types.Kind(type) is not (TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double)) continue;
                var width = types.Size(type) * 8;
                Store?[] sources;
                if (FrameOffset(data) is { } directOffset)
                    sources = [ReachingStackStore(block, block.Statements.IndexOf(call), directOffset, [], width)];
                else if (data is Use pointer && phis.TryGetValue(pointer.Variable, out var phi) && block.Statements.Contains(phi)
                    && phi.Sources.Length == block.Predecessors.Count)
                {
                    if (block.Statements.Take(block.Statements.IndexOf(call)).Any(s => s is Store or Call)) continue;
                    if (blocks.SelectMany(b => b.Statements).Where(s => s != call && s != phi)
                        .Any(s => s is Phi other && other.Sources.Contains(phi.Target)
                            || ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => u.Variable == phi.Target))) continue;
                    sources = phi.Sources.Select((source, i) => FrameOffset(new Use(source, 64)) is { } offset
                        ? ReachingStackStore(block.Predecessors[i], block.Predecessors[i].Statements.Count, offset, [], width) : null).ToArray();
                }
                else continue;
                if (sources.Any(s => s is null || boxArgumentStores.ContainsKey(s))) continue;
                // 栈槽只能由这些写入和地址定义访问；普通加载或其他调用继续交给帧区域恢复。
                var offsets = sources.Select(s => FrameOffset(s!.Target)!.Value).ToHashSet();
                if (blocks.SelectMany(b => b.Statements).SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).OfType<Load>()
                    .Any(load => FrameOffset(load.Address) is { } at && offsets.Any(offset => at < offset + width / 8 && offset < at + load.Width / 8))) continue;
                if (blocks.SelectMany(b => b.Statements).Where(s => s != call && s is not (Define or Phi) && !sources.Contains(s))
                    .SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk)
                    .Any(e => FrameOffset(e) is { } offset && offsets.Contains(offset))) continue;
                var local = StructLocal(type, width);
                foreach (var store in sources) boxArgumentStores[store!] = local;
                mergedBoxValues[call.Address] = local;
                var replacement = call with { Arguments = [call.Arguments[0], Expr.C(0, 64)] };
                block.Statements[block.Statements.IndexOf(call)] = replacement;
                ledger.Replace(call, replacement);
                changed = true;
            }
            if (!changed) return;
            RemoveDeadDefinitions();
            definitions = IndexDefinitions();
        }

        [StoreRule(2)]
        private bool StoreBoxArgument(Store store, List<ManagedStatement> output)
        {
            if (!boxArgumentStores.TryGetValue(store, out var local)) return false;
            output.Add(new ManagedAssignment(store.Address, local, RecoverAs(store.Value, local.Type, store.Address)));
            return true;
        }

        [CallRule(9)]
        private bool BoxMergedArgument(Call call, List<ManagedStatement> output)
        {
            if (!mergedBoxValues.TryGetValue(call.Address, out var local) || call.Defines.FirstOrDefault() is not { } result) return false;
            output.Add(new ManagedAssignment(call.Address, Local(result), new BoxValue(local, local.Type, types.Object)));
            return true;
        }
    }
}
