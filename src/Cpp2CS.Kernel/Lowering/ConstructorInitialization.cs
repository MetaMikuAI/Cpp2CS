using Cpp2CS.Kernel.Facts;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;

namespace Cpp2CS.Kernel;

/// <summary>引用类型实例构造函数的 this 初始化（ECMA-335 III.1.8.1.4，设计 9.3）。</summary>
internal static class ConstructorInitialization
{
    // 单条路径上只区分零次、一次与多次。合流取并集，保留冲突中是否含有未初始化的路径。
    [Flags]
    private enum Count : byte { None = 0, Zero = 1, One = 2, Many = 4 }

    internal static string? Check(EffectGraph graph, IEntityMetadata metadata, IReadOnlyList<Certificate> selected)
    {
        var host = graph.Host;
        if (!host.HasThis || metadata.IsInstanceConstructor(host.Entity) != true || metadata.IsValueType(host.DeclaringType) == true
            || host.DeclaringType == metadata.SystemObject) return null;

        var snapshot = graph.Snapshot;
        var receiver = CallLegality.HostThis(snapshot, host);
        var uses = selected.GroupBy(c => c.Claim.Landing).OrderBy(g => g.Key.Index)
            .SelectMany(g => Selection.Order([.. g]) ?? throw new InvalidOperationException("同一落点的凭据次序冲突"))
            .Where(c => receiver != null && c.Claim.Operands.Contains(receiver))
            .ToLookup(c => c.Claim.Landing.Block);
        var inputs = new Count[snapshot.BlockCount];
        var pending = new Queue<BlockId>();
        inputs[snapshot.Entry.Index] = Count.Zero;
        pending.Enqueue(snapshot.Entry);
        while (pending.TryDequeue(out var block))
        {
            var state = inputs[block.Index];
            foreach (var certificate in uses[block])
            {
                var claim = certificate.Claim;
                string il = OperationCatalog.Get(claim.Operation).Il;
                bool onThis = claim.Operands[0] == receiver;
                bool initializes = onThis && il == "call" && claim.Entity is { } method && metadata.IsInstanceConstructor(method) == true;
                if ((state & Count.Zero) != 0)
                {
                    bool ownField = onThis && il == "stfld" && claim.Entity is { } field && metadata.Field(field).DeclaringType == host.DeclaringType;
                    if ((!initializes && !ownField) || claim.Operands.Skip(1).Contains(receiver))
                        return $"第 4 条：{claim.Landing} 的 {claim.Operation} 在初始化之前使用 this";
                }
                if (initializes)
                {
                    var next = (state & Count.Zero) != 0 ? Count.One : Count.None;
                    if ((state & (Count.One | Count.Many)) != 0) next |= Count.Many;
                    state = next;
                }
            }

            var exits = snapshot.Terminator(block).Exits;
            for (int i = 0; i < exits.Length; i++)
            {
                var exit = exits[i];
                if (exit.Kind == ExitKind.Return && !graph.EndsInThrow(block) && state != Count.One)
                    return $"第 3 条：{new ProgramPoint(block, snapshot.OccurrenceCount(block))} 的返回路径上没有恰好一次 this 初始化";
                if (exit.Kind != ExitKind.Target || !graph.Live(new(block, i))) continue;
                int target = exit.Target.Index;
                var joined = inputs[target] | state;
                if (joined == inputs[target]) continue;
                inputs[target] = joined;
                pending.Enqueue(exit.Target);
            }
        }
        return null;
    }
}
