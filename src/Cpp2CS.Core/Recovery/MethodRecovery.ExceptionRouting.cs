using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        /// <summary>
        /// 单入口闭包可能把只属于外层的调用包进内层 try。用原生异常边标记当前捕获目标，
        /// 内层 catch 对这些调用直接 rethrow，保留外层处理路径。
        /// </summary>
        private ManagedBody RouteExceptionSources(ManagedBody body, ExceptionLayout layout, ExceptionFragment[] order)
        {
            var byEntry = layout.Regions.ToDictionary(r => r.Entry);
            var targets = layout.EntryPaths.ToDictionary(p => p.Source, p => byEntry.GetValueOrDefault(p.Entry));
            static bool Within(ExceptionRegionPlan inner, ExceptionRegionPlan outer)
            {
                for (var current = inner; current is not null; current = current.Parent)
                {
                    if (current == outer) return true;
                    if (current.ParentPart != "try") return false;
                }
                return false;
            }
            var guarded = layout.Regions.Where(r => r.Kind == "catch" && r.Try.Any(f => targets.GetValueOrDefault(f) is { } target
                && target != r && Within(r, target))).ToArray();
            if (guarded.Length == 0) return body;
            var guards = guarded.Select((r, i) => (Region: r, Flag: StructLocal(types.Boolean, 8),
                Entry: 0xf700000000000000UL + (ulong)i * 2, Reject: 0xf700000000000001UL + (ulong)i * 2)).ToArray();
            var original = body.Blocks.ToDictionary(b => b.Address);
            var updates = guarded.ToDictionary(r => r, Updates);
            Dictionary<ExceptionFragment, bool> Updates(ExceptionRegionPlan region)
            {
                var desired = new Dictionary<ExceptionFragment, bool>();
                foreach (var fragment in order.Where(region.Try.Contains))
                {
                    // 已删除的运行时操作和空桥不改变捕获路由。
                    if (original[FragmentLabel(fragment)].Statements is [ManagedJump { Edge.Copies.Count: 0 }]) continue;
                    var target = targets.GetValueOrDefault(fragment);
                    if (target is not null && !Within(target, region) && !Within(region, target))
                        throw Fail(fragment.Block.Start, "异常区域 捕获目标不在当前嵌套链");
                    desired[fragment] = target is not null ? Within(target, region) : fragment.NativeExceptionSite is null;
                }
                // 1/2 是两种已知值，4 表示从区域外进入。所有入边值相同时才省略重复赋值。
                var incoming = layout.Edges.GroupBy(e => e[1]).ToDictionary(g => g.Key, g => g.Select(e => e[0]).Distinct().ToArray());
                var states = region.Try.ToDictionary(f => f.Id, _ => 0);
                int Input(ExceptionFragment fragment) => (fragment == region.TryEntry ? 4 : 0)
                    | (incoming.GetValueOrDefault(fragment.Id) ?? []).Aggregate(0, (bits, id) => bits | states.GetValueOrDefault(id, 4));
                bool changed;
                do
                {
                    changed = false;
                    foreach (var fragment in region.Try)
                    {
                        var bits = desired.TryGetValue(fragment, out var enabled) ? enabled ? 1 : 2 : Input(fragment);
                        if (states[fragment.Id] == bits) continue;
                        states[fragment.Id] = bits;
                        changed = true;
                    }
                } while (changed);
                return desired.Where(p => Input(p.Key) != (p.Value ? 1 : 2)).ToDictionary();
            }
            var output = new List<ManagedBlock>();
            foreach (var fragment in order)
            {
                var label = FragmentLabel(fragment);
                foreach (var guard in guards.Where(g => g.Region.Entry == fragment))
                {
                    output.Add(new(guard.Entry, [new ManagedBranch(0, guard.Flag, new(label, []), new(guard.Reject, []))]));
                    output.Add(new(guard.Reject, [new ManagedRethrow(0)]));
                }
                var statements = new List<ManagedStatement>();
                foreach (var guard in guards)
                    if (updates[guard.Region].TryGetValue(fragment, out var enabled))
                        statements.Add(new ManagedAssignment(0, guard.Flag, new ConstantValue(enabled ? 1UL : 0, types.Boolean, 8)));
                statements.AddRange(original[label].Statements);
                output.Add(new(label, statements));
            }
            ulong[] IncludeGuards(IReadOnlyList<ulong> labels) => labels.SelectMany(label =>
                guards.FirstOrDefault(g => FragmentLabel(g.Region.Entry) == label) is { Region: not null } guard
                    ? new[] { guard.Entry, guard.Reject, label } : [label]).ToArray();
            return body with
            {
                Blocks = output,
                Regions = body.Regions.Select(r => r with
                {
                    Try = IncludeGuards(r.Try), Handler = IncludeGuards(r.Handler),
                    HandlerEntry = guards.FirstOrDefault(g => FragmentLabel(g.Region.Entry) == r.HandlerEntry) is { Region: not null } guard
                        ? guard.Entry : r.HandlerEntry,
                }).ToArray(),
            };
        }
    }
}
