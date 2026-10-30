using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using static Cpp2CS.Idioms.IdiomState;

namespace Cpp2CS.Idioms;

internal static class RecordPass
{
    internal static void Record(this IdiomState state, Template template, Block head, Point start, Dictionary<string, ulong> exits, Dictionary<string, object> inputs)
    {
        var env = new Dictionary<string, ulong>();
        for (var i = 0; i < 31; i++)
            if (state.ReachingBefore(head, start, Storage.Gpr(i)) is { } v && state.defs.Expand(new Use(v, 64)) is Const c)
                env[$"x{i}"] = c.Value;
        inputs["env"] = env;
        // 派生寄存器：此处持有"可放置基址 + 偏移"处读取值的寄存器（如重复使用的 klass->typeHierarchyDepth），测试按布置好的内存计算
        var derived = new Dictionary<string, object>();
        for (var i = 0; i < 31; i++)
            if (!env.ContainsKey($"x{i}") && state.ReachingBefore(head, start, Storage.Gpr(i)) is { } v && StripConversionsPass.StripConversions(state.defs.Expand(new Use(v, 64))) is Load load && SplitPass.Split(load.Address) is var (basis, offset) && basis is not Const && state.Location(basis, head, start) is { } at)
                derived[$"x{i}"] = new Dictionary<string, object>
                {
                    ["base"] = at,
                    ["offset"] = offset,
                    ["width"] = load.Width
                };
        inputs["derived"] = derived;
        inputs["block"] = head.Start;
        // 唯一前驱链：从链首到 head 只有这一条路径，沿它执行得到的寄存器值就是程序在 head 入口的值
        var path = new List<ulong>();
        for (var b = head; b.Predecessors.Distinct().Where(x => !state.removed.Contains(x)).ToArray() is [var p] && p != head && !b.IsLandingPad && !path.Contains(p.Start) && path.Count < 8; b = p)
            path.Insert(0, p.Start);
        inputs["path"] = path;
        state.Result.Instances.Add(new(template, state.function.Entry, Math.Max(start.Address, head.Start), exits, inputs));
    }
}
