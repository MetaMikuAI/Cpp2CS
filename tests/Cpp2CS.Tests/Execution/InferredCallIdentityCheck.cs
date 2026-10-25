using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests.Execution;

internal static class InferredCallIdentityCheck
{
    [Command("owner-runtime", "F8 独立运行时身份核对的正负测试", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var index = new WorldIndex(facts, new ManagedTypes(facts.Model, facts.Layouts));
        var a = new Assertions();
        // 测试输入来自全局元数据槽，既不读取被测函数机器码，也不从正见证实例名单挑指针。
        var slots = facts.Usages.Slots.Values.Where(s => s.Usage.Value is MethodRef m && UnregisteredMethods.IsClosed(m))
            .Select(s => (Slot: s, Method: (MethodRef)s.Usage.Value)).ToLookup(s => s.Method.Method);
        var tested = 0;
        var definitions = new HashSet<MethodDef>();
        var groups = facts.Unregistered.All.OrderBy(d => d.Address).GroupBy(d => d.Definition).ToArray();
        var eligible = groups.Where(g => slots[g.Key].Where(s => index.Abi.Classify(s.Method, out _) is { } sig
            && UnregisteredMethods.Shape(sig) == UnregisteredMethods.Shape(g.First().Abi)).Select(s => s.Method).Distinct().Take(2).Count() == 2).Select(g => g.Key).ToHashSet();
        // 每个可提供双槽的定义选取一个入口。
        foreach (var identity in groups.Select(g => g.First()))
        {
            var pair = slots[identity.Definition].Where(s => index.Abi.Classify(s.Method, out _) is { } sig
                && UnregisteredMethods.Shape(sig) == UnregisteredMethods.Shape(identity.Abi)).DistinctBy(s => s.Method).Take(2).ToArray();
            if (pair.Length < 2) continue;
            var world = new World(index, 0, new Hints([], []), null);
            var first = world.SlotValue(pair[0].Slot.Usage);
            var second = world.SlotValue(pair[1].Slot.Usage);
            a.Equal(pair[0].Method, InferredCallIdentity.Resolve(world, identity, first, pair[0].Method), "实际槽位映射决定实例");
            a.Equal(pair[1].Method, InferredCallIdentity.Resolve(world, identity, second, pair[1].Method), "同定义的另一个实例独立接受");
            Reject(() => InferredCallIdentity.Resolve(world, identity, first, pair[1].Method), "同定义错误实例必须报错");
            Reject(() => InferredCallIdentity.Resolve(world, identity, 0, pair[0].Method), "零指针必须报错");
            Reject(() => InferredCallIdentity.Resolve(world, identity, World.RuntimeBase + 1, pair[0].Method), "未知指针必须报错");
            Reject(() => InferredCallIdentity.Resolve(world, identity, first, null), "CIL 没有对应调用必须报错");
            var wrong = facts.Model.Methods.First(m => m != identity.Definition && m.IsStatic && m.GenericParameters.Count == 0 && m.Owner.GenericParameters.Count == 0);
            var wrongRef = new MethodRef(wrong, [], []);
            Reject(() => InferredCallIdentity.Resolve(world, identity, world.MethodInfo(wrongRef), wrongRef), "不同定义即使与 CIL 相同也必须报错");
            // 删掉全部 A 实例证据后结果必须不变，防止桩身份偷偷回退到 L1 候选。
            a.Equal(pair[1].Method, InferredCallIdentity.Resolve(world, identity with { Witnesses = [] }, second, pair[1].Method), "运行时身份不依赖 L1 实例见证");
            if (identity.Definition.GenericParameters.Count > 0 || identity.Definition.Owner.GenericParameters.Count > 0)
            {
                var open = new MethodRef(identity.Definition, [], []);
                Reject(() => InferredCallIdentity.Resolve(world, identity, world.MethodInfo(open), open), "开放实例即使与 CIL 相同也必须报错");
            }
            definitions.Add(identity.Definition);
            tested++;
        }
        a.True(tested > 0, "输入中存在可检查的多实例槽位");
        a.True(definitions.SetEquals(eligible), "覆盖输入中的全部双槽定义");
        Console.WriteLine($"双槽定义 {definitions.Count}，入口 {tested}");
        return a.Finish("owner-runtime");

        void Reject(Action action, string message)
        {
            var rejected = false;
            try { action(); } catch (InferredCallError) { rejected = true; }
            a.True(rejected, message);
        }
    }
}
