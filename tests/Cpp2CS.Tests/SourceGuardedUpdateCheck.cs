using System.Reflection;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceGuardedUpdateCheck
{
    [Command("source-guarded-update", "条件字段更新的完整守卫、写入与异常边界", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var owner = new TypeDef { Index = -1, Assembly = "Tests", Namespace = "Tests", Name = "Subject", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var type = new DefinitionRef(owner, []);
        var method = new MethodRef(new MethodDef { Index = -1, Owner = owner, Name = "Acquire", Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1, ReturnType = types.Boolean }, [], []);
        var fields = new[] { "Enabled", "Marked" }.Select((name, i) => new FieldDef { Index = -1 - i, Owner = owner,
            Name = name, Type = types.Boolean, Attributes = FieldAttributes.Private, Offset = 16 + i }).ToArray();
        FieldValue Field(ManagedValue receiver, int index) => new(receiver, new(fields[index], type), types.Boolean, 8);
        ConstantValue Bit(ulong value) => new(value, types.Boolean, 8);
        ManagedBranch Branch(ulong site, ManagedValue receiver, int field, Cond condition, ulong taken, ulong fallthrough) =>
            new(site, new ComparisonValue(condition, Field(receiver, field), Bit(0), types.Boolean), new(taken, []), new(fallthrough, []));
        var self = new ArgumentValue(-1, type, 64);
        var template = new ManagedBody(method, [new(0, [Branch(0, self, 0, Cond.Eq, 3, 1)]),
            new(1, [Branch(1, self, 1, Cond.Ne, 3, 2)]), new(2, [new ManagedStore(2, Field(self, 1), Bit(1)), new ManagedReturn(2, Bit(1))]),
            new(3, [new ManagedReturn(3, Bit(0))])]);
        var a = new Assertions();
        var candidate = SourceGuardedUpdate.Create(template, types);
        a.True(candidate is { Guards.Count: 2 }, "完整条件更新方法得到两个有序守卫");
        if (candidate is null) return a.Finish("source-guarded-update");
        var receiver = new ArgumentValue(0, type, 64);
        var getter = new MethodRef(new MethodDef { Index = -2, Owner = owner, Name = "Read", Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1, ReturnType = types.Boolean }, [], []);
        var observer = new ManagedCall(12, new(method, receiver, [], false), null, false);
        foreach (var mode in new[] { "valid", "snapshot", "escaping-snapshot", "getter", "opaque-getter", "unproven-getter", "escaping-getter",
            "other-receiver", "other-value", "observer", "shared-entry", "wrong-guard", "other-failure", "other-handler" })
        {
            var second = new List<ManagedStatement>();
            if (mode == "observer") second.Add(observer);
            second.Add(Branch(11, mode == "other-receiver" ? new ArgumentValue(1, type, 64) : receiver, 1,
                mode == "wrong-guard" ? Cond.Eq : Cond.Ne, mode == "other-failure" ? 14UL : 13UL, 12));
            var snapshot = new LocalValue(new(Storage.Temp(20), 1), types.Boolean, 8);
            if (mode is "snapshot" or "escaping-snapshot")
            {
                second[0] = ((ManagedBranch)second[0]) with { Condition = new ComparisonValue(Cond.Ne, snapshot, Bit(0), types.Boolean) };
                second.Insert(0, new ManagedAssignment(11, snapshot, Field(receiver, 1)));
            }
            if (mode.Contains("getter", StringComparison.Ordinal))
            {
                second[0] = ((ManagedBranch)second[0]) with { Condition = snapshot };
                second.Insert(0, new ManagedCall(11, new(getter, receiver, [], false), snapshot, false) { Inlined = mode != "opaque-getter" });
            }
            var blocks = new List<ManagedBlock> { new(10, [Branch(10, receiver, 0, Cond.Eq, 13, 11)]), new(11, second),
                new(12, [new ManagedStore(12, Field(receiver, 1), Bit(mode == "other-value" ? 0UL : 1UL)), observer, new ManagedReturn(12, null)]),
                new(13, [new ManagedReturn(13, null)]) };
            if (mode is "escaping-snapshot" or "escaping-getter") blocks[3] = blocks[3] with { Statements = [new ManagedReturn(13, snapshot)] };
            if (mode == "shared-entry") blocks.Add(new(14, [new ManagedJump(14, new(11, []))]));
            if (mode == "other-failure") blocks.Add(new(14, [new ManagedReturn(14, null)]));
            var original = new ManagedBody(method, blocks);
            if (mode == "other-handler") original = original with { Regions = [new([10], 13, [13], null, ManagedRegionKind.Catch)] };
            var changed = candidate.Rewrite(original, types, () => new(new(Storage.Temp(-10), 1), types.Boolean, 1), (_, _) => { },
                m => m == getter && mode != "unproven-getter" ? new(fields[1], type) : null);
            a.Equal(mode is "valid" or "snapshot" or "getter", changed is not null, mode);
            if (changed is not null)
            {
                a.True(!changed.Blocks.SelectMany(b => b.Statements).OfType<ManagedStore>().Any(), "字段写入归入已证明调用");
                a.True(changed.Blocks.SelectMany(b => b.Statements).Contains(observer), "后续副作用仍在成功路径");
            }
        }
        var extra = template with { Blocks = [.. template.Blocks.Take(3), new(3, [new ManagedStore(3, Field(self, 1), Bit(0)), new ManagedReturn(3, Bit(0))])] };
        a.True(SourceGuardedUpdate.Create(extra, types) is null, "失败路径有写入时不视为条件更新");
        var wrongReturn = template with { Blocks = [.. template.Blocks.Take(2), new(2, [new ManagedStore(2, Field(self, 1), Bit(1)), new ManagedReturn(2, Bit(0))]), template.Blocks[3]] };
        a.True(SourceGuardedUpdate.Create(wrongReturn, types) is null, "写入后返回false不匹配成功标记");
        return a.Finish("source-guarded-update");
    }
}
