using Cpp2CS.Facts;
using Cpp2CS.Input;

namespace Cpp2CS.Tests.Execution;

internal static class LsdaCheck
{
    [Command("eh-lsda", "独立 FDE/LSDA 全量逐项比对（facts 也运行）", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var checks = new Assertions();
        Compare(FactsBuilder.Build(binary, metadata), checks);
        return checks.Finish("eh-lsda");
    }

    public static void Compare(ProgramFacts facts, Assertions checks)
    {
        var decoded = IndependentLsda.ReadImage(facts.Model.Image).Where(t => facts.Code.RegionOf(t.Start) == CodeRegion.Managed).ToDictionary(t => t.Start);
        var expected = facts.Code.Functions.Where(f => f.Region == CodeRegion.Managed && f.ExceptionRegions.Length > 0).ToArray();
        var errors = new List<string>();
        var sites = 0; var actions = 0;
        foreach (var function in expected)
        {
            if (!decoded.TryGetValue(function.Start, out var table) || table.End != function.End || table.Sites.Length != function.ExceptionRegions.Length)
            { errors.Add($"0x{function.Start:x}: FDE 或调用点数量"); continue; }
            foreach (var (actual, core) in table.Sites.Zip(function.ExceptionRegions))
            {
                sites++;
                if (actual.Start != core.Start || actual.End != core.End || actual.Landing != core.LandingPad || actual.ActionOffset != core.ActionOffset || actual.Actions.Length != core.Actions.Length)
                { errors.Add($"0x{function.Start:x}@0x{core.Start:x}: 调用点/落地块/action"); continue; }
                foreach (var (a, b) in actual.Actions.Zip(core.Actions))
                {
                    actions++;
                    var type = b.TypeInfo is > 0 ? facts.Model.Image.ReadPointer(b.TypeInfo.Value) : b.TypeInfo;
                    if (a.Address != b.Address || a.Filter != b.Filter || a.Next != b.NextOffset || a.TypeSlot != b.TypeInfo || a.TypeInfo != type || a.Kind != b.Kind)
                        errors.Add($"0x{function.Start:x}@0x{core.Start:x} action 0x{b.Address:x}: {a} / {b}, resolved=0x{type:x}");
                }
            }
        }
        checks.True(expected.Select(f => f.Start).ToHashSet().SetEquals(decoded.Keys), "独立 FDE/LSDA 的托管函数集合一致");
        checks.Equal(0, errors.Count, $"独立 LSDA 逐项比对：{expected.Length} 函数，{sites} 调用区间，{actions} actions；{string.Join(';', errors.Take(3))}");
        Console.WriteLine($"独立 LSDA：functions={expected.Length} sites={sites} actions={actions} mismatch={errors.Count} typeEncodings={string.Join(',', decoded.Values.Select(t => $"0x{t.TypeEncoding:x}").Distinct())}");
    }
}
