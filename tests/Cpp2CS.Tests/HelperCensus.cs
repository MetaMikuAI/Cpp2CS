using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Runtime;

namespace Cpp2CS.Tests;

/// <summary>
/// helpers &lt;binary&gt; &lt;metadata&gt; [命名空间,...]：统计回归集中直接调用的非托管目标，打印识别结果与依据。
/// </summary>
internal static class HelperCensus
{
    /// <summary>copydiff &lt;binary&gt; &lt;metadata&gt; 0xA 0xB：并排打印两个函数的归一化语句，标出第一处不同。</summary>
    public static int Diff(string binary, string metadata, ulong a, ulong b)
    {
        var model = ModelCheck.Load(binary, metadata);
        var functions = FunctionTable.Build(model.Image);
        var machine = Corpus.Machine(model.Image);
        var copies = new ManagedCopies(machine, functions, model);
        var left = copies.ShapeOf(a)?.Statements;
        var right = copies.ShapeOf(b)?.Statements;
        Console.WriteLine($"引用相同 {copies.ShapeOf(a)?.References == copies.ShapeOf(b)?.References}  距离 {(left is null || right is null ? -1 : ManagedCopies.EditDistance(left, right, 64))}");
        Console.WriteLine($"0x{a:x}: {functions.At(a)}  {left?.Length.ToString() ?? "null"} 条");
        Console.WriteLine($"0x{b:x}: {functions.At(b)}  {right?.Length.ToString() ?? "null"} 条");
        if (left is null || right is null) return 1;
        for (var i = 0; i < Math.Max(left.Length, right.Length); i++)
        {
            var l = i < left.Length ? left[i] : "";
            var r = i < right.Length ? right[i] : "";
            Console.WriteLine($"{(l == r ? "  " : "! ")}{l,-70} | {r}");
        }
        return 0;
    }

    /// <summary>copyfind &lt;binary&gt; &lt;metadata&gt; 0xA：列出外部引用最接近的托管方法（按引用集合差与编辑距离）。</summary>
    public static int Find(string binary, string metadata, ulong target)
    {
        var model = ModelCheck.Load(binary, metadata);
        var functions = FunctionTable.Build(model.Image);
        var machine = Corpus.Machine(model.Image);
        var copies = new ManagedCopies(machine, functions, model);
        var shape = copies.ShapeOf(target)!;
        var refs = shape.References.Split(',', ';').ToHashSet();
        Console.WriteLine($"0x{target:x} 语句 {shape.Statements.Length} 引用 {shape.References}");
        var results = new List<(int Common, int Distance, ulong Address, string Refs)>();
        foreach (var address in model.Code.Keys)
        {
            if (functions.At(address) is not { } range || range.Start != address) continue;
            var size = (long)(range.End - range.Start) - (long)(functions.At(target)!.End - target);
            if (Math.Abs(size) > 512 || copies.ShapeOf(address) is not { } other) continue;
            var common = other.References.Split(',', ';').Count(refs.Contains);
            if (common * 2 < refs.Count) continue;
            results.Add((common, ManagedCopies.EditDistance(shape.Statements, other.Statements, 200), address, other.References));
        }
        foreach (var r in results.OrderBy(r => r.Distance).Take(8))
            Console.WriteLine($"  0x{r.Address:x} 共同引用 {r.Common} 距离 {r.Distance} {Name(model, r.Address)}  {r.Refs}");
        return 0;
    }

    public static int Run(string binary, string metadata, string? selector)
    {
        var model = ModelCheck.Load(binary, metadata);
        var functions = FunctionTable.Build(model.Image);
        var machine = Corpus.Machine(model.Image);
        var builder = new CfgBuilder(machine, functions);
        var helpers = new RuntimeHelpers(builder);
        var copies = new ManagedCopies(machine, functions, model);
        var namespaces = selector?.Split(',') ?? Corpus.Default(model.Image.Architecture);
        var addresses = Corpus.Select(model, namespaces).Select(m => m.Address).Distinct().Order().ToList();
        var counts = new Dictionary<ulong, int>();
        var sample = new Dictionary<ulong, ulong>();
        int managed = 0, other = 0, indirect = 0;
        foreach (var address in addresses)
        {
            if (functions.At(address) is not { } range || range.Start != address) continue;
            var function = builder.Build(address, range);
            foreach (var call in function.Blocks.SelectMany(b => b.Statements).OfType<Call>())
            {
                if (call.Target is not Const { Value: var target })
                {
                    indirect++;
                    continue;
                }
                if (model.Code.ContainsKey(target)) managed++;
                else
                {
                    other++;
                    counts[target] = counts.GetValueOrDefault(target) + 1;
                    sample.TryAdd(target, call.Address);
                }
            }
        }
        Console.WriteLine($"直接调用托管方法 {managed}  直接调用其他 {other}（{counts.Count} 个目标）  间接调用 {indirect}");
        int identified = 0, identifiedSites = 0, copyTargets = 0, copySites = 0, ambiguousCopies = 0, nearCopies = 0, nearSites = 0;
        foreach (var (target, count) in counts.OrderByDescending(p => p.Value))
        {
            var helper = helpers.Identify(target);
            if (helper is not null)
            {
                identified++;
                identifiedSites += count;
            }
            else if (copies.Match(target) is { } copy)
            {
                copyTargets++;
                copySites += count;
                if (copy.Originals.Count > 1) ambiguousCopies++;
                if (!copy.Exact)
                {
                    nearCopies++;
                    nearSites += count;
                }
                if (count >= 20 || !copy.Exact)
                    Console.WriteLine($"  0x{target:x} {count,6}  副本(距离 {copy.Distance}) -> {string.Join(" ", copy.Originals.Take(3).Select(o => $"0x{o:x} {Name(model, o)}"))}{(copy.Originals.Count > 3 ? $" 等 {copy.Originals.Count} 个" : "")}");
                continue;
            }
            if (count < 20 && helper is not null) continue;
            var chain = builder.NoReturn.ImportName(target) is { } import ? $"导入 {import}" : string.Join(" ", helpers.Chain(target).Select(c => (c.IsCall ? "bl " : "b ") + $"0x{c.Target:x}"));
            Console.WriteLine($"  0x{target:x} {count,6}  {helper?.ToString() ?? "?",-40} {(helper is null ? $"{chain}  例 0x{sample[target]:x}" : helper.Evidence)}");
        }
        Console.WriteLine($"已识别目标 {identified}，覆盖调用 {identifiedSites}/{other}");
        Console.WriteLine($"托管副本目标 {copyTargets}（多义 {ambiguousCopies}，非精确 {nearCopies} 个/{nearSites} 处），覆盖调用 {copySites}；剩余 {other - identifiedSites - copySites}");
        return 0;
    }

    private static string Name(Model.ProgramModel model, ulong address) =>
        model.Code[address] is [var owner, ..] ? owner.Method.ToString() : "?";
}
