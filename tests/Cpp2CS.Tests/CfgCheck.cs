using System.Diagnostics;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Images;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

/// <summary>回归集：按命名空间（精确或“X.”前缀）选出有代码地址的托管方法。</summary>
internal static class Corpus
{
    public static string RootNamespace(TypeDef type)
    {
        while (type.DeclaringType is not null) type = type.DeclaringType;
        return type.Namespace;
    }

    public static bool InNamespaces(TypeDef type, IReadOnlyList<string> namespaces)
    {
        var ns = RootNamespace(type);
        return namespaces.Any(n => ns == n || ns.StartsWith(n + ".", StringComparison.Ordinal));
    }

    public static List<MethodDef> Select(ProgramModel model, IReadOnlyList<string> namespaces) =>
        model.Methods.Where(m => m.Address != 0 && InNamespaces(m.Owner, namespaces)).ToList();

    public static IReadOnlyList<string> Default(Architecture architecture) => architecture == Architecture.Arm64
        ? ["Sekai.Mysekai", "Sekai.Api", "Sekai.API"]
        : ["GameData.Profile", "DayScene.UI.RogueLike", "GameData.RunTime.Common", "Night.BossBattle.DLC4_BossBattle", "Common.UI"];

    public static IMachine Machine(ImageDocument image) => image.Architecture switch
    {
        Architecture.Arm64 => new Arm64Machine(image),
        _ => throw new NotSupportedException($"{image.Architecture} 尚无提升器"),
    };
}

/// <summary>
/// cfg &lt;binary&gt; &lt;metadata&gt; [0x地址 | 命名空间,...]：
/// 给地址时打印该函数的控制流图；否则对回归集逐个构建并统计。
/// </summary>
internal static class CfgCheck
{
    public static int Run(string binary, string metadata, string? selector)
    {
        var model = ModelCheck.Load(binary, metadata);
        var functions = FunctionTable.Build(model.Image);
        var machine = Corpus.Machine(model.Image);
        var builder = new CfgBuilder(machine, functions);
        if (selector is not null && selector.StartsWith("0x"))
        {
            var address = Convert.ToUInt64(selector[2..], 16);
            if (model.Code.TryGetValue(address, out var owners))
                foreach (var owner in owners) Console.WriteLine($"// {owner.Method}");
            var function = builder.Build(address);
            Console.WriteLine($"// {function.Range.Describe()}  块 {function.Blocks.Count}  跳转表 {function.JumpTables}  未解析间接跳转 {function.UnresolvedIndirectJumps}");
            Console.WriteLine($"// 不返回判定构建了 {builder.NoReturn.Analyzed} 个函数，其中不返回 {builder.NoReturn.Known.Count(p => p.Value)}");
            foreach (var problem in function.Problems) Console.WriteLine($"// 问题: {problem}");
            foreach (var region in function.Range.ExceptionRegions) Console.WriteLine($"// 区间 0x{region.Start:x}..0x{region.End:x} -> 0x{region.LandingPad:x}");
            Console.Write(function);
            return 0;
        }

        var namespaces = selector?.Split(',') ?? Corpus.Default(model.Image.Architecture);
        var methods = Corpus.Select(model, namespaces);
        var addresses = methods.Select(m => m.Address).Distinct().Order().ToList();
        var watch = Stopwatch.StartNew();
        int built = 0, noRange = 0, withProblems = 0, blocks = 0, tables = 0, unresolved = 0, pads = 0;
        var samples = new List<string>();
        var indirect = new List<string>();
        foreach (var address in addresses)
        {
            if (functions.At(address) is not { } range || range.Start != address)
            {
                noRange++;
                if (samples.Count < 20) samples.Add($"0x{address:x} 无边界");
                continue;
            }
            var function = builder.Build(address, range);
            built++;
            blocks += function.Blocks.Count;
            tables += function.JumpTables;
            unresolved += function.UnresolvedIndirectJumps;
            pads += function.Blocks.Count(b => b.IsLandingPad);
            foreach (var block in function.Blocks)
                if (block.Statements[^1] is Ir.Call { Kind: Ir.CallKind.TailIndirect } jump && indirect.Count < 400) indirect.Add($"0x{address:x} @0x{jump.Address:x} {jump.Target}");
            if (function.Problems.Count > 0)
            {
                withProblems++;
                if (samples.Count < 20) samples.Add($"0x{address:x} {string.Join("; ", function.Problems)}");
            }
        }
        var noReturn = builder.NoReturn.Known.Count(p => p.Value);
        Console.WriteLine($"命名空间   {string.Join(",", namespaces)}");
        Console.WriteLine($"方法       {methods.Count}  代码地址 {addresses.Count}");
        Console.WriteLine($"构建       {built}  无边界 {noRange}  有问题 {withProblems}  用时 {watch.ElapsedMilliseconds} ms");
        Console.WriteLine($"基本块     {blocks}  落地块 {pads}  跳转表 {tables}  未解析间接跳转 {unresolved}");
        Console.WriteLine($"不返回函数 {noReturn}（已判定 {builder.NoReturn.Known.Count}，构建 {builder.NoReturn.Analyzed}）");
        if (machine is Arm64Machine arm) Console.WriteLine($"补丁桩指令 {arm.PatchedInstructions}（勘误 843419，按原位置提升）");
        foreach (var sample in samples) Console.WriteLine("  " + sample);
        if (Environment.GetEnvironmentVariable("CPP2CS_INDIRECT") is not null)
            foreach (var sample in indirect) Console.WriteLine("  间接 " + sample);
        return 0;
    }
}
