using Cpp2CS.Arm64;
using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;
using System.Text.Encodings.Web;
using System.Text.Json;

namespace Cpp2CS.Tests;

internal static class RecoveryCensus
{
    [Command("recovery-audit", "全程序流式 L3 恢复普查；不把恢复成功当作执行验证", Arguments = "<binary> <metadata> <output> [--skip N]")]
    public static int Audit(string binary, string metadata, string output, string[] options)
    {
        var facts = FactsBuilder.Build(binary, metadata, Console.Error.WriteLine);
        var recovery = new MethodRecovery(facts, new ManagedTypes(facts.Model, facts.Layouts));
        Directory.CreateDirectory(output);
        var json = new JsonSerializerOptions { Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping };
        using var writer = new StreamWriter(Path.Combine(output, "recovery.jsonl")) { AutoFlush = true };
        var skip = options.Length == 0 ? 0 : options is ["--skip", var number] ? int.Parse(number) : throw new ArgumentException("仅支持 --skip N");
        var count = skip; var recovered = 0;
        foreach (var method in facts.Model.Methods.Where(m => m.Address != 0 && facts.Code.RegionOf(m.Address) == CodeRegion.Managed).Skip(skip))
        {
            File.WriteAllText(Path.Combine(output, "current-method.tsv"), $"{count}\t0x{method.Address:x}\t{new MethodRef(method, [], [])}");
            var result = recovery.Recover(new MethodRef(method, [], []), method.Address);
            if (result.Body is not null) recovered++;
            writer.WriteLine(JsonSerializer.Serialize(new { address = $"0x{method.Address:x}", method = result.Method.ToString(), assembly = method.Owner.Assembly,
                status = result.Body is null ? "hole" : "recovered", bytes = facts.Code.At(method.Address)?.Size,
                holes = result.Holes.Select(h => new { address = $"0x{h.Address:x}", reason = h.Reason, derived = h.Derived }) }, json));
            if (++count % 1000 == 0) Console.Error.WriteLine($"L3 {count}，无洞 {recovered}；当前 {method}");
        }
        Console.WriteLine($"L3 区间 [{skip}, {count}) 完成，无洞 {recovered}；尚未写出、编译或执行验证");
        return 0;
    }

    [Command("recovery-census", "全程序方法定义与高频运算普查", Arguments = "<binary> <metadata> <output>")]
    public static int Run(string binary, string metadata, string output)
    {
        var facts = FactsBuilder.Build(binary, metadata, Console.Error.WriteLine);
        Directory.CreateDirectory(output);
        var methods = facts.Model.Methods.Where(m => m.Address != 0 && facts.Code.RegionOf(m.Address) == CodeRegion.Managed).ToArray();
        File.WriteAllLines(Path.Combine(output, "methods.tsv"), methods.Select(m => $"0x{m.Address:x}\t{new MethodRef(m, [], [])}\t{m.Owner.Assembly}"));
        File.WriteAllLines(Path.Combine(output, "assemblies.tsv"), new[] { "assembly\tdefinitions\tmanaged-entry\tno-entry\tunique-bytes" }.Concat(
            facts.Model.Methods.GroupBy(m => m.Owner.Assembly).OrderBy(g => g.Key, StringComparer.Ordinal).Select(g =>
                $"{g.Key}\t{g.Count()}\t{g.Count(m => m.Address != 0 && facts.Code.RegionOf(m.Address) == CodeRegion.Managed)}\t{g.Count(m => m.Address == 0)}\t{g.Where(m => m.Address != 0 && facts.Code.RegionOf(m.Address) == CodeRegion.Managed).Select(m => m.Address).Distinct().Sum(e => (long)(facts.Code.At(e)?.Size ?? 0))}")));
        var names = methods.ToLookup(m => m.Address);
        var totals = new Dictionary<string, (int Sites, HashSet<ulong> Functions)>();
        var statements = new List<Stmt>();
        using var sites = new StreamWriter(Path.Combine(output, "arithmetic-sites.tsv"));
        sites.WriteLine("entry\tsite\toperation\tmethod");
        foreach (var function in facts.Code.Functions.Where(f => f.Region == CodeRegion.Managed))
        {
            for (var pc = function.Start; pc + 4 <= function.End; pc += 4)
            {
                statements.Clear();
                Arm64Lifter.Lift(pc, facts.Code.Word(pc)!.Value, statements);
                var operations = statements.OfType<Assign>().SelectMany(s => ExprMap.Walk(s.Value)).Select(e => e switch
                {
                    Binary { Op: BinOp.FMin or BinOp.FMax or BinOp.SDiv or BinOp.UDiv or BinOp.Ror or BinOp.MulHighS or BinOp.MulHighU } b => b.Op.ToString(),
                    Intrinsic { Name: "fminnm" or "fmaxnm" } i => i.Name,
                    _ => null,
                }).OfType<string>().Distinct();
                foreach (var operation in operations)
                {
                    var row = totals.GetValueOrDefault(operation, (Sites: 0, Functions: new HashSet<ulong>()));
                    row.Functions.Add(function.Start);
                    totals[operation] = (row.Sites + 1, row.Functions);
                    sites.WriteLine($"0x{function.Start:x}\t0x{pc:x}\t{operation}\t{names[function.Start].FirstOrDefault()}");
                }
            }
        }
        var summary = new[] { "operation\tsites\tfunctions\tdefinitions\tbytes" }.Concat(totals.OrderByDescending(p => p.Value.Sites).Select(p =>
            $"{p.Key}\t{p.Value.Sites}\t{p.Value.Functions.Count}\t{p.Value.Functions.Sum(e => names[e].Count())}\t{p.Value.Functions.Sum(e => (long)facts.Code.At(e)!.Size)}")).ToArray();
        File.WriteAllLines(Path.Combine(output, "arithmetic.tsv"), summary);
        Console.WriteLine($"方法定义 {facts.Model.Methods.Count}；托管入口定义 {methods.Length}；独立入口 {methods.Select(m => m.Address).Distinct().Count()}；程序集 {facts.Model.Methods.Select(m => m.Owner.Assembly).Distinct().Count()}");
        foreach (var line in summary) Console.WriteLine(line);
        return 0;
    }
}
