using System.Text;
using Cpp2CS.Facts;

namespace Cpp2CS.Cli;

/// <summary>把基础事实写成制表符分隔的文本，供人工核对与其他工具读取。第一行为列名。</summary>
internal static class FactsWriter
{
    public static void Write(ProgramFacts facts, string output)
    {
        Tsv(Path.Combine(output, "functions.tsv"), ["start", "end", "region", "evidence", "lsda_regions", "import", "entries"],
            facts.Code.Functions.Select(f => new[]
            {
                Hex(f.Start), Hex(f.End), f.Region.ToString(), f.Evidence.ToString(), f.ExceptionRegions.Length.ToString(), f.Import ?? "",
                string.Join(";", facts.EntriesAt(f.Start).Select(e => $"{e.Kind}={e.Method?.ToString() ?? e.Detail ?? e.Index.ToString()}")),
            }));
        Tsv(Path.Combine(output, "helpers.tsv"), ["address", "region", "kind", "detail", "call_sites", "evidence"],
            facts.Helpers.Helpers.Values.OrderByDescending(h => h.CallSites).Select(h => new[]
            {
                Hex(h.Address), facts.Code.RegionOf(h.Address).ToString(), h.Kind.ToString(), h.Detail ?? "", h.CallSites.ToString(), h.Evidence,
            }));
        Tsv(Path.Combine(output, "usages.tsv"), ["slot", "kind", "index", "value", "addressing_functions", "loading_functions"],
            facts.Usages.Slots.Values.OrderBy(s => s.Address).Select(s => new[]
            {
                Hex(s.Address), s.Usage.Kind.ToString(), s.Usage.Index.ToString(), s.Usage.Value.ToString() ?? "", s.AddressingFunctions.ToString(), s.LoadingFunctions.ToString(),
            }));
        Tsv(Path.Combine(output, "rgctx.tsv"), ["image", "token", "index", "kind", "value"],
            facts.Registrations.Rgctx.OrderBy(p => p.Key.Image, StringComparer.Ordinal).ThenBy(p => p.Key.Token)
                .SelectMany(p => p.Value.Select((r, i) => new[] { p.Key.Image, $"0x{p.Key.Token:x8}", i.ToString(), r.Kind.ToString(), r.Value?.ToString() ?? "" })));
        Tsv(Path.Combine(output, "erratum-patches.tsv"), ["site", "stub", "original", "adrp_page_offset"],
            facts.Code.Patches.Values.OrderBy(p => p.Site).Select(p => new[]
            {
                Hex(p.Site), Hex(p.Stub), $"0x{p.Original:x8}", p.AdrpPageOffset is { } o ? $"0x{o:x3}" : "",
            }));
    }

    private static string Hex(ulong value) => $"0x{value:x}";

    private static void Tsv(string path, string[] header, IEnumerable<string[]> rows)
    {
        using var writer = new StreamWriter(path, false, new UTF8Encoding(false));
        writer.WriteLine(string.Join('\t', header));
        foreach (var row in rows) writer.WriteLine(string.Join('\t', row.Select(Clean)));
    }

    private static string Clean(string value) => value.Replace('\t', ' ').Replace('\n', ' ').Replace('\r', ' ');
}
