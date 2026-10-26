using System.Text.Json;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Facts;
using Cpp2CS.Recovery;
using Microsoft.CodeAnalysis.CSharp;

namespace Cpp2CS.Tests;

internal static partial class StateMachineScope
{
    [Command("type-scope-inventory", "指定类型及其嵌套类型的全部方法和状态机清单", Arguments = "<binary> <metadata> <types file> <output>")]
    public static int TypeInventory(string binary, string metadata, string typeFile, string output)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var requested = File.ReadLines(typeFile).Select(l => l.Trim()).Where(l => l.Length != 0 && !l.StartsWith('#')).ToArray();
        var roots = requested.Select(name =>
        {
            var generic = name.IndexOf('<');
            var full = generic < 0 ? name : name[..generic];
            var arity = generic < 0 ? 0 : name[generic..].Count(c => c == ',') + 1;
            return facts.Model.Types.Single(t => t.FullName == full && t.GenericParameters.Count == arity);
        }).ToHashSet();
        string Selected(TypeDef type)
        {
            for (TypeDef? current = type; current is not null; current = current.DeclaringType)
                if (roots.Contains(current)) return current.FullName;
            return "";
        }
        Directory.CreateDirectory(output);
        var members = facts.Model.Methods.Where(m => Selected(m.Owner).Length != 0).ToArray();
        File.WriteAllLines(Path.Combine(output, "types.tsv"), new[] { "type\tsource\tmethods\tnative\tnoAddress" }.Concat(roots.OrderBy(t => t.FullName).Select(t =>
        {
            var methods = members.Where(m => Selected(m.Owner) == t.FullName).ToArray();
            return $"{t.FullName}\t{t.Assembly}_{(t.Namespace.Length == 0 ? t.Name : t.Namespace + "." + t.Name)}.cs\t{methods.Length}\t{methods.Count(m => m.Address != 0)}\t{methods.Count(m => m.Address == 0)}";
        })));
        File.WriteAllLines(Path.Combine(output, "members.tsv"), new[] { "type\taddress\tmethod\tkind" }.Concat(members.Select(m =>
            $"{Selected(m.Owner)}\t{Hex(m.Address)}\t{m}\t{(m.Name == "MoveNext" ? "MoveNext" : m.Owner.DeclaringType is null ? "ordinary" : "nested")}")));
        Console.WriteLine($"目标类型={roots.Count}；元数据方法={members.Length}；无独立入口={members.Count(m => m.Address == 0)}");
        Inventory(facts.Model.Methods, Selected, output, true);
        var ordinary = members.Where(m => m.Address != 0 && facts.Code.RegionOf(m.Address) == CodeRegion.Managed)
            .Select(m => new RecoveryTarget(new(m, [], []), m.Address));
        var shared = facts.Model.Code.SelectMany(p => p.Value.Where(o => o.IsInstance && Selected(o.Method.Method.Owner).Length != 0)
            .Select(o => new RecoveryTarget(o.Method, p.Key))).Where(t => t.Instance.Method.Address == 0)
            .GroupBy(t => t.Instance.Method).Select(g => g.OrderBy(t => t.Instance.TypeArguments.Concat(t.Instance.MethodArguments)
                .Any(a => !ManagedTypes.IsReferenceType(a) || FieldLayouts.IsFullyShared(a))).ThenBy(t => t.Entry).First());
        var targets = ordinary.Concat(shared).OrderBy(t => t.Entry).ToArray();
        File.WriteAllLines(Path.Combine(output, "methods.tsv"), targets.Select(t => $"{Hex(t.Entry)}\t{t.Instance}"));
        var entries = facts.Model.Code.Where(p => p.Value.Any(o => Selected(o.Method.Method.Owner).Length != 0)).Select(p => p.Key)
            .Concat(ordinary.Select(t => t.Entry)).Where(e => facts.Code.RegionOf(e) == CodeRegion.Managed).Distinct().Order().ToArray();
        File.WriteAllLines(Path.Combine(output, "native-entries.tsv"), new[] { "entry\tbytes" }
            .Concat(entries.Select(e => $"{Hex(e)}\t{facts.Code.At(e)!.Size}")));
        Console.WriteLine($"含泛型共享入口的方法={targets.Length}；全部原生实例入口={entries.Length}；固定字节分母={entries.Sum(e => (long)facts.Code.At(e)!.Size)}");
        return 0;
    }

    private static void TypeReport(string inventoryDirectory, string recoverDirectory, string output)
    {
        var members = File.ReadLines(Path.Combine(inventoryDirectory, "members.tsv")).Skip(1).Select(l => l.Split('\t')).ToArray();
        var recovered = File.ReadLines(Path.Combine(recoverDirectory, "recovery.jsonl")).Select(l => JsonDocument.Parse(l)).ToArray();
        var status = recovered.Where(d => !d.RootElement.GetProperty("dependency").GetBoolean())
            .ToDictionary(d => d.RootElement.GetProperty("address").GetString()!, d => d.RootElement.GetProperty("status").GetString()!);
        var rows = new List<string> { "type\tmethods\temitted\thole\temitFailed\tnoAddress\tnotSelected\t_003C\t_003E" };
        foreach (var line in File.ReadLines(Path.Combine(inventoryDirectory, "types.tsv")).Skip(1))
        {
            var fields = line.Split('\t');
            var group = members.Where(m => m[0] == fields[0]).ToArray();
            var statuses = group.Select(m => m[1] == "0x0" ? "no-address" : status.GetValueOrDefault(m[1], "not-selected")).ToArray();
            var path = Path.Combine(recoverDirectory, "src", fields[1]);
            var identifiers = File.Exists(path) ? CSharpSyntaxTree.ParseText(File.ReadAllText(path)).GetRoot().DescendantTokens()
                .Where(t => t.RawKind == (int)SyntaxKind.IdentifierToken).Select(t => t.ValueText).ToArray() : [];
            rows.Add(string.Join('\t', fields[0], group.Length, statuses.Count(s => s == "emitted"), statuses.Count(s => s == "hole"),
                statuses.Count(s => s == "emit-failed"), statuses.Count(s => s == "no-address"), statuses.Count(s => s == "not-selected"),
                identifiers.Sum(s => s.Split("_003C", StringSplitOptions.None).Length - 1), identifiers.Sum(s => s.Split("_003E", StringSplitOptions.None).Length - 1)));
        }
        File.WriteAllLines(Path.Combine(output, "types-summary.tsv"), rows);
        foreach (var doc in recovered) doc.Dispose();
        Console.WriteLine(string.Join('\n', rows));
    }
}
