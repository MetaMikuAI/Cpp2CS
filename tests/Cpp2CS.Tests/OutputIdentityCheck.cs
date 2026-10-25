using System.Text;
using System.Text.RegularExpressions;
using Mono.Cecil;

namespace Cpp2CS.Tests;

/// <summary>
/// 检查两次 recover 的产物是否逐项相同。
/// recover 写出的顶层文件、全部 C# 逐字节比较；程序集只排除 Cecil 自带的 MVID 和 PE 时间戳，另外逐个比较已写出方法的 CIL。
/// 两边都有执行对照结果时，再比较每个方法的判定、一致用例数与覆盖率。对照产生的证据（accessor-verified.tsv）和分片不参与比较。
/// </summary>
internal static class OutputIdentityCheck
{
    private static readonly string[] Verification = ["execution.tsv", "accessor-verified.tsv"];

    [Command("same-output", "两次 recover 的产物逐项相同（清单、洞、C# 逐字节，程序集比较全部 CIL，另比较执行判定）", Arguments = "<恢复目录 前> <恢复目录 后>")]
    public static int Run(string before, string after)
    {
        var a = new Assertions();
        var manifests = TopLevel(before).Union(TopLevel(after)).Except(Verification).Order(StringComparer.Ordinal).ToArray();
        var rawEqual = 0; var normalized = 0; var files = 0;
        foreach (var relative in manifests.Concat(Files("src")).Concat(Files("assemblies")))
        {
            files++;
            var leftPath = Path.Combine(before, relative); var rightPath = Path.Combine(after, relative);
            if (!File.Exists(leftPath) || !File.Exists(rightPath)) { a.True(false, $"文件集合 {relative}"); continue; }
            var left = File.ReadAllBytes(leftPath); var right = File.ReadAllBytes(rightPath);
            if (left.AsSpan().SequenceEqual(right)) { rawEqual++; continue; }
            if (relative == "holes.txt")
            {
                string WithoutTime(byte[] bytes) => Regex.Replace(Encoding.UTF8.GetString(bytes), @"(?m)^(C#：.*)，\d+\.\d+ s\r?$", "$1，<计时> s");
                a.Equal(WithoutTime(left), WithoutTime(right), "洞报告只排除末尾 C# 计时");
            }
            else if (relative.StartsWith("assemblies" + Path.DirectorySeparatorChar, StringComparison.Ordinal))
            {
                Normalize(left, leftPath); Normalize(right, rightPath);
                a.True(left.AsSpan().SequenceEqual(right), $"程序集字节（仅 MVID/时间戳除外）{relative}");
                normalized++;
            }
            else a.True(false, $"文件逐字节不同 {relative}");
        }
        var rows = File.ReadLines(Path.Combine(before, "emitted.tsv")).Select(line => line.Split('\t')).ToArray();
        var bodies = 0;
        foreach (var group in rows.GroupBy(r => r[0]))
        {
            using var left = ModuleDefinition.ReadModule(Path.Combine(before, "assemblies", group.Key));
            using var right = ModuleDefinition.ReadModule(Path.Combine(after, "assemblies", group.Key));
            foreach (var row in group)
            {
                var token = Convert.ToInt32(row[5], 16);
                a.True(EmittedBodyCheck.Describe((MethodDefinition)left.LookupToken(token)).AsSpan()
                    .SequenceEqual(EmittedBodyCheck.Describe((MethodDefinition)right.LookupToken(token))), $"CIL {row[3]} {row[4]}");
                bodies++;
            }
        }
        var verdicts = 0;
        if (File.Exists(Path.Combine(before, "execution.tsv")) && File.Exists(Path.Combine(after, "execution.tsv")))
        {
            // 列：入口、方法、判定、一致用例数、覆盖率；按方法比较，顺序无关。
            Dictionary<string, string> Read(string directory) => File.ReadLines(Path.Combine(directory, "execution.tsv"))
                .Select(l => l.Split('\t')).Where(f => f.Length >= 5).ToDictionary(f => $"{f[0]}\t{f[1]}", f => string.Join('\t', f[2..5]));
            var left = Read(before); var right = Read(after);
            foreach (var key in left.Keys.Union(right.Keys).Order(StringComparer.Ordinal))
            {
                a.Equal(left.GetValueOrDefault(key), right.GetValueOrDefault(key), $"执行判定 {key}");
                verdicts++;
            }
        }
        Console.WriteLine($"same-output：文件 {files}，原始字节相同 {rawEqual}，排除 MVID/PE 时间戳的程序集 {normalized}，CIL 方法 {bodies}，执行判定 {verdicts}");
        return a.Finish("same-output");

        static IEnumerable<string> TopLevel(string directory) => Directory.GetFiles(directory).Select(Path.GetFileName).OfType<string>();
        IEnumerable<string> Files(string directory) => Directory.GetFiles(Path.Combine(before, directory), "*", SearchOption.AllDirectories)
            .Select(p => Path.GetRelativePath(before, p)).Union(Directory.GetFiles(Path.Combine(after, directory), "*", SearchOption.AllDirectories).Select(p => Path.GetRelativePath(after, p)))
            .Order(StringComparer.Ordinal);
    }

    private static void Normalize(byte[] bytes, string file)
    {
        using var module = ModuleDefinition.ReadModule(file);
        var mvid = module.Mvid.ToByteArray();
        var first = bytes.AsSpan().IndexOf(mvid);
        if (first < 0 || bytes.AsSpan(first + mvid.Length).IndexOf(mvid) >= 0) throw new InvalidDataException($"{file}：MVID 不是唯一字节串");
        bytes.AsSpan(first, 16).Clear();
        var pe = BitConverter.ToInt32(bytes, 0x3c);
        if (!bytes.AsSpan(pe, 4).SequenceEqual(new byte[] { 0x50, 0x45, 0, 0 })) throw new InvalidDataException($"{file}：PE 签名");
        bytes.AsSpan(pe + 8, 4).Clear();
    }
}
