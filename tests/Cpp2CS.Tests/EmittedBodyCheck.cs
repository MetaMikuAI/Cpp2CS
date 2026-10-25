using System.Text;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests;

/// <summary>比较磁盘产物与执行对照重新写出的 CIL；仅检查产物一致性，不参与执行语义或输入合成。</summary>
internal static class EmittedBodyCheck
{
    public static void AssertSame(string directory, IEnumerable<MethodRecoveryResult> results, Skeleton skeleton)
    {
        var count = Compare(directory, results, skeleton);
        // 磁盘程序集的 Cecil 图只用于身份检查；32 分片同时进入 WorldIndex 前释放这份临时图。
        // 放在 Compare 返回之后，确保局部变量不再持有模块；不影响待执行的 skeleton。
        GC.Collect();
        Console.WriteLine($"  写出 CIL 一致性：{count} 方法（逐指令、操作数、签名、局部变量与 EH）");
    }

    private static int Compare(string directory, IEnumerable<MethodRecoveryResult> results, Skeleton skeleton)
    {
        var rows = File.ReadLines(Path.Combine(directory, "emitted.tsv")).Select(l => l.Split('\t'))
            .ToDictionary(f => (Convert.ToUInt64(f[3], 16), f[4]));
        var count = 0;
        foreach (var group in results.GroupBy(r => rows[(r.Entry, r.Method.ToString())][0]))
        {
            using var module = ModuleDefinition.ReadModule(Path.Combine(directory, "assemblies", group.Key));
            foreach (var result in group)
            {
                var row = rows[(result.Entry, result.Method.ToString())];
                var saved = (MethodDefinition)module.LookupToken(Convert.ToInt32(row[5], 16));
                var tested = skeleton.Method(result.Method.Method);
                var savedDescription = Describe(saved);
                var testedDescription = Describe(tested);
                if (!savedDescription.SequenceEqual(testedDescription))
                {
                    var offset = Enumerable.Range(0, Math.Min(savedDescription.Length, testedDescription.Length))
                        .FirstOrDefault(i => savedDescription[i] != testedDescription[i], Math.Min(savedDescription.Length, testedDescription.Length));
                    string Context(byte[] data) => System.Text.Json.JsonSerializer.Serialize(Encoding.UTF8.GetString(data.Skip(Math.Max(0, offset - 40)).Take(160).ToArray()));
                    throw new InvalidDataException($"0x{result.Entry:x} {result.Method}：磁盘写出 CIL 与执行对照 CIL 不一致；请检查 CPP2CS_READABILITY 与恢复版本；偏移 {offset}，磁盘 {Context(savedDescription)}，对照 {Context(testedDescription)}");
                }
                count++;
            }
        }
        return count;
    }

    internal static byte[] Describe(MethodDefinition method) => CilBodyFingerprint.Describe(method);
}
