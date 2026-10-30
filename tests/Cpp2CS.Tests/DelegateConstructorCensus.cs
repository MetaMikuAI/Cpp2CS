using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Lifting;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

/// <summary>独立检查全部注册委托构造器是否读取隐藏 MethodInfo；不参考被测调用者或恢复后的 CIL。</summary>
internal static class DelegateConstructorCensus
{
    [Command("delegate-constructors", "全部注册委托构造器的隐藏 MethodInfo 读取普查", Arguments = "<binary> <metadata> <输出.tsv>")]
    public static int Run(string binary, string metadata, string output)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var abi = new ManagedAbi(facts.Layouts);
        var lifter = new FunctionLifter(facts);
        var rows = new List<string> { "entry\tmethod\thidden\tread\terrors" };
        var failures = 0;
        var entries = facts.Registrations.Entries.Where(e => e.Method is { Method.Name: ".ctor" } m && IsDelegate(m.DeclaringType)).DistinctBy(e => e.Address).ToArray();
        foreach (var entry in entries)
        {
            var signature = abi.Classify(entry.Method!, out _);
            var lifted = lifter.Lift(entry.Address);
            var statements = lifted.Function.Blocks.SelectMany(b => b.Statements).ToArray();
            var hidden = signature?.MethodInfo?.Register;
            var reads = hidden is null || statements.SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => u.Variable.Version == 0 && u.Variable.Storage == hidden)
                || statements.OfType<Phi>().Any(p => p.Sources.Any(v => v.Version == 0 && v.Storage == hidden));
            if (reads || !lifted.Succeeded) failures++;
            rows.Add($"0x{entry.Address:x}\t{entry.Method}\t{hidden}\t{reads}\t{string.Join(';', lifted.Errors)}");
        }
        Directory.CreateDirectory(Path.GetDirectoryName(output)!);
        File.WriteAllLines(output, rows);
        Console.WriteLine($"注册委托构造入口 {entries.Length}；读取隐藏 MethodInfo 或提升失败 {failures}");
        return failures == 0 ? 0 : 1;
    }

    private static bool IsDelegate(TypeRef? type)
    {
        for (var current = type as DefinitionRef; current is not null; current = current.Definition.BaseType as DefinitionRef)
            if (current.Definition.FullName == "System.MulticastDelegate") return true;
        return false;
    }
}
