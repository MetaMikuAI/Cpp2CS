using System.Text;
using Cpp2CS.Input;
using Cpp2CS.Target;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>按 FDE 遍历整幅映像的 LSDA。子句按调用点行计数，落地块按地址去重。</summary>
internal static class UnwindAudit
{
    public static int Run(string binary)
    {
        var elf = Elf64.Load(binary);
        byte[] file = File.ReadAllBytes(binary);
        var unwind = new UnwindIndex(elf, file);
        int functions = 0, rows = 0, landed = 0, failed = 0;
        var typeCounts = new SortedDictionary<ulong, int>();
        var pads = new Dictionary<ulong, (bool Cleanup, bool HasClause, bool Specification)>();
        foreach (var frame in unwind.Frames)
        {
            if (frame.Lsda == 0) continue;
            functions++;
            CallSite[] sites;
            try
            {
                sites = unwind.Sites(frame, out int count);
                rows += count;
            }
            catch (InvalidDataException error)
            {
                Console.Error.WriteLine($"FDE 0x{frame.Start:x}，LSDA 0x{frame.Lsda:x}：{error.Message}");
                failed++;
                continue;
            }
            landed += sites.Length;
            foreach (var site in sites)
            {
                var pad = pads.GetValueOrDefault(site.Landing);
                pads[site.Landing] = (pad.Cleanup || site.Cleanup, pad.HasClause || !site.Clauses.IsEmpty,
                    pad.Specification || site.Specification);
                foreach (var clause in site.Clauses)
                    typeCounts[clause.TypeInfo] = typeCounts.GetValueOrDefault(clause.TypeInfo) + 1;
            }
        }
        Console.WriteLine($"有 LSDA 的函数 {functions}，调用点行 {rows}，带落地块的行 {landed}，读不通 {failed}");
        Console.WriteLine($"带清理的落地块 {pads.Values.Count(p => p.Cleanup)}，只有清理 {pads.Values.Count(p => p.Cleanup && !p.HasClause && !p.Specification)}，带异常说明 {pads.Values.Count(p => p.Specification)}");
        var named = typeCounts.Select(p => (Address: p.Key, Name: p.Key == 0 ? "全捕获" : TypeName(elf, file, p.Key), Count: p.Value));
        foreach (var group in named.GroupBy(t => t.Name).OrderBy(g => g.Key, StringComparer.Ordinal))
        {
            Console.WriteLine($"子句 {group.Key}：{group.Sum(t => t.Count)}");
            foreach (var type in group.Where(t => t.Address != 0))
                Console.WriteLine($"  类型信息 0x{type.Address:x} {type.Name}");
        }
        return failed == 0 ? 0 : 1;
    }

    // Itanium C++ ABI 的 std::type_info：第二个指针指向类型的名字串。
    static string TypeName(Elf64 elf, byte[] file, ulong address)
    {
        ulong name = elf.Pointer(checked(address + 8));
        int start = elf.FileOffset(name) ?? throw new InvalidDataException($"类型信息 0x{address:x} 的名字没有文件内容");
        int end = Array.IndexOf(file, (byte)0, start);
        if (end <= start || elf.FileOffset(name, (ulong)(end - start + 1)) == null)
            throw new InvalidDataException($"类型信息 0x{address:x} 的名字串无效");
        return Encoding.UTF8.GetString(file, start, end - start);
    }
}
