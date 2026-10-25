using Cpp2CS.Functions;

namespace Cpp2CS.Facts;

/// <summary>代码地图、引用普查与注册表入口之间的交叉不变式。</summary>
public static class CodeChecks
{
    public static void Run(FactChecks checks, CodeMap map, CodeScan scan, Registrations registrations)
    {
        var image = map.Image;
        string Hex(ulong a) => $"0x{a:x}";
        string Where(ulong a) => map.At(a) is { } f ? $"{Hex(a)}（函数 {Hex(f.Start)}+0x{a - f.Start:x}）" : $"{Hex(a)}（不在函数内）";

        // 范围为零的 FDE 是被丢弃函数留下的空条目，不对应代码。
        var emptyFdes = map.FdeSkipped.Where(x => x.EndsWith("FDE 范围为零", StringComparison.Ordinal)).ToArray();
        checks.Add("fde.skipped", "Error", map.Functions.Count(f => f.Evidence == BoundaryEvidence.EhFrame) + map.FdeSkipped.Count,
            map.FdeSkipped.Except(emptyFdes).ToArray(), $"全部 FDE 条目均已解析（CIE 增强、指针编码、LSDA）；范围为零的空条目 {emptyFdes.Length} 个");
        var counts = map.Functions.GroupBy(f => (f.Region, f.Evidence)).OrderBy(g => g.Key.Region).ThenBy(g => g.Key.Evidence)
            .Select(g => $"{g.Key.Region}/{g.Key.Evidence}={g.Count()}");
        checks.Info("code.functions", map.Functions.Count, string.Join("，", counts));

        foreach (var (section, _) in map.CodeSections)
        {
            var covered = map.Functions.Where(f => section.Contains(f.Start)).Sum(f => (double)f.Size);
            checks.Info($"code.coverage.{section.Name}", (long)section.Size, $"函数覆盖 {100 * covered / section.Size:F4}%");
        }
        checks.Add("code.gaps.unexplained", "Error", map.Gaps.Count,
            map.Gaps.Where(g => g.Kind == "unexplained").Select(g => $"{Hex(g.Start)}..{Hex(g.End)}").ToArray(),
            "可执行节中函数之外的区间只能是勘误补丁桩或填充：" + string.Join("，", map.Gaps.GroupBy(g => g.Kind).Select(g => $"{g.Key}={g.Count()}")));
        checks.Add("code.erratum843419", "Error", map.Patches.Count,
            map.Patches.Values.Where(p => p.AdrpPageOffset is null).Select(p => $"{Hex(p.Site)} → {Hex(p.Stub)}").ToArray(),
            "每个补丁位置之前 1–4 条内有 ADRP；ADRP 页内偏移分布：" + string.Join("，", map.Patches.Values
                .GroupBy(p => p.AdrpPageOffset).OrderByDescending(g => g.Count()).Select(g => $"{(g.Key is { } o ? $"0x{o:x3}" : "无")}={g.Count()}")));
        checks.Add("code.referenced-without-fde.managed", "Error", map.ReferencedWithoutFde.Count,
            map.ReferencedWithoutFde.Where(p => map.RegionOf(p.Key) == CodeRegion.Managed).Select(p => $"{Hex(p.Key)} ({p.Value})").ToArray(),
            "托管代码节中没有缺少 FDE 的被引用入口；运行时节中的：" + string.Join("，", map.ReferencedWithoutFde.Select(p => $"{Hex(p.Key)}({p.Value})")));

        checks.Add("scan.conditional-escape", "Error", map.Functions.Count, scan.EscapingConditionals.Select(e => $"{Where(e.Site)} → {Where(e.Target)}").ToArray(),
            "条件分支（B.cond/CBZ/TBZ）不离开所在函数");

        var calls = new List<string>();
        var tails = new List<string>();
        var codePointers = new List<string>();
        long callCount = 0, tailCount = 0, pointerCount = 0, localLabels = 0;
        foreach (var r in scan.All)
        {
            switch (r.Kind)
            {
                case RefKind.Call:
                    callCount++;
                    if (!map.IsEntry(r.Target)) calls.Add($"{Where(r.Site)} → {Where(r.Target)}");
                    break;
                case RefKind.TailCall:
                    tailCount++;
                    if (!map.IsEntry(r.Target)) tails.Add($"{Where(r.Site)} → {Where(r.Target)}");
                    break;
                case RefKind.Address or RefKind.Adr when image.IsExecutable(r.Target):
                    // 同一函数内的代码地址是局部标号（跳转表基址等），不是入口
                    if (map.At(r.Site) is { } owner && owner.Contains(r.Target)) { localLabels++; break; }
                    pointerCount++;
                    if (!map.IsEntry(r.Target)) codePointers.Add($"{Where(r.Site)} → {Where(r.Target)}");
                    break;
            }
        }
        checks.Add("scan.call-targets", "Error", callCount, calls, "BL 目标都是函数入口（含 PLT 桩）");
        checks.Add("scan.tailcall-targets", "Error", tailCount, tails, "跳出函数的 B 目标都是函数入口（勘误补丁已还原）");
        checks.Add("scan.code-pointers", "Error", pointerCount, codePointers, $"ADRP+ADD / ADR 构造的、指向所在函数之外的代码地址都是函数入口（函数内局部标号 {localLabels} 处）");

        var relocated = image.RelocatedPointerTargets().Where(image.IsExecutable).Distinct().ToArray();
        checks.Add("reloc.code-pointers", "Error", relocated.Length,
            relocated.Where(t => !map.IsEntry(t)).Select(Where).ToArray(), "重定位写入的代码指针都是函数入口");

        checks.Add("registrations.entries-at-functions", "Error", registrations.Entries.Count,
            registrations.Entries.Where(e => !map.IsEntry(e.Address)).Select(e => $"{e.Kind} {Where(e.Address)} {e.Method}").ToArray(),
            "注册表中的每个代码入口都是函数入口：" + string.Join("，", registrations.Entries.GroupBy(e => e.Kind).Select(g => $"{g.Key}={g.Count()}")));

        var managed = map.Functions.Where(f => f.Region == CodeRegion.Managed).ToArray();
        var owned = managed.Count(f => registrations.ByAddress.ContainsKey(f.Start));
        var calledOnly = new HashSet<ulong>(scan.All.Where(r => r.Kind is RefKind.Call or RefKind.TailCall).Select(r => r.Target));
        var unowned = managed.Where(f => !registrations.ByAddress.ContainsKey(f.Start)).ToArray();
        checks.Info("managed.functions", managed.Length,
            $"有注册表所有者 {owned}；无所有者 {unowned.Length}（其中被 BL/B 调用 {unowned.Count(f => calledOnly.Contains(f.Start))}，" +
            $"无代码引用 {unowned.Count(f => !calledOnly.Contains(f.Start))}）");
        checks.Info("registrations.addresses", registrations.ByAddress.Count,
            $"注册表入口 {registrations.Entries.Count} 条落在 {registrations.ByAddress.Count} 个不同地址；" +
            string.Join("，", registrations.ByAddress.Values.Where(v => v.Length > 1).GroupBy(v => string.Join("+", v.Select(e => e.Kind).Distinct().Order()))
                .OrderByDescending(g => g.Count()).Take(8).Select(g => $"[{g.Key}]×{g.Count()}")));
        var shared = registrations.ByAddress.Where(p => p.Value.Count(e => e.Method is not null) > 1).ToArray();
        checks.Info("registrations.shared-code", shared.Length,
            $"同一地址有多个托管所有者（ICF 折叠或泛型共享）的入口数；所有者合计 {shared.Sum(p => p.Value.Length)}，最多 {(shared.Length == 0 ? 0 : shared.Max(p => p.Value.Length))}");
    }
}
