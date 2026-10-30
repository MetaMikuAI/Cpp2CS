
namespace Cpp2CS.Facts;

/// <summary>一个运行时元数据槽位（v27+ 全局变量，初值为编码令牌，运行时替换为指针）。</summary>
/// <summary>LoadingFunctions：直接读取槽位内容的函数数；AddressingFunctions：取得槽位地址（经 GOT 或 ADRP+ADD）的函数数。</summary>
public sealed record UsageSlot(ulong Address, Usage Usage, int LoadingFunctions, int AddressingFunctions);

/// <summary>
/// 元数据槽位表。以托管代码对槽位的引用为锚：被引用且初值能按 ((kind&lt;&lt;29)|(index&lt;&lt;1))+1 解码的位置即槽位。
/// 本映像以 PIC 方式经 GOT 访问全局变量：ADRP+LDR 读出 .got 项（RELATIVE 重定位给出槽位地址），
/// 再把槽位地址交给初始化 helper 或从中读取运行时指针；因此引用分为直接（ADRP+LDR/ADD 到槽位）与经 GOT 两类。
/// 另对可写数据节逐字扫描可解码的值，用于核对（只被扫描到而无代码引用的，单独列出，不并入槽位表）。
/// </summary>
public sealed class UsageSlots
{
    public required IReadOnlyDictionary<ulong, UsageSlot> Slots { get; init; }
    /// <summary>可写数据中可解码、但没有托管代码引用的位置。</summary>
    public required IReadOnlyDictionary<ulong, Usage> UnreferencedDecodable { get; init; }
    /// <summary>调用目标 → 调用点之前 4 条内以 ADRP+ADD 构造了槽位地址的调用点数（元数据初始化 helper 的证据）。</summary>
    public required IReadOnlyDictionary<ulong, int> SlotAddressBeforeCall { get; init; }

    public UsageSlot? At(ulong address) => Slots.GetValueOrDefault(address);

    public static UsageSlots Build(ProgramModel model, CodeMap map, CodeScan scan)
    {
        var image = model.Image;
        var writable = image.Sections.Where(s => (s.Flags & 1) != 0 && !s.Executable && s.Type != 8).ToArray();
        var got = image.Section(".got");
        // 引用目标 → 槽位地址：经 GOT 的 8 字节读取取重定位后的指针，其余直接取目标。
        ulong? SlotOf(CodeRef r)
        {
            if (r.Kind == RefKind.Load && r.Size == 8 && got is not null && got.Contains(r.Target))
                return image.RelocatedPointer(r.Target) is { } pointee && model.UsageAt(pointee) is not null ? pointee : null;
            if (r.Kind is RefKind.Load or RefKind.Address && r.Target % 8 == 0 && writable.Any(s => s.Contains(r.Target)) && model.UsageAt(r.Target) is not null)
                return r.Target;
            return null;
        }

        var loads = new Dictionary<ulong, HashSet<int>>();
        var addresses = new Dictionary<ulong, HashSet<int>>();
        var beforeCall = new Dictionary<ulong, int>();
        for (var i = 0; i < map.Functions.Count; i++)
        {
            if (map.Functions[i].Region != CodeRegion.Managed) continue;
            var refs = scan.Of(i);
            for (var k = 0; k < refs.Length; k++)
            {
                var r = refs[k];
                if (r.Kind == RefKind.Call)
                {
                    for (var j = k - 1; j >= 0 && r.Site - refs[j].Site <= 16; j--)
                        if (SlotOf(refs[j]) is not null)
                        {
                            beforeCall[r.Target] = beforeCall.GetValueOrDefault(r.Target) + 1;
                            break;
                        }
                    continue;
                }
                if (SlotOf(r) is not { } slot) continue;
                // 经 GOT 或 ADRP+ADD 得到的是槽位地址；直接 ADRP+LDR 读的是槽位内容
                var bucket = r.Kind == RefKind.Load && slot == r.Target ? loads : addresses;
                if (!bucket.TryGetValue(slot, out var set)) bucket[slot] = set = [];
                set.Add(i);
            }
        }

        var slots = new Dictionary<ulong, UsageSlot>();
        foreach (var target in loads.Keys.Concat(addresses.Keys).Distinct())
            if (model.UsageAt(target) is { } usage)
                slots[target] = new UsageSlot(target, usage, loads.GetValueOrDefault(target)?.Count ?? 0, addresses.GetValueOrDefault(target)?.Count ?? 0);

        var unreferenced = new Dictionary<ulong, Usage>();
        foreach (var section in writable)
        {
            var resolved = image.Resolve(section.Address);
            if (resolved.Kind != Cpp2CS.Image.AddressKind.FileBacked) continue;
            for (var a = (section.Address + 7) & ~7UL; a + 8 <= section.Address + section.Size; a += 8)
                if (!slots.ContainsKey(a) && image.RelocatedPointer(a) is null && model.UsageAt(a) is { } usage)
                    unreferenced[a] = usage;
        }
        return new UsageSlots { Slots = slots, UnreferencedDecodable = unreferenced, SlotAddressBeforeCall = beforeCall };
    }

    public void Check(FactChecks checks, Registrations registrations)
    {
        checks.Info("usage.slots", Slots.Count, "被托管代码引用的元数据槽位，按种类：" + string.Join("，",
            Slots.Values.GroupBy(s => s.Usage.Kind).OrderBy(g => g.Key).Select(g => $"{g.Key}={g.Count()}")) +
            $"；只取地址（经 GOT/ADRP+ADD）的 {Slots.Values.Count(s => s.LoadingFunctions == 0)} 个，有直接读取的 {Slots.Values.Count(s => s.LoadingFunctions > 0)} 个");
        checks.Add("usage.unreferenced-decodable", "Warning", Slots.Count + UnreferencedDecodable.Count,
            UnreferencedDecodable.OrderBy(p => p.Key).Select(p => $"0x{p.Key:x} {p.Value}").ToArray(),
            "可写数据中能解码为令牌、但托管代码不引用的位置（死槽位或偶然值）：" + string.Join("，",
                UnreferencedDecodable.Values.GroupBy(u => u.Kind).OrderBy(g => g.Key).Select(g => $"{g.Key}={g.Count()}")));
        if (registrations.MetadataUsageSlots.Count > 0)
        {
            var listed = registrations.MetadataUsageSlots.ToHashSet();
            checks.Add("usage.registration-list", "Error", listed.Count,
                Slots.Keys.Where(k => !listed.Contains(k)).Select(k => $"0x{k:x}").ToArray(), "代码引用的槽位都在 metadataUsages 表中");
        }
        else checks.Info("usage.registration-list", 0, "metadataRegistration.metadataUsages 为空（v27+ 槽位只以编码初值存在）");
    }
}
