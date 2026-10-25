namespace Cpp2CS.Facts;

/// <summary>
/// 以托管代码的实际用法核验 <see cref="RuntimeLayout"/> 中的偏移：
/// 1. 静态构造调用（ClassInit helper）之前读取 Il2CppClass.cctor_finished_or_no_cctor 并据此跳过；
/// 2. 接口慢路径（InterfaceLookup）之前扫描 interface_offsets_count / interfaceOffsets；
/// 3. 间接调用（BLR）的目标来自 vtable 槽（Il2CppClass+0x138+16n 的 methodPtr）、委托 invoke_impl，或其他来源（分别计数）。
/// </summary>
public static class LayoutChecks
{
    private const int LookBack = 8;

    public static void Run(FactChecks checks, CodeMap map, CodeScan scan, RuntimeHelpers helpers)
    {
        var classInit = helpers.Helpers.Values.Where(h => h.Kind == HelperKind.ClassInit).Select(h => h.Address).ToHashSet();
        // 自带守卫的 ClassInit 入口（函数开头即读取 cctor_finished_or_no_cctor，相当于 il2cpp_codegen_runtime_class_init_inline 的外联版本）：调用者不再需要守卫
        var selfGuarded = classInit.Where(a => map.At(a) is { } f && Linear(map, f, Math.Min(f.End, a + 4 * 4), 4, w => IsLoad(w, RuntimeLayout.ClassCctorFinishedOrNoCctor, 4))).ToHashSet();
        var interfaceLookup = helpers.Helpers.Values.Where(h => h.Kind == HelperKind.InterfaceLookup).Select(h => h.Address).ToHashSet();
        long initSites = 0, selfGuardedSites = 0, interfaceSites = 0, blr = 0, vtable = 0, interfaceHit = 0, invoke = 0, methodPointer = 0, other = 0;
        var initMissing = new List<string>();
        var interfaceMissing = new List<string>();
        var otherSamples = new List<string>();
        for (var i = 0; i < map.Functions.Count; i++)
        {
            var function = map.Functions[i];
            if (function.Region != CodeRegion.Managed) continue;
            foreach (var r in scan.Of(i))
            {
                if (r.Kind != RefKind.Call) continue;
                if (classInit.Contains(r.Target))
                {
                    initSites++;
                    if (selfGuarded.Contains(r.Target)) { selfGuardedSites++; continue; }
                    if (!Before(map, function, r.Site, 12, w => IsLoad(w, RuntimeLayout.ClassCctorFinishedOrNoCctor, 4)))
                        initMissing.Add($"0x{r.Site:x}");
                }
                else if (interfaceLookup.Contains(r.Target))
                {
                    interfaceSites++;
                    if (!Before(map, function, r.Site, 32, w => IsLoad(w, RuntimeLayout.ClassInterfaceOffsetsCount, 2))
                        || !Before(map, function, r.Site, 32, w => IsLoad(w, RuntimeLayout.ClassInterfaceOffsets, 8)))
                        interfaceMissing.Add($"0x{r.Site:x}");
                }
            }
            for (var pc = function.Start; pc + 4 <= function.End; pc += 4)
            {
                if (map.Word(pc) is not { } w || !A64.IsBlr(w)) continue;
                blr++;
                var target = A64.Rn(w);
                // 目标寄存器最近一次被装载：LDR Xt, [Xn, #imm] 或 LDP Xt, Xt2, [Xn, #imm]
                var source = LoadOffsetInto(map, function, pc, target);
                if (source is { } off && off >= RuntimeLayout.ClassVtable && (off - RuntimeLayout.ClassVtable) % RuntimeLayout.VirtualInvokeDataSize == 0) vtable++;
                else if (source == 0 && Linear(map, function, pc, LookBack + 4, x => A64.IsAddImmediate64(x) && A64.AddImmediate(x) == RuntimeLayout.ClassVtable)) interfaceHit++;
                else if (source == RuntimeLayout.DelegateInvokeImpl) invoke++;
                else if (source == RuntimeLayout.MethodPointer) methodPointer++;
                else
                {
                    other++;
                    if (otherSamples.Count < 12) otherSamples.Add($"0x{pc:x}（目标装载偏移 {(source is { } o ? $"0x{o:x}" : "无")}）");
                }
            }
        }
        // 剩余未找到守卫的调用点：守卫寄存器经其他路径进入调用块，需要完整 CFG 前驱才能定位；偏移本身已由其余调用点确认，故记为 Warning
        checks.Add("layout.cctor-guard", "Warning", initSites, initMissing,
            $"每个 ClassInit 调用点之前 12 条内（或跳到其所在块的分支之前）读取 Il2CppClass+0x{RuntimeLayout.ClassCctorFinishedOrNoCctor:x}（cctor_finished_or_no_cctor，4 字节）；" +
            $"调用自带守卫入口（{string.Join("、", selfGuarded.Select(a => $"0x{a:x}"))}）的 {selfGuardedSites} 处不需要");
        checks.Add("layout.interface-scan", "Error", interfaceSites, interfaceMissing,
            $"每个 InterfaceLookup 调用点之前 32 条内读取 +0x{RuntimeLayout.ClassInterfaceOffsetsCount:x}（interface_offsets_count，2 字节）与 +0x{RuntimeLayout.ClassInterfaceOffsets:x}（interfaceOffsets）");
        checks.Add("layout.indirect-calls", "Warning", blr, otherSamples.Take(12).ToArray(),
            $"托管代码 BLR {blr} 处：目标装载自 vtable 槽（+0x{RuntimeLayout.ClassVtable:x}+16n）{vtable}，接口命中（klass+16·(offset+slot)+0x{RuntimeLayout.ClassVtable:x}）{interfaceHit}，" +
            $"委托 invoke_impl（+0x{RuntimeLayout.DelegateInvokeImpl:x}）{invoke}，偏移 0 的方法指针（MethodInfo.methodPointer 等）{methodPointer}，其他 {other}（样例见下，非违例）");
    }

    private static bool IsLoad(uint w, int offset, int size) =>
        A64.IsUnsignedOffsetAccess(w) && !A64.IsStore(w) && A64.AccessSize(w) == size && (int)A64.AccessOffset(w) == offset;

    /// <summary>
    /// 在 site 之前 count 条内，或在跳到 site 所在块的条件/无条件分支之前 count 条内，存在满足 predicate 的指令。
    /// 编译器常把冷路径（类初始化、接口慢路径）放到函数尾部，守卫读取与调用不在同一段直线代码中。
    /// </summary>
    private static bool Before(CodeMap map, CodeFunction function, ulong site, int count, Func<uint, bool> predicate)
    {
        if (Linear(map, function, site, count, predicate)) return true;
        // 所在块的起点：向前直到上一条无条件转移（B/RET/BR）之后
        var start = site;
        while (start > function.Start && map.Word(start - 4) is { } p && !A64.IsB(p) && !A64.IsRet(p) && !A64.IsBr(p)) start -= 4;
        for (var pc = function.Start; pc + 4 <= function.End; pc += 4)
        {
            if (map.Word(pc) is not { } w) continue;
            var target = A64.ConditionalTarget(w, pc) ?? (A64.IsB(w) ? A64.Imm26Target(w, pc) : null);
            if (target is not { } t || t < start || t > site) continue;
            if (Linear(map, function, pc + 4, count + 1, predicate)) return true;
            // CBZ/CBNZ/TBZ 测试的寄存器：沿直线代码回溯到它最近一次被写入，看那条是否就是所求的装载
            if ((A64.IsCbz(w) || A64.IsTbz(w)) && DefinedBy(map, function, pc, A64.Rd(w), predicate)) return true;
        }
        return false;
    }

    private static bool DefinedBy(CodeMap map, CodeFunction function, ulong site, int reg, Func<uint, bool> predicate)
    {
        for (var pc = site; pc > function.Start; pc -= 4)
        {
            if (map.Word(pc - 4) is not { } w) return false;
            if (A64.MayWriteRd(w) && A64.Rd(w) == reg) return predicate(w);
        }
        return false;
    }

    private static bool Linear(CodeMap map, CodeFunction function, ulong site, int count, Func<uint, bool> predicate)
    {
        for (var k = 1; k <= count && site >= function.Start + 4UL * (ulong)k; k++)
            if (map.Word(site - 4UL * (ulong)k) is { } w && predicate(w)) return true;
        return false;
    }

    /// <summary>向前查找最近一条写 reg 的装载指令，返回其无符号偏移；遇到其他写 reg 的指令或超出回看范围返回 null。</summary>
    private static int? LoadOffsetInto(CodeMap map, CodeFunction function, ulong site, int reg)
    {
        for (var k = 1; k <= LookBack && site >= function.Start + 4UL * (ulong)k; k++)
        {
            if (map.Word(site - 4UL * (ulong)k) is not { } w) return null;
            if (A64.IsUnsignedOffsetAccess(w) && !A64.IsStore(w) && A64.Rd(w) == reg && A64.AccessSize(w) == 8) return (int)A64.AccessOffset(w);
            // LDP Xt1, Xt2, [Xn, #imm7*8]（有符号偏移形式）
            if ((w & 0xFFC00000) == 0xA9400000 && (A64.Rd(w) == reg || (int)((w >> 10) & 31) == reg))
            {
                var imm = (int)(((long)((ulong)((w >> 15) & 0x7F) << 57)) >> 57) * 8;
                return A64.Rd(w) == reg ? imm : imm + 8;
            }
            if (A64.MayWriteRd(w) && A64.Rd(w) == reg) return null;
        }
        return null;
    }
}
