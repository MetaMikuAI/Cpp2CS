using System.Text;
using Cpp2CS.Images;

namespace Cpp2CS.Facts;

/// <summary>托管代码调用的运行时辅助函数种类。</summary>
public enum HelperKind
{
    Unknown,
    /// <summary>按编码令牌初始化元数据槽位（参数为槽位地址）。</summary>
    InitMetadata,
    ObjectNew, NewArray, NewArrayFull, Box, Unbox, ClassInit, Raise, WriteBarrier, IsAssignableFrom,
    /// <summary>构造并抛出指定异常（不返回）。Detail 为异常类型全名。</summary>
    Throw,
    /// <summary>未内联的判空：x0 为空时抛出 NullReferenceException，否则返回。</summary>
    NullCheck,
    /// <summary>构造并返回指定异常对象。Detail 为异常类型全名。</summary>
    GetException,
    /// <summary>il2cpp_object_get_virtual_method 等虚方法/接口查找。</summary>
    VirtualMethodLookup,
    StringNew,
    /// <summary>确保类已完成 Class::Init（布局、vtable），初始化失败则抛出；返回参数本身。不运行静态构造。</summary>
    InitializedTypeInfo,
    /// <summary>接口方法查找慢路径：(对象, 接口类, 槽位) → VirtualInvokeData*。</summary>
    InterfaceLookup,
    /// <summary>is_assignable_from(klass, obj->klass) 成立返回对象，否则 null（isinst）。</summary>
    IsInst,
    /// <summary>dmb ish：内存屏障（Thread.MemoryBarrier / volatile）。</summary>
    MemoryBarrier,
    /// <summary>以 C++ 异常 Il2CppExceptionWrapper 抛出 x0 中的托管异常对象（重新抛出，不更新堆栈）。</summary>
    Rethrow,
    /// <summary>__clang_call_terminate：开始捕获后调用 std::terminate。</summary>
    Terminate,
    /// <summary>libunwind _Unwind_Resume：清理落地块结束后继续展开。</summary>
    UnwindResume,
    /// <summary>确保 MethodInfo 的 rgctx_data 已初始化（共享泛型方法），返回参数本身。</summary>
    InitMethodRgctx,
    /// <summary>数组元素地址：arr + 0x20 + index × klass->element_size。</summary>
    ArrayElementAddress,
    /// <summary>实例字段数据地址：obj + FieldInfo->offset（值类型减对象头）。</summary>
    FieldAddress,
    /// <summary>导入的 C/C++ 运行时函数（memcpy、__cxa_*、libm 等）。Detail 为符号名。</summary>
    Import,
    /// <summary>其他 il2cpp_* 导出（Detail 为导出名），语义按导出 API 理解。</summary>
    Export,
}

/// <summary>一个被托管代码调用的辅助函数。Evidence 说明依据；Callers 为托管调用点数。</summary>
public sealed record RuntimeHelper(ulong Address, HelperKind Kind, string? Detail, string Evidence, int CallSites)
{
    public override string ToString() => Detail is null ? Kind.ToString() : $"{Kind}({Detail})";
}

/// <summary>
/// 识别托管代码（il2cpp 节）调用的非托管目标。依据只用代码与符号事实，不读调试信息：
/// 1. PLT 导入名；
/// 2. il2cpp_* 导出：从导出与候选各自沿“细跳板”（首条为 B，或至多 8 条且只有一次调用的包装）前进，链路相交即同一实现；
/// 3. 异常：闭包内有函数以 ("System", "XxxException") C 字符串构造异常；若同时到达 Raise 则为 Throw，否则 GetException。
///    Throw 还要求函数本身不返回（没有 ret，也不以 B/BR 跳到会返回的函数）：会返回的是条件抛出（判空、越界、类型检查、icall 解析），
///    其中只认精确形态 "cbz x0 → 抛出 NRE；ret"（未内联的判空，NullCheck），其余记为 Unknown；
/// 4. 元数据槽位初始化：闭包内有令牌解码（取位 29–31 的 UBFX/LSR #29）且调用点前紧邻 ADRP+ADD 构造已解码槽位地址。
/// 识别不出的目标保持 Unknown 并按调用点数排序报告，不按启发式强行命名。
/// </summary>
public sealed class RuntimeHelpers
{
    private const int ThinLimit = 8;
    private const int ClosureDepth = 4;
    private const int ClosureFunctionLimit = 96;
    private const int ExceptionWrapperLimit = 24;

    private static readonly (string Export, HelperKind Kind)[] ExportKinds =
    [
        ("il2cpp_object_new", HelperKind.ObjectNew),
        ("il2cpp_array_new_specific", HelperKind.NewArray),
        ("il2cpp_array_new_full", HelperKind.NewArrayFull),
        ("il2cpp_value_box", HelperKind.Box),
        ("il2cpp_object_unbox", HelperKind.Unbox),
        ("il2cpp_runtime_class_init", HelperKind.ClassInit),
        ("il2cpp_raise_exception", HelperKind.Raise),
        ("il2cpp_gc_wbarrier_set_field", HelperKind.WriteBarrier),
        ("il2cpp_class_is_assignable_from", HelperKind.IsAssignableFrom),
        ("il2cpp_object_get_virtual_method", HelperKind.VirtualMethodLookup),
        ("il2cpp_string_new_len", HelperKind.StringNew),
    ];

    private readonly CodeMap map;
    private readonly CodeScan scan;
    private readonly Dictionary<ulong, (HelperKind Kind, string Export, int Depth)> exportChains = new();
    private readonly Dictionary<ulong, RuntimeHelper> helpers = new();

    public IReadOnlyDictionary<ulong, RuntimeHelper> Helpers => helpers;

    private RuntimeHelpers(CodeMap map, CodeScan scan)
    {
        this.map = map;
        this.scan = scan;
    }

    public RuntimeHelper? At(ulong address) => helpers.GetValueOrDefault(address);

    /// <summary>
    /// targets：托管代码调用的、没有托管所有者的目标及调用点数；slotAddressesBeforeCall：目标 → 调用点前紧邻构造了已解码元数据槽位地址的次数。
    /// </summary>
    public static RuntimeHelpers Identify(CodeMap map, CodeScan scan, IReadOnlyDictionary<ulong, int> targets, IReadOnlyDictionary<ulong, int> slotAddressesBeforeCall)
    {
        var result = new RuntimeHelpers(map, scan);
        result.BuildExportChains();
        result.interfaceSlowPath = result.InterfaceSlowPath();
        foreach (var (target, count) in targets)
            result.helpers[target] = result.Classify(target, count, slotAddressesBeforeCall.GetValueOrDefault(target));
        return result;
    }

    private void BuildExportChains()
    {
        var exports = map.Image.Exports;
        var semantic = ExportKinds.ToDictionary(e => e.Export, e => e.Kind);
        foreach (var (name, address) in exports)
        {
            if (!name.StartsWith("il2cpp_", StringComparison.Ordinal)) continue;
            var kind = semantic.GetValueOrDefault(name, HelperKind.Export);
            var depth = 0;
            foreach (var hop in Chain(address))
            {
                // 语义导出优先于一般导出；同为语义导出时取离导出更近者
                if (!exportChains.TryGetValue(hop, out var existing) || (existing.Kind == HelperKind.Export && kind != HelperKind.Export)
                    || (existing.Kind != HelperKind.Export && kind != HelperKind.Export && depth < existing.Depth))
                    exportChains[hop] = (kind, name, depth);
                depth++;
            }
        }
    }

    /// <summary>沿细跳板前进：入口即 B，或至多 ThinLimit 条且恰有一次调用/尾调用、无其他引用的包装。</summary>
    private IEnumerable<ulong> Chain(ulong address)
    {
        var seen = new HashSet<ulong>();
        var current = address;
        for (var i = 0; i < 6 && seen.Add(current); i++)
        {
            yield return current;
            if (Thin(current) is not { } next) yield break;
            current = next;
        }
    }

    private ulong? Thin(ulong address)
    {
        var index = map.EntryIndex(address);
        if (index < 0) return null;
        var function = map.Functions[index];
        if (map.Word(address) is { } first && A64.IsB(first)) return A64.Imm26Target(first, address);
        if (function.Size > ThinLimit * 4) return null;
        // 导出 API 外层常有 catch(...) 落地块，其中的 __cxa_begin_catch/__cxa_end_catch/terminate 不算包装的调用
        var refs = scan.Of(index).ToArray().Where(r => !IsExceptionPlumbing(r.Target)).ToArray();
        return refs.Length == 1 && refs[0].Kind is RefKind.Call or RefKind.TailCall ? refs[0].Target : null;
    }

    private bool IsExceptionPlumbing(ulong target) =>
        map.At(target) is { Region: CodeRegion.Plt, Import: { } name } && (name.StartsWith("__cxa_", StringComparison.Ordinal) || name.Contains("terminate", StringComparison.Ordinal));

    private string? ImportAt(ulong target) => map.At(target) is { Region: CodeRegion.Plt, Import: var name } ? name : null;

    /// <summary>函数内的指令字（勘误补丁已还原）。</summary>
    private IEnumerable<(ulong Pc, uint Word)> Words(ulong address, int limit)
    {
        var function = map.At(address);
        if (function is null) yield break;
        for (var pc = function.Start; pc < function.End && pc < function.Start + (ulong)limit * 4; pc += 4)
            if (map.Word(pc) is { } w) yield return (pc, w);
    }

    /// <summary>无符号偏移读取 [Xn, #offset]（任意宽度）的指令是否出现在函数前 limit 条中。</summary>
    private bool LoadsOffset(ulong address, int offset, int limit = 24) =>
        Words(address, limit).Any(x => A64.IsUnsignedOffsetAccess(x.Word) && !A64.IsStore(x.Word) && (int)A64.AccessOffset(x.Word) == offset);

    private IEnumerable<ulong> CallsOf(ulong address)
    {
        var index = map.EntryIndex(address);
        if (index < 0) return [];
        return scan.Of(index).ToArray().Where(r => r.Kind is RefKind.Call or RefKind.TailCall).Select(r => r.Target);
    }

    /// <summary>沿 B/细包装到达的最终实现。</summary>
    private ulong Terminal(ulong address) => Chain(address).Last();

    private HelperKind KindAt(ulong address)
    {
        foreach (var hop in Chain(address))
            if (exportChains.TryGetValue(hop, out var e)) return e.Kind;
        return HelperKind.Unknown;
    }

    /// <summary>il2cpp_object_get_virtual_method 实现中，接口偏移扫描（interface_offsets_count、interfaceOffsets）失败后调用的慢路径。</summary>
    private ulong? InterfaceSlowPath()
    {
        if (!map.Image.Exports.TryGetValue("il2cpp_object_get_virtual_method", out var export)) return null;
        var body = Terminal(export);
        if (!LoadsOffset(body, RuntimeLayout.ClassInterfaceOffsetsCount, 40) || !LoadsOffset(body, RuntimeLayout.ClassInterfaceOffsets, 40)) return null;
        return CallsOf(body).FirstOrDefault() is var first && first != 0 ? first : null;
    }

    /// <summary>结构规则：只依赖精确偏移与固定指令序列，命中的都写明依据。</summary>
    private (HelperKind Kind, string? Detail, string Evidence)? Structural(ulong target, ulong[] chain)
    {
        var body = chain[^1];
        var words = Words(body, 64).Select(x => x.Word).ToArray();
        if (words is [0xD5033BBF, var ret] && A64.IsRet(ret)) return (HelperKind.MemoryBarrier, null, "函数体为 dmb ish; ret");
        if (interfaceSlowPath is { } slow && chain.Contains(slow))
            return (HelperKind.InterfaceLookup, null, $"il2cpp_object_get_virtual_method 在接口偏移扫描失败后调用 0x{slow:x}");
        var calls = CallsOf(body).ToArray();
        var imports = calls.Select(ImportAt).Where(n => n is not null).ToArray();
        if (imports.Contains("__cxa_allocate_exception") && imports.Contains("__cxa_throw") && ThrowsIl2CppWrapper(body))
            return (HelperKind.Rethrow, null, "以 __cxa_allocate_exception/__cxa_throw 抛出 typeinfo 名含 Il2CppExceptionWrapper 的 C++ 异常");
        if (words.Length <= 4 && imports.Length == 2 && imports[0] == "__cxa_begin_catch" && imports[1]!.Contains("terminate", StringComparison.Ordinal))
            return (HelperKind.Terminate, null, "__cxa_begin_catch 之后调用 std::terminate");
        if (References(body, "_Unwind_Resume")) return (HelperKind.UnwindResume, null, "函数引用 libunwind 字符串 \"_Unwind_Resume\"");
        // 包装规则看链上第一个不是单条 B 的函数本身：保存 x0，先调用一次实现，再检查/返回 x0（其后可能有抛出路径的其他调用）
        var wrapper = chain.FirstOrDefault(h => map.Word(h) is not { } w0 || !A64.IsB(w0), body);
        var wrapperWords = Words(wrapper, 64).Select(x => x.Word).ToArray();
        var wrapperCalls = CallsOf(wrapper).ToArray();
        if (wrapperWords.Length <= 32 && wrapperCalls.Length >= 1)
        {
            if (LoadsOffset(wrapper, RuntimeLayout.ClassInitializationExceptionGCHandle, 12)
                && LoadsOffset(wrapperCalls[0], RuntimeLayout.ClassBitflags1, 8))
                return (HelperKind.InitializedTypeInfo, null,
                    $"调用 0x{wrapperCalls[0]:x}（检查 Il2CppClass+0x{RuntimeLayout.ClassBitflags1:x} 的 initialized 位）后读取 +0x{RuntimeLayout.ClassInitializationExceptionGCHandle:x} initializationExceptionGCHandle");
            if (LoadsOffset(wrapperCalls[0], RuntimeLayout.MethodRgctxData, 4) && LoadsOffset(wrapperCalls[0], RuntimeLayout.MethodGenericMethod, 24)
                && wrapperWords.Contains(0xAA1303E0u))   // mov x0, x19：返回原参数
                return (HelperKind.InitMethodRgctx, null,
                    $"调用 0x{wrapperCalls[0]:x}（读取 MethodInfo+0x{RuntimeLayout.MethodRgctxData:x} rgctx_data 与 +0x{RuntimeLayout.MethodGenericMethod:x} genericMethod）后返回原 MethodInfo");
        }
        // cbz x0, ...（0xB4000000 | imm19 << 5 | Rt=0）出现在前 6 条：空对象直接返回
        if (calls.Length >= 1 && KindAt(calls[0]) == HelperKind.IsAssignableFrom && words.Take(6).Any(w => (w & 0xFF00001F) == 0xB4000000))
            return (HelperKind.IsInst, null, $"空对象直接返回，否则调用 is_assignable_from 实现 0x{calls[0]:x}");
        if (LoadsOffset(body, RuntimeLayout.ClassElementSize, 8) && words.Any(w => A64.IsAddImmediate64(w) && A64.AddImmediate(w) == RuntimeLayout.ArrayData))
            return (HelperKind.ArrayElementAddress, null, $"读取 Il2CppClass+0x{RuntimeLayout.ClassElementSize:x} element_size，并加数组头 0x{RuntimeLayout.ArrayData:x}");
        if (words.Length <= 10 && LoadsOffset(body, RuntimeLayout.FieldParent, 4) && LoadsOffset(body, RuntimeLayout.FieldOffset, 4) && calls.Length == 0)
            return (HelperKind.FieldAddress, null, $"读取 FieldInfo+0x{RuntimeLayout.FieldOffset:x} offset 加到对象地址（值类型扣除对象头）");
        return null;
    }

    private ulong? interfaceSlowPath;

    /// <summary>函数中以 ADRP+ADD 取得的 typeinfo 对象，其名称指针（+8）指向含 Il2CppExceptionWrapper 的字符串。</summary>
    private bool ThrowsIl2CppWrapper(ulong address)
    {
        var index = map.EntryIndex(address);
        if (index < 0) return false;
        foreach (var r in scan.Of(index))
            if (r.Kind == RefKind.Address && map.Image.ReadPointer(r.Target + 8) is { } name && CString(map.Image, name) is { } text
                && text.Contains("Il2CppExceptionWrapper", StringComparison.Ordinal))
                return true;
        return false;
    }

    private bool References(ulong address, string text)
    {
        var index = map.EntryIndex(address);
        if (index < 0) return false;
        foreach (var r in scan.Of(index))
            if (r.Kind == RefKind.Address && CString(map.Image, r.Target) is { } s && s.Contains(text, StringComparison.Ordinal)) return true;
        return false;
    }

    private RuntimeHelper Classify(ulong target, int calls, int slotCalls)
    {
        var function = map.At(target);
        if (function?.Region == CodeRegion.Plt)
            return new(target, HelperKind.Import, function.Import, "PLT 导入", calls);
        foreach (var (name, address) in map.Image.Exports)
            if (address == target)
            {
                var kind = ExportKinds.FirstOrDefault(e => e.Export == name).Kind;
                return new(target, kind == HelperKind.Unknown ? HelperKind.Export : kind, name, "导出地址", calls);
            }

        var chain = Chain(target).ToArray();
        foreach (var hop in chain.Skip(1))
            if (exportChains.TryGetValue(hop, out var e))
                return new(target, e.Kind, e.Kind == HelperKind.Export || e.Kind == HelperKind.VirtualMethodLookup ? e.Export : null,
                    $"跳板链 {string.Join(" → ", chain.TakeWhile(h => h != hop).Append(hop).Select(h => $"0x{h:x}"))} 与导出 {e.Export} 相交", calls);
        foreach (var hop in chain.Skip(1))
            if (map.At(hop) is { Region: CodeRegion.Plt } plt)
                return new(target, HelperKind.Import, plt.Import, $"跳板链到达 PLT 导入 {plt.Import}", calls);

        if (Structural(target, chain) is { } structural)
            return new(target, structural.Kind, structural.Detail, structural.Evidence, calls);

        var closure = Closure(target);
        if (function is { Size: <= ExceptionWrapperLimit * 4 } && closure.Any(HasTokenDecode) && slotCalls * 2 > calls)
            return new(target, HelperKind.InitMetadata, null,
                $"闭包内有令牌解码（UBFX/LSR #29），{slotCalls}/{calls} 个调用点前紧邻构造已解码的元数据槽位地址", calls);

        // 异常规则只用于小的包装函数：大函数的闭包会经由其中的抛出调用碰到异常名，那不代表它本身是抛出 helper。
        var exceptions = function is { Size: <= ExceptionWrapperLimit * 4 } ? closure.Select(ExceptionName).Where(n => n is not null).Distinct().ToArray() : [];
        if (exceptions.Length == 1)
        {
            var raises = closure.Any(f => exportChains.TryGetValue(f, out var e) && e.Kind == HelperKind.Raise);
            if (raises && CanReturn(target, 2))
            {
                var head = Words(target, 2).Select(x => x.Word).ToArray();
                // cbz x0, 抛出路径；ret
                if (exceptions[0] == "System.NullReferenceException" && head is [var cbz, var ret] && (cbz & 0xFF00001F) == 0xB4000000 && A64.IsRet(ret))
                    return new(target, HelperKind.NullCheck, null, "cbz x0 → 抛出 NullReferenceException，否则 ret（未内联的判空）", calls);
                return new(target, HelperKind.Unknown, null,
                    $"闭包内以 C 字符串构造 {exceptions[0]} 并到达 il2cpp_raise_exception，但函数可以返回（条件抛出）", calls);
            }
            return new(target, raises ? HelperKind.Throw : HelperKind.GetException, exceptions[0],
                $"闭包内以 C 字符串 (\"System\", \"{exceptions[0]![7..]}\") 构造异常{(raises ? "并到达 il2cpp_raise_exception" : "")}", calls);
        }
        return new(target, HelperKind.Unknown, null,
            exceptions.Length > 1 ? $"闭包内有多个异常名：{string.Join("、", exceptions)}" : "没有可用证据", calls);
    }

    /// <summary>函数可能返回：含 ret 或 BR，或以 B 跳出自身范围到可能返回的函数（depth 用尽时按可能返回处理）。</summary>
    private bool CanReturn(ulong address, int depth)
    {
        if (map.At(address) is not { } function) return true;
        foreach (var (pc, word) in Words(address, 256))
        {
            if (A64.IsRet(word) || A64.IsBr(word)) return true;
            if (A64.IsB(word) && A64.Imm26Target(word, pc) is var target && !function.Contains(target) && (depth == 0 || CanReturn(target, depth - 1))) return true;
        }
        return false;
    }

    /// <summary>从 address 出发，经直接调用与尾调用可达的小函数集合（含自身），深度与规模受限。</summary>
    private List<ulong> Closure(ulong address)
    {
        var result = new List<ulong>();
        var seen = new HashSet<ulong> { address };
        var frontier = new List<ulong> { address };
        for (var depth = 0; depth <= ClosureDepth && frontier.Count > 0; depth++)
        {
            var next = new List<ulong>();
            foreach (var f in frontier)
            {
                var index = map.EntryIndex(f);
                if (index < 0) continue;
                result.Add(f);
                if (map.Functions[index].Size > ClosureFunctionLimit * 4) continue;
                foreach (var r in scan.Of(index))
                    if (r.Kind is RefKind.Call or RefKind.TailCall && seen.Add(r.Target)) next.Add(r.Target);
            }
            frontier = next;
        }
        return result;
    }

    private bool HasTokenDecode(ulong address)
    {
        var function = map.At(address);
        if (function is null || function.Size > ClosureFunctionLimit * 4 * 4) return false;
        for (var pc = function.Start; pc < function.End; pc += 4)
            if (map.Word(pc) is { } w && (w & 0xFFFFFC00) is 0xD35D7C00 or 0xD35DFC00 or 0x531D7C00) return true;
        return false;
    }

    /// <summary>函数内以 ADRP+ADD 构造的两个只读 C 字符串 "System" 与 "...Exception" → "System.XxxException"。</summary>
    private string? ExceptionName(ulong address)
    {
        var index = map.EntryIndex(address);
        if (index < 0) return null;
        string? ns = null, name = null;
        foreach (var r in scan.Of(index))
        {
            if (r.Kind != RefKind.Address) continue;
            var text = CString(map.Image, r.Target);
            if (text == "System") ns = text;
            else if (text is not null && text.EndsWith("Exception", StringComparison.Ordinal) && text.All(char.IsAsciiLetterOrDigit)) name ??= text;
        }
        return ns is not null && name is not null ? $"{ns}.{name}" : null;
    }

    internal static string? CString(ImageDocument image, ulong address)
    {
        var section = image.SectionAt(address);
        if (section is null || section.Name != ".rodata") return null;
        var bytes = image.ReadUpTo(address, 128);
        var end = bytes.IndexOf((byte)0);
        if (end <= 0) return null;
        foreach (var b in bytes[..end]) if (b < 0x20 || b > 0x7e) return null;
        return Encoding.ASCII.GetString(bytes[..end]);
    }
}
