using System.Buffers.Binary;
using Cpp2CS.Native.Images;
using Cpp2CS.Targets.Elf;

namespace Cpp2CS.Tests;

internal static class ImageChecks
{
    public const string Command = "image";
    public static int Run()
    {
        var a = new Assertions();
        foreach (var machine in new ushort[] { 183, 62 })
        {
            var exceptionBytes = WithExceptions(machine);
            var exceptionImage = ElfImage.Parse(exceptionBytes);
            a.True(exceptionImage.Functions.Any(f => f.Evidence.HasFlag(FunctionEvidence.UnwindTable) && f.Start == 0x300 && f.Length == 16), "展开记录与非零基址");
            a.True(exceptionImage.TryRegions is [{ Start: 0x300, Length: 4, Handler: 0x308 }] && exceptionImage.TryRegions[0].Clauses is [{ Kind: ClauseKind.CatchAll }], "异常区间与 catch-all");
            exceptionBytes[0x399] = 0x7f;
            var specification = ElfImage.Parse(exceptionBytes);
            a.True(specification.TryRegions[0].Clauses is [{ Kind: ClauseKind.ExceptionSpecification, Matches.Length: 0 }], "空异常规格");
            exceptionBytes = WithExceptions(machine);
            exceptionBytes[0x39a] = 0x7f;
            Reject(a, () => ElfImage.Parse(exceptionBytes), "异常动作链成环");
            exceptionBytes = WithExceptions(machine); exceptionBytes[0x394] = 3;
            Reject(a, () => ElfImage.Parse(exceptionBytes), "异常调用表截断");
            exceptionBytes = WithExceptions(machine); Put(exceptionBytes, 0x36c, 0, 4);
            var emptyRange = ElfImage.Parse(exceptionBytes);
            a.True(emptyRange.Diagnostics.Length == 1 && !emptyRange.Functions.Any(f => f.Evidence.HasFlag(FunctionEvidence.UnwindTable)), "零长度展开记录只报告诊断");
            var bytes = Minimal(machine);
            IImage image = ElfImage.Parse(bytes);
            a.True(image.FunctionSymbols is [{ Name: "function", Offset: 0x300, Size: 16 }], "动态符号回退只含已定义函数，偏移相对基址");
            var zeroSymbol = Minimal(machine); Put(zeroSymbol, 0x140, 0, 8);
            a.True(ElfImage.Parse(zeroSymbol).FunctionSymbols is [{ Size: 0 }], "零大小符号仍保留入口");
            a.True(image.PreferredBase == 0x400000 && image.PointerWidth == 8 && image.ByteOrder == ByteOrder.LittleEndian, "头属性与相对基址");
            a.True(image.Query(0x600).Storage == StorageKind.ZeroFill && image.Query(0x800).Storage == StorageKind.Unmapped, "零填充与未映射");
            a.True(image.IsExecutable(0, 0x800) && image.IsWritable(0x600, 0x200) && !image.IsExecutable(0x7ff, 2), "区间权限");
            a.True(image.ReadUnsigned(0x600, 8) == 0 && image.ReadUnsigned(0x5ff, 2) == 0, "零填充及跨边界读取");
            a.True(image.Relocations.Count == 2 && image.ReadPointer(0x200) == new PointerTarget.Internal(0x300), "相对重定位与基址归一化");
            a.True(image.ReadPointer(0x208) is PointerTarget.Import { Symbol.Name: "external", Addend: 3 }, "导入槽解析及加数");
            a.True(image.Functions.Any(f => f.Start == 0x300 && f.Length == 16 && f.Evidence.HasFlag(FunctionEvidence.SymbolTable)), "符号函数边界");
            a.True(image.Exports.Any(e => e.Name == "function" && e.Target == new PointerTarget.Internal(0x300)), "导出符号");
            a.True(image.ReadPointer(0x1f8) is PointerTarget.Null && image.ReadPointer(0x210) is PointerTarget.Null, "首尾相邻槽不重叠");
            a.True(image.ReadPointer(0x1f9) is PointerTarget.Unknown && image.ReadPointer(0x204) is PointerTarget.Unknown && image.ReadPointer(0x20f) is PointerTarget.Unknown, "首部、相邻中间与尾部重叠");
            var changed = Minimal(machine); Put(changed, 0x250, 0x400800, 8);
            var tail = ElfImage.Parse(changed);
            a.True(tail.ReadPointer(0x200) == new PointerTarget.Internal(0x800) && tail.Query(0x800).Storage == StorageKind.Unmapped, "尾后目标与可读性分离");
            changed = Minimal(machine); Put(changed, 0x250, 0x400900, 8);
            a.True(ElfImage.Parse(changed).ReadPointer(0x200) == new PointerTarget.Internal(0x900), "未映射目标保留偏移");
            changed = Minimal(machine); Put(changed, 0x250, 0, 8);
            a.True(ElfImage.Parse(changed).ReadPointer(0x200) is PointerTarget.Internal, "重定位目标零地址不误判为空槽");
            changed = Minimal(machine); Put(changed, 0x220, 0x400300, 8);
            a.True(ElfImage.Parse(changed).ReadPointer(0x220) is PointerTarget.NotPointer, "位置无关非零槽没有指针证据");
            Put(changed, 0x4e0, 0, 8);
            a.True(ElfImage.Parse(changed).ReadPointer(0x220) is PointerTarget.NotPointer, "无重定位表的 ET_DYN 不猜指针");
            Put(changed, 16, 2, 2);
            a.True(ElfImage.Parse(changed).ReadPointer(0x220) == new PointerTarget.Internal(0x300), "固定基址无重定位映像读取原始地址");
            var merged = exceptionImage.Functions.Single(f => f.Start == 0x300);
            a.True(merged.Evidence == (FunctionEvidence.UnwindTable | FunctionEvidence.SymbolTable) && merged.Extents is [{ Length: 16 }], "同起点同长度合并证据");
            changed = WithExceptions(machine); Put(changed, 0x140, 24, 8);
            var conflict = ElfImage.Parse(changed);
            a.True(conflict.Functions.Single(f => f.Start == 0x300).Extents.Length == 2 && conflict.Diagnostics.Any(d => d.Contains("证据冲突", StringComparison.Ordinal)), "不同长度保留证据并诊断");
            changed = Minimal(machine); Put(changed, 0x258, 0x400204, 8);
            var overlap = ElfImage.Parse(changed);
            a.True(overlap.ReadPointer(0x200) is PointerTarget.Unknown && overlap.ReadPointer(0x204) is PointerTarget.Unknown, "重叠记录不按精确命中掩盖冲突");
            changed = Minimal(machine); Put(changed, 0x240, 0x4001f8, 8); Put(changed, 0x248, machine == 183 ? 1031UL : 36UL, 8);
            var wide = ElfImage.Parse(changed);
            a.True(wide.ReadPointer(0x1f8) is PointerTarget.Unknown && wide.ReadPointer(0x200) is PointerTarget.Unknown
                && wide.ReadPointer(0x208) is PointerTarget.Import && wide.ReadPointer(0x1f0) is PointerTarget.Null, "宽重定位的内部与相邻边界");
            changed = Minimal(machine); Put(changed, 0x258, 0x400200, 8);
            Reject(a, () => ElfImage.Parse(changed), "重复起点重定位拒绝");
            foreach (var (at, value) in new[] { (4, 1), (5, 2), (18, 40) })
            {
                changed = Minimal(machine); Put(changed, at, (ulong)value, at == 18 ? 2 : 1);
                Reject(a, () => ElfImage.Parse(changed), "不支持的位数、字节序或机器明确拒绝");
            }
            bytes[0x200] = 255;
            a.True(image.ReadUnsigned(0x200, 1) == 0, "输入复制后不可变");
            Parallel.For(0, 32, _ => { if (image.ReadPointer(0x200) != new PointerTarget.Internal(0x300)) throw new InvalidOperationException(); });
            foreach (var cut in new[] { 0, 4, 63, 100, 0x500 })
                Reject(a, () => ElfImage.Parse(bytes.AsSpan(0, cut)), "截断输入");
            var malformed = Minimal(machine); Put(malformed, 96, ulong.MaxValue, 8);
            Reject(a, () => ElfImage.Parse(malformed), "段长度越界");
            malformed = Minimal(machine); Put(malformed, 0x240 + 8, 0xffff00000001, 8);
            Reject(a, () => ElfImage.Parse(malformed), "符号索引越界或未支持重定位");
            Reject(a, () => image.ReadUnsigned(0x800, 8), "未映射读取");
        }
        return a.Finish("映像快速检查");
    }
    private static void Reject(Assertions a, Action action, string name)
    {
        try { action(); a.True(false, name); }
        catch (InvalidDataException) { a.True(true, name); }
        catch (NotSupportedException) { a.True(true, name); }
    }
    private static void Put(byte[] b, int at, ulong value, int width)
    {
        for (var i = 0; i < width; i++) b[at + i] = (byte)(value >> (i * 8));
    }
    private static byte[] WithExceptions(ushort machine)
    {
        var b = Minimal(machine);
        void W(int at, ulong value, int width = 8) => Put(b, at, value, width);
        W(56, 2, 2); W(120, 0x6474e550, 4); W(128, 0x320); W(136, 0x400320); W(152, 20); W(160, 20);
        W(0x320, 0x3b031b01, 4); W(0x324, 0x1c, 4); W(0x328, 1, 4);
        W(0x32c, unchecked((uint)-32), 4); W(0x330, 0x40, 4);
        W(0x340, 15, 4); b[0x348] = 1;
        b[0x349] = (byte)'z'; b[0x34a] = (byte)'L'; b[0x34b] = (byte)'R';
        b[0x34d] = 1; b[0x34e] = 0x78; b[0x34f] = 16; b[0x350] = 2; b[0x351] = 0x1b; b[0x352] = 0x1b;
        W(0x360, 17, 4); W(0x364, 0x24, 4); W(0x368, unchecked((uint)-104), 4); W(0x36c, 16, 4);
        b[0x370] = 4; W(0x371, 0x1f, 4);
        b[0x390] = 0xff; b[0x392] = 0x15; b[0x393] = 1; b[0x394] = 4;
        b[0x396] = 4; b[0x397] = 8; b[0x398] = 1; b[0x399] = 1;
        return b;
    }
    private static byte[] Minimal(ushort machine)
    {
        var b = new byte[0x600];
        void W(int at, ulong value, int width = 8) => Put(b, at, value, width);
        W(0, 0x464c457f, 4); b[4] = 2; b[5] = 1; b[6] = 1;
        W(16, 3, 2); W(18, machine, 2); W(20, 1, 4); W(32, 64); W(40, 0x400);
        W(52, 64, 2); W(54, 56, 2); W(56, 1, 2); W(58, 64, 2); W(60, 4, 2);
        W(64, 1, 4); W(68, 7, 4); W(80, 0x400000); W(96, 0x600); W(104, 0x800); W(112, 0x1000);
        var names = System.Text.Encoding.UTF8.GetBytes("\0external\0function\0"); names.CopyTo(b, 0x180);
        W(0x118, 1, 4); b[0x11c] = 0x12;
        W(0x130, 10, 4); b[0x134] = 0x12; W(0x136, 1, 2); W(0x138, 0x400300); W(0x140, 16);
        W(0x240, 0x400200); W(0x248, machine == 183 ? 1027UL : 8UL); W(0x250, 0x400300);
        W(0x258, 0x400208); W(0x260, (1UL << 32) | (machine == 183 ? 1025UL : 6UL)); W(0x268, 3);
        W(0x444, 3, 4); W(0x458, 0x180); W(0x460, (ulong)names.Length);
        W(0x484, 11, 4); W(0x498, 0x100); W(0x4a0, 72); W(0x4a8, 1, 4); W(0x4b8, 24);
        W(0x4c4, 4, 4); W(0x4d8, 0x240); W(0x4e0, 48); W(0x4e8, 2, 4); W(0x4f8, 24);
        return b;
    }
}

internal static class ImageCorpusChecks
{
    public const string Command = "image-corpus";
    public static int Run()
    {
        var root = Environment.GetEnvironmentVariable("CPP2CS_CORPUS");
        if (string.IsNullOrEmpty(root)) { Console.WriteLine("跳过：未提供语料"); return 0; }
        var a = new Assertions();
        foreach (var target in new[] { "arm64-v8a", "x86_64" })
        {
            var directory = Path.Combine(root, "artifacts", "il2cppOutput", "build", target);
            var image = ElfImage.Load(Path.Combine(directory, "libil2cpp.so"));
            var namedImage = ElfImage.Load(Path.Combine(directory, "libil2cpp.dbg.so"));
            a.True(!namedImage.FunctionSymbols.IsEmpty, "语料函数符号非空");
            var exported = namedImage.Exports.Single(e => e.Name == "il2cpp_init");
            a.True(exported.Target is PointerTarget.Internal entry && namedImage.FunctionSymbols.Any(s => s.Name == exported.Name && s.Offset == entry.Offset), "按符号名找到已知导出函数");
            var symbolFunctions = ReadSymbolRanges(Path.Combine(directory, "libil2cpp.sym.so"));
            a.True(image.PreferredBase == 0 && image.PointerWidth == 8, "语料基址和指针宽度");
            a.True(image.Ranges.Any(r => r.Executable) && image.Ranges.Any(r => r.Writable) && image.Ranges.Any(r => r.Storage == StorageKind.ZeroFill), "语料范围种类齐全");
            foreach (var r in image.Relocations.Where(r => r.Kind == RelocationKind.Pointer))
            {
                a.True(r.Target is not PointerTarget.Unknown, "指针重定位目标可解析");

            }
            ImageMeasurements.Report(image, a);
            var byStart = image.Functions.GroupBy(f => f.Start).ToDictionary(g => g.Key, g => g.Max(f => f.Length));
            var covered = symbolFunctions.Count(f => byStart.TryGetValue(f.Start, out var length) && length >= f.Length);
            var shorter = symbolFunctions.Count(f => byStart.TryGetValue(f.Start, out var length) && length < f.Length);
            var missing = symbolFunctions.Length - covered - shorter;
            var starts = byStart.Keys.Order().ToArray();
            var ends = starts.Select(start => start + byStart[start]).ToArray();
            for (var i = 1; i < ends.Length; i++) ends[i] = Math.Max(ends[i], ends[i - 1]);
            foreach (var r in image.TryRegions)
            {
                a.True(r.Handler is not { } h || image.IsExecutable(h), "处理入口可执行");
                var index = Array.BinarySearch(starts, r.Start);
                if (index < 0) index = ~index - 1;
                a.True(index >= 0 && r.Start + r.Length <= ends[index], "异常区间属于函数范围");
            }
            Console.WriteLine($"{target}: base=0x{image.PreferredBase:x}, pointer={image.PointerWidth}, ranges={image.Ranges.Length}, executableBytes={image.Ranges.Where(r => r.Executable).Sum(r => (long)r.Length)}, writableBytes={image.Ranges.Where(r => r.Writable).Sum(r => (long)r.Length)}, zeroBytes={image.Ranges.Where(r => r.Storage == StorageKind.ZeroFill).Sum(r => (long)r.Length)}");
            Console.WriteLine($"重定位={image.Relocations.Count}: {string.Join(", ", image.Relocations.GroupBy(r => r.Kind).Select(g => $"{g.Key}={g.Count()}"))}; internal={image.Relocations.Count(r => r.Target is PointerTarget.Internal)}, import={image.Relocations.Count(r => r.Target is PointerTarget.Import)}");
            Console.WriteLine($"函数范围={image.Functions.Length}, 符号函数={symbolFunctions.Length}, 同起点覆盖={covered}, 同起点较短={shorter}, 缺少起点={missing}; try={image.TryRegions.Length}, 有处理入口={image.TryRegions.Count(r => r.Handler != null)}, 子句={image.TryRegions.Sum(r => r.Clauses.Length)}, 诊断={image.Diagnostics.Length}");
            foreach (var group in image.Diagnostics.GroupBy(d => d.Contains("长度为零", StringComparison.Ordinal) ? "零长度展开记录" : d)) Console.WriteLine($"{group.Key}: {group.Count()}");
        }
        return a.Finish("映像语料检查");
    }

    // 独立读取符号真值；分离符号文件的装载段不包含可执行映像，不能作为 IImage 载入。
    private static FunctionRange[] ReadSymbolRanges(string path)
    {
        var bytes = File.ReadAllBytes(path);
        ulong U64(int at) => BinaryPrimitives.ReadUInt64LittleEndian(bytes.AsSpan(at, 8));
        uint U32(int at) => BinaryPrimitives.ReadUInt32LittleEndian(bytes.AsSpan(at, 4));
        ushort U16(int at) => BinaryPrimitives.ReadUInt16LittleEndian(bytes.AsSpan(at, 2));
        if (U32(0) != 0x464c457f || bytes[4] != 2 || bytes[5] != 1 || U16(58) != 64) throw new InvalidDataException("符号真值必须为 ELF64 little-endian");
        var sections = checked((int)U64(40));
        var result = new List<FunctionRange>();
        for (var i = 0; i < U16(60); i++)
        {
            var s = sections + i * 64;
            if (U32(s + 4) != 2) continue;
            var offset = checked((int)U64(s + 24));
            var size = checked((int)U64(s + 32));
            if (U64(s + 56) != 24 || size % 24 != 0) throw new InvalidDataException("符号真值表长度不正确");
            for (var p = offset; p < offset + size; p += 24)
                if ((bytes[p + 4] & 15) == 2 && U16(p + 6) is > 0 and < 0xff00 && U64(p + 16) != 0)
                    result.Add(new(U64(p + 8), U64(p + 16), FunctionEvidence.SymbolTable));
        }
        if (result.Count == 0) throw new InvalidDataException("缺少函数符号真值");
        return result.ToArray();
    }
}

internal static class ImageMeasurements
{
    internal static void Report(IImage image, Assertions a)
    {
        long mapped = 0, tail = 0, other = 0;
        var ends = image.Ranges.Select(r => r.Start + r.Length).ToHashSet();
        foreach (var r in image.Relocations)
        {
            if (r.Target is not PointerTarget.Internal t) continue;
            if (image.Query(t.Offset).Storage != StorageKind.Unmapped) mapped++;
            else if (ends.Contains(t.Offset)) tail++;
            else { other++; Console.WriteLine($"其他目标：slot=0x{r.Offset:x}, target=0x{t.Offset:x}"); }
        }
        Console.WriteLine($"目标分类：已映射={mapped}, 尾后={tail}, 其他={other}");
        a.True(other == 0, "内部重定位目标仅为已映射或尾后地址");
    }
}

internal static class ImageSampleChecks
{
    public const string Command = "image-samples";
    public static int Run()
    {
        var root = Environment.GetEnvironmentVariable("CPP2CS_SAMPLES");
        if (string.IsNullOrEmpty(root)) { Console.WriteLine("跳过：未提供样本"); return 0; }
        var a = new Assertions();
        foreach (var file in Directory.EnumerateFiles(root, "*.so", SearchOption.AllDirectories).Order())
        {
            Console.WriteLine($"样本：{file}");
            var watch = System.Diagnostics.Stopwatch.StartNew();
            IImage image;
            try { image = ElfImage.Load(file); }
            catch (NotSupportedException error)
            {
                Console.WriteLine($"不支持：{error.Message}; elapsed={watch.Elapsed.TotalSeconds:F3}s");
                continue;
            }
            watch.Stop();
            Console.WriteLine($"load={watch.Elapsed.TotalSeconds:F3}s, ranges={image.Ranges.Length}, relocations={image.Relocations.Count}, functions={image.Functions.Length}, try={image.TryRegions.Length}, diagnostics={image.Diagnostics.Length}");
            var counts = new Dictionary<RelocationKind, long>();
            foreach (var relocation in image.Relocations) counts[relocation.Kind] = counts.GetValueOrDefault(relocation.Kind) + 1;
            Console.WriteLine(string.Join(", ", counts.Select(g => $"{g.Key}={g.Value}")));
            ImageMeasurements.Report(image, a);
            a.True(watch.Elapsed < TimeSpan.FromMinutes(1), "载入少于一分钟");
        }
        return a.Finish("映像样本检查");
    }
}
