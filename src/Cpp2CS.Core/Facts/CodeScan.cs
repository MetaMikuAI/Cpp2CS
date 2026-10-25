namespace Cpp2CS.Facts;

public enum RefKind : byte
{
    /// <summary>BL：直接调用。</summary>
    Call,
    /// <summary>跳出所在函数的 B：尾调用。</summary>
    TailCall,
    /// <summary>ADRP + ADD：构造出的地址（代码指针、数据地址）。</summary>
    Address,
    /// <summary>ADRP + LDR（无符号偏移）：从该地址读取。</summary>
    Load,
    /// <summary>ADRP + STR（无符号偏移）：向该地址写入。</summary>
    Store,
    /// <summary>ADR：PC 相对地址。</summary>
    Adr,
}

/// <summary>函数内的一处引用。Size 只对 Load/Store 有意义（访问宽度）。</summary>
public readonly record struct CodeRef(ulong Site, ulong Target, RefKind Kind, byte Size);

/// <summary>函数内的统计：间接调用、间接跳转、返回；以及违反边界不变式的分支。</summary>
public readonly record struct FunctionShape(int IndirectCalls, int IndirectJumps, int Returns, int EscapingConditionals);

/// <summary>
/// 逐函数扫描代码引用。ADRP 配对：记住每个寄存器最近一次 ADRP 的页地址，
/// 被 ADD/LDR/STR 以该寄存器为基址使用时生成引用；寄存器被改写或距离超过 64 条指令后失效。
/// 这是事实层的普查扫描，不替代控制流与数据流分析；配对结果另由槽位解码、入口落点等不变式核验。
/// </summary>
public sealed class CodeScan
{
    private const int AdrpWindow = 64;
    private readonly CodeRef[] refs;
    private readonly int[] offsets;
    private readonly FunctionShape[] shapes;

    public CodeMap Map { get; }
    public IReadOnlyList<CodeRef> All => refs;
    public IReadOnlyList<(ulong Site, ulong Target)> EscapingConditionals { get; }

    private CodeScan(CodeMap map, CodeRef[] refs, int[] offsets, FunctionShape[] shapes, List<(ulong, ulong)> escaping)
    {
        Map = map;
        this.refs = refs;
        this.offsets = offsets;
        this.shapes = shapes;
        EscapingConditionals = escaping;
    }

    public ReadOnlySpan<CodeRef> Of(int function) => refs.AsSpan(offsets[function], offsets[function + 1] - offsets[function]);

    public FunctionShape ShapeOf(int function) => shapes[function];

    public static CodeScan Run(CodeMap map)
    {
        var functions = map.Functions;
        var offsets = new int[functions.Count + 1];
        var shapes = new FunctionShape[functions.Count];
        var parts = new List<CodeRef>[functions.Count];
        var escaping = new List<(ulong, ulong)>[functions.Count];
        Parallel.For(0, functions.Count, new ParallelOptions { MaxDegreeOfParallelism = Environment.ProcessorCount }, i =>
        {
            var (list, shape, escapes) = ScanFunction(map, functions[i]);
            parts[i] = list;
            shapes[i] = shape;
            escaping[i] = escapes;
        });
        var total = 0;
        for (var i = 0; i < parts.Length; i++) { offsets[i] = total; total += parts[i].Count; }
        offsets[^1] = total;
        var refs = new CodeRef[total];
        for (var i = 0; i < parts.Length; i++) parts[i].CopyTo(refs, offsets[i]);
        return new(map, refs, offsets, shapes, escaping.Where(e => e is not null).SelectMany(e => e).ToList());
    }

    private static (List<CodeRef>, FunctionShape, List<(ulong, ulong)>) ScanFunction(CodeMap map, CodeFunction function)
    {
        var list = new List<CodeRef>();
        var escaping = new List<(ulong, ulong)>();
        int indirectCalls = 0, indirectJumps = 0, returns = 0;
        Span<ulong> page = stackalloc ulong[32];
        Span<ulong> since = stackalloc ulong[32];
        Span<bool> live = stackalloc bool[32];
        if (function.Region == CodeRegion.Plt) return (list, default, escaping);
        for (var pc = function.Start; pc + 4 <= function.End; pc += 4)
        {
            if (map.Word(pc) is not { } w) break;
            for (var r = 0; r < 32; r++) if (live[r] && pc - since[r] > AdrpWindow * 4UL) live[r] = false;
            if (A64.IsBl(w)) { list.Add(new(pc, A64.Imm26Target(w, pc), RefKind.Call, 0)); Clobber(live); continue; }
            if (A64.IsB(w))
            {
                var target = A64.Imm26Target(w, pc);
                if (!function.Contains(target)) list.Add(new(pc, target, RefKind.TailCall, 0));
                continue;
            }
            if (A64.ConditionalTarget(w, pc) is { } conditional)
            {
                if (!function.Contains(conditional)) escaping.Add((pc, conditional));
                continue;
            }
            if (A64.IsBlr(w)) { indirectCalls++; Clobber(live); continue; }
            if (A64.IsBr(w)) { indirectJumps++; continue; }
            if (A64.IsRet(w)) { returns++; continue; }
            if (A64.IsAdr(w)) { list.Add(new(pc, A64.AdrTarget(w, pc), RefKind.Adr, 0)); live[A64.Rd(w)] = false; continue; }
            if (A64.IsAdrp(w))
            {
                var rd = A64.Rd(w);
                page[rd] = A64.AdrpPage(w, pc);
                since[rd] = pc;
                live[rd] = true;
                continue;
            }
            var rn = A64.Rn(w);
            if (A64.IsAddImmediate64(w) && live[rn])
                list.Add(new(pc, page[rn] + A64.AddImmediate(w), RefKind.Address, 0));
            else if (A64.IsUnsignedOffsetAccess(w) && live[rn])
                list.Add(new(pc, page[rn] + A64.AccessOffset(w), A64.IsStore(w) ? RefKind.Store : RefKind.Load, (byte)A64.AccessSize(w)));
            Kill(w, live);
        }
        return (list, new(indirectCalls, indirectJumps, returns, escaping.Count), escaping);
    }

    /// <summary>调用之后调用者保存之外的寄存器（x0–x18、x30）不再保有 ADRP 页地址。</summary>
    private static void Clobber(Span<bool> live)
    {
        for (var r = 0; r <= 18; r++) live[r] = false;
        live[30] = false;
    }

    private static void Kill(uint w, Span<bool> live)
    {
        if (A64.MayWriteRd(w)) live[A64.Rd(w)] = false;
        // LDP 的第二个目的寄存器（位 10–14）
        if ((w & 0x3A000000) == 0x28000000 && ((w >> 22) & 1) != 0) live[(int)((w >> 10) & 31)] = false;
        // 前/后变址写回基址寄存器
        var pair = (w & 0x3A000000) == 0x28000000 && ((w >> 23) & 1) != 0;
        var single = (w & 0x3B200400) == 0x38000400;
        if (pair || single) live[A64.Rn(w)] = false;
    }
}
