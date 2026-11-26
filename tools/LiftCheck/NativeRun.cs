using System.Globalization;
using System.Runtime.InteropServices;
using Cpp2CS.Target;
using static Cpp2CS.Tools.LiftCheck.NativeApi;

namespace Cpp2CS.Tools.LiftCheck;

internal sealed unsafe class NativeRun : IDisposable
{
    readonly Image image;
    readonly Disassembly disassembly;
    readonly ulong seed;
    readonly Frame frame;
    readonly nint engine;
    readonly Trace trace = new();
    readonly byte[] pageBytes = new byte[4096];
    readonly HashSet<ulong> mapped = [];
    readonly List<Delegate> hooks = [];
    int steps, calls;
    readonly HashSet<uint> executed;
    readonly int budget;
    readonly TextWriter? instructions;
    readonly UndefinedSource? undefined;
    ulong defined = 0xfful | 1ul << 8 | 1ul << 31 | 0xfful << 32;
    ulong? resume;
    bool finished;
    ulong pc;
    int vectorTransfers;
    TraceEvent? lowHalf;
    delegate void Code(nint uc, ulong at, uint size, nint data);
    delegate void Data(nint uc, int type, ulong at, int size, long value, nint data);
    [return: MarshalAs(UnmanagedType.I1)]
    delegate bool Missing(nint uc, int type, ulong at, int size, long value, nint data);
    public NativeRun(Image image, Disassembly disassembly, Frame frame, ulong seed, int budget, HashSet<uint> executed, TextWriter? instructions = null, UndefinedSource? undefined = null)
    {
        this.undefined = undefined; this.instructions = instructions; this.budget = budget; this.executed = executed;
        this.image = image; this.disassembly = disassembly; this.frame = frame; this.seed = seed;
        if (uc_open(2, 0, out engine) != 0) throw new InvalidOperationException("Unicorn 无法创建 ARM64 CPU");
        Hook(4, (Code)OnCode);
        Hook(1 << 10 | 1 << 11, (Data)OnData);
        Hook(16 | 32 | 64, (Missing)OnMissing);
        // 地址空间末页的首次缺页可能让 Unicorn 的读钩子报告全一哨兵。预置该页保留原始访问地址。
        MapPage(ulong.MaxValue & ~4095ul);
        for (int r = 0; r <= 64; r++) Set(r, EnvironmentState.Register(seed, r));
        ulong flags = EnvironmentState.Mix(seed) & 0xf0000000;
        Status(uc_reg_write(engine, 3, &flags));
    }
    void Hook(int kind, Delegate hook)
    {
        hooks.Add(hook); Status(uc_hook_add(engine, out _, kind, Marshal.GetFunctionPointerForDelegate(hook), 0, 1, 0));
    }
    void Status(int status)
    {
        if (status != 0) { trace.Error ??= "Unicorn " + status; uc_emu_stop(engine); }
    }
    static int Id(int r) => r switch { 29 => 1, 30 => 2, 31 => 4, >= 32 and < 64 => 104 + r - 32, 64 => 262, _ => 199 + r };
    UInt128 Get(int r) { UInt128 v = 0; Status(uc_reg_read(engine, Id(r), &v)); return v; }
    void Set(int r, UInt128 value) => Status(uc_reg_write(engine, Id(r), &value));

    bool OnMissing(nint _, int type, ulong address, int size, long value, nint data)
        => MapPage(address & ~4095ul);

    bool MapPage(ulong page)
    {
        if (!mapped.Add(page)) { trace.Error = "重复缺页"; return false; }
        Status(uc_mem_map(engine, page, 4096, 7));
        if (trace.Error != null) return false;
        image.Page(page, pageBytes, seed);
        fixed (byte* bytes = pageBytes) Status(uc_mem_write(engine, page, bytes, 4096));
        return trace.Error == null;
    }
    void OnData(nint _, int type, ulong address, int size, long value, nint data)
    {
        // Unicorn 的 Q 寄存器访存通过两个 64 位回调报告。只在独立反汇编指定 Q 访问、
        // 同一指令、同一方向、两个地址严格相邻时组成一个架构访问；其余形态报错。
        if (vectorTransfers > 0)
        {
            string kind = type == 16 ? "读" : "写";
            if (size == 16 && type == 16 && lowHalf == null)
            { trace.Add(kind, address, 128); vectorTransfers--; return; }
            if (size != 8) { trace.Error = "Q 访存回调位宽"; uc_emu_stop(engine); return; }
            UInt128 bits = type == 16 ? 0 : (ulong)value;
            if (lowHalf is not { } lo) { lowHalf = new(kind, address, 64, bits); return; }
            if (lo.Kind != kind || address != lo.Address + 8)
            { trace.Error = "Q 访存回调地址或方向"; uc_emu_stop(engine); return; }
            trace.Add(kind, lo.Address, 128, lo.Value | (bits << 64)); lowHalf = null; vectorTransfers--; return;
        }
        if (type == 16) trace.Add("读", address, size * 8);
        else if (size <= 8) trace.Add("写", address, size * 8, (ulong)value & Bits.Mask(size * 8));
        else { trace.Error = "Unicorn 写钩子超过 64 位"; uc_emu_stop(engine); }
    }
    void EventCall(ulong target)
    {
        trace.Add("调用", target);
        for (int r = 0; r <= 8; r++) Arg(r);
        for (int r = 32; r < 40; r++) Arg(r);
        Arg(31);
        void Arg(int r)
        {
            if ((defined & (1ul << r)) != 0) trace.Add("实参", width: r >= 32 ? 128 : 64, value: Get(r), slot: r);
        }
        calls++;
        for (int r = 0; r < 64; r++)
        {
            if (r is 18 or >= 19 and <= 29 or 31) continue;
            var next = EnvironmentState.Register(seed, r, calls);
            if (r is >= 40 and < 48) next = (next & ~(UInt128)ulong.MaxValue) | (ulong)Get(r);
            Set(r, next);
        }
        ulong flags = EnvironmentState.Mix(seed + (uint)calls) & 0xf0000000;
        Status(uc_reg_write(engine, 3, &flags));
        defined = 3ul | 0xful << 32 | 1ul << 31;
    }
    void End(string kind)
    {
        trace.Add(kind); finished = true; uc_emu_stop(engine);
    }
    void Return(UInt128 target)
    {
        End("Return");
        void Slot(int r, int w, UInt128 v) => trace.Add("返回槽", width: w, value: v, slot: r);
        Slot(0, 64, Get(0)); Slot(1, 64, Get(1));
        for (int r = 32; r < 36; r++) Slot(r, 128, Get(r));
        Slot(30, 64, target); Slot(31, 64, Get(31));
        for (int r = 19; r <= 29; r++) Slot(r, 64, Get(r));
        for (int r = 40; r < 48; r++) Slot(r, 64, (ulong)Get(r));
    }
    static int BranchReg(string op) => op switch { "lr" => 30, "fp" => 29, "xzr" => -1, _ => int.Parse(op.AsSpan(1)) };
    void OnCode(nint _, ulong address, uint size, nint data)
    {
        if (vectorTransfers != 0 || lowHalf != null) { trace.Error = "Q 访存回调缺失"; uc_emu_stop(engine); return; }
        pc = trace.Pc = address;
        if (++steps > budget) { trace.Exhausted = true; uc_emu_stop(engine); return; }
        if (address < frame.Start || address >= frame.End)
        {
            var link = Get(30); EventCall(address); Return(link); return;
        }
        uint word = 0; Status(uc_mem_read(engine, address, &word, 4));
        executed.Add(word);
        var i = disassembly.At(address, word);
        undefined?.Record(pc, word, i, trace.Events.Count);
        if (instructions != null)
        {
            var decoded = Decoder.Decode(word);
            string inputs = "";
            if (decoded.Form is Form.Memory or Form.Pair or Form.Shifted or Form.Extended)
                inputs = $" N={Get(decoded.N):x} M={Get(decoded.M):x}";
            instructions.WriteLine($"{steps}\t{trace.Events.Count}\t{pc:x}\t{i.Name} {i.Operands}{inputs}");
        }
        if (i.Operands.StartsWith('q')) vectorTransfers = i.Name switch
        {
            "ldp" or "stp" or "ldnp" or "stnp" => 2,
            "ldr" or "str" or "ldur" or "stur" => 1,
            _ => 0
        };
        switch (i.Name)
        {
            case "bl":
            case "blr":
                ulong target = i.Name == "bl" ? ParseAddress(i.Operands) : BranchReg(i.Operands) is int r && r >= 0 ? (ulong)Get(r) : 0;
                EventCall(target);
                if (pc + 4 == frame.End) End("NoReturn");
                else { resume = pc + 4; uc_emu_stop(engine); }
                break;
            case "ret":
                Return(i.Operands.Length == 0 ? Get(30) : BranchReg(i.Operands) is int ret && ret >= 0 ? Get(ret) : 0); break;
            case "brk": case "udf": End("Trap"); break;
            default: defined |= (ulong)i.Written; break;
        }
    }
    static ulong ParseAddress(string text)
    {
        var value = text.AsSpan().TrimStart('#');
        return value.StartsWith("0x") ? ulong.Parse(value[2..], NumberStyles.HexNumber) : ulong.Parse(value);
    }
    public (Trace Trace, UInt128[] Registers) Step(ulong pc)
    {
        int status = uc_emu_start(engine, pc, pc + 4, 0, 1);
        if (status != 0) trace.Error ??= "Unicorn " + status;
        var row = new UInt128[Abi.Count];
        for (int r = 0; r <= Abi.Thread; r++) row[r] = Get(r);
        ulong flags = 0;
        Status(uc_reg_read(engine, 3, &flags));
        for (int r = Abi.Negative; r <= Abi.Overflow; r++) row[r] = (flags >> (31 - r + Abi.Negative)) & 1;
        return (trace, row);
    }

    public Trace Run(ulong entry)
    {
        resume = entry;
        while (!finished && trace.Error == null && resume.HasValue)
        {
            ulong start = resume.Value; resume = null;
            int status = uc_emu_start(engine, start, ulong.MaxValue, 0, 0);
            if (status != 0) { trace.Error ??= "Unicorn " + status; trace.Diagnostic ??= $"PC {pc:x}"; }
        }
        if (!finished && !trace.Exhausted && trace.Error == null) trace.Error = "原生执行无结局";
        return trace;
    }
    public void Dispose() { uc_close(engine); GC.KeepAlive(hooks); }
}
