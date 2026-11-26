using System.Runtime.InteropServices;

namespace Cpp2CS.Tools.LiftCheck;

/// <summary>Unicorn 2 和 Capstone 5 的 C 接口。句柄与回调只在一次进程内使用。</summary>
internal static unsafe class NativeApi
{
    public static void Load(string unicorn, string capstone)
    {
        NativeLibrary.SetDllImportResolver(typeof(NativeApi).Assembly, (name, _, _) => name switch
        {
            "uc" => NativeLibrary.Load(unicorn),
            "cs" => NativeLibrary.Load(capstone),
            _ => 0
        });
    }
    [DllImport("uc")] public static extern uint uc_version(out uint major, out uint minor);
    [DllImport("uc")] public static extern int uc_open(int arch, int mode, out nint handle);
    [DllImport("uc")] public static extern int uc_close(nint handle);
    [DllImport("uc")] public static extern int uc_emu_start(nint handle, ulong start, ulong end, ulong timeout, nuint count);
    [DllImport("uc")] public static extern int uc_emu_stop(nint handle);
    [DllImport("uc")] public static extern int uc_mem_map(nint handle, ulong address, nuint size, uint permissions);
    [DllImport("uc")] public static extern int uc_mem_write(nint handle, ulong address, void* source, nuint size);
    [DllImport("uc")] public static extern int uc_mem_read(nint handle, ulong address, void* dest, nuint size);
    [DllImport("uc")] public static extern int uc_reg_read(nint handle, int reg, void* dest);
    [DllImport("uc")] public static extern int uc_reg_write(nint handle, int reg, void* value);
    [DllImport("uc")] public static extern int uc_hook_add(nint handle, out nuint hook, int kind, nint callback, nint data, ulong first, ulong last);
    [DllImport("cs")] public static extern int cs_version(out int major, out int minor);
    [DllImport("cs")] public static extern int cs_open(int arch, int mode, out nuint handle);
    [DllImport("cs")] public static extern int cs_close(ref nuint handle);
    [DllImport("cs")] public static extern int cs_option(nuint handle, int option, nuint value);
    [DllImport("cs")] public static extern nuint cs_disasm(nuint handle, byte* code, nuint size, ulong pc, nuint count, out nint instruction);
    [DllImport("cs")] public static extern void cs_free(nint instruction, nuint count);
    [DllImport("cs")] public static extern int cs_regs_access(nuint handle, nint insn, ushort* read, out byte nread, ushort* written, out byte nwritten);
    [DllImport("cs")] public static extern nint cs_reg_name(nuint handle, uint reg);
}

internal sealed record NativeInstruction(string Name, string Operands, UInt128 Read, UInt128 Written);

internal sealed unsafe class Disassembly : IDisposable
{
    nuint handle;
    readonly Dictionary<(ulong, uint), NativeInstruction> cache = [];
    readonly Dictionary<ushort, int> names = [];
    public Disassembly()
    {
        NativeApi.cs_version(out int major, out _);
        if (major != 5 || NativeApi.cs_open(1, 0, out handle) != 0 || NativeApi.cs_option(handle, 2, 3) != 0)
            throw new InvalidOperationException("需要 Capstone 5 的 AArch64 详细模式");
    }
    int Register(ushort reg)
    {
        if (names.TryGetValue(reg, out int existing)) return existing;
        var id = Marshal.PtrToStringAnsi(NativeApi.cs_reg_name(handle, reg))!;
        return names[reg] = RegisterName(id);
    }
    static int RegisterName(string id) => id switch
        {
            "fp" => 29,
            "lr" => 30,
            "nzcv" => 65,
            "sp" or "wsp" => 31,
            _ when id.Length > 1 && int.TryParse(id.AsSpan(1), out int n) && "xw".Contains(id[0]) => n,
            _ when id.Length > 1 && int.TryParse(id.AsSpan(1), out int n) && "bhsdqv".Contains(id[0]) => n + 32,
            _ => -1
        };
    public NativeInstruction At(ulong pc, uint word)
    {
        if (cache.TryGetValue((pc, word), out var instruction)) return instruction;
        if (NativeApi.cs_disasm(handle, (byte*)&word, 4, pc, 1, out nint raw) != 1) return new("?", "", 0, 0);
        string name = Marshal.PtrToStringAnsi(raw + 42)!, operands = Marshal.PtrToStringAnsi(raw + 74)!;
        ushort* reads = stackalloc ushort[64]; ushort* writes = stackalloc ushort[64];
        if (NativeApi.cs_regs_access(handle, raw, reads, out byte readCount, writes, out byte count) != 0)
            throw new InvalidOperationException("Capstone 未给出寄存器写集");
        UInt128 Mask(ushort* regs, int length)
        {
            UInt128 mask = 0;
            for (int j = 0; j < length; j++) if (Register(regs[j]) is int r && r >= 0) mask |= UInt128.One << r;
            return mask;
        }
        var read = Mask(reads, readCount);
        var written = Mask(writes, count);
        // DDI 0487：比较指令和丢弃结果的比较别名只写 NZCV。
        // Capstone 5 对 CMP 等别名把第一源寄存器列入写集。
        if (name is "cmp" or "cmn" or "tst" or "ccmp" or "ccmn" or "fcmp" or "fcmpe" or "fccmp" or "fccmpe")
        {
            var flags = UInt128.One << 65;
            read = (read | written) & ~flags;
            if (name is "ccmp" or "ccmn" or "fccmp" or "fccmpe") read |= flags;
            written = flags;
        }
        // DDI 0487，ADDS/SUBS：Rd 接收加减结果，NZCV 接收标志。Capstone 5 的立即数形式可只列出 NZCV。
        if (name is "adds" or "subs")
        {
            var fields = operands.Split(',', StringSplitOptions.TrimEntries);
            written = UInt128.One << 65;
            if (RegisterName(fields[0]) is int dest && dest >= 0) written |= UInt128.One << dest;
            read = 0;
            foreach (string source in fields.AsSpan(1))
                if (RegisterName(source) is int reg && reg >= 0) read |= UInt128.One << reg;
        }
        NativeApi.cs_free(raw, 1);
        return cache[(pc, word)] = new(name, operands, read, written);
    }
    public void Dispose() => NativeApi.cs_close(ref handle);
}
