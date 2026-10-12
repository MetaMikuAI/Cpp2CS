using System.Runtime.InteropServices;

namespace Cpp2CS.Native;

public sealed record Operand(int Kind, string? Register, long Immediate, string? Base, string? Index, int Displacement, uint Shift, uint ShiftKind, uint Extend)
{
    public double? FloatingPoint { get; init; }
}
public sealed record Instruction(ulong Address, string Mnemonic, string Display, Operand[] Operands, bool Writeback, bool PostIndex, string Bytes)
{
    public int ConditionCode { get; init; }
    public string[] Reads { get; init; } = [];
    public string[] Writes { get; init; } = [];
}

// Capstone 5 x64 C ABI。读取结构化操作数，op_str 仅用于诊断。
public sealed class Arm64Decoder : IDisposable
{
    [UnmanagedFunctionPointer(CallingConvention.Cdecl)] private delegate int Version(out int major, out int minor);
    [UnmanagedFunctionPointer(CallingConvention.Cdecl)] private delegate int Open(int arch, int mode, out nuint handle);
    [UnmanagedFunctionPointer(CallingConvention.Cdecl)] private delegate int Option(nuint handle, int type, nuint value);
    [UnmanagedFunctionPointer(CallingConvention.Cdecl)] private delegate nuint Disasm(nuint handle, byte[] bytes, nuint size, ulong address, nuint count, out nint instructions);
    [UnmanagedFunctionPointer(CallingConvention.Cdecl)] private delegate nint RegName(nuint handle, uint register);
    [UnmanagedFunctionPointer(CallingConvention.Cdecl)] private delegate void Free(nint instructions, nuint count);
    [UnmanagedFunctionPointer(CallingConvention.Cdecl)] private delegate int Close(ref nuint handle);
    [UnmanagedFunctionPointer(CallingConvention.Cdecl)] private delegate int Registers(nuint handle, nint instruction, [Out] ushort[] reads, out byte readCount, [Out] ushort[] writes, out byte writeCount);
    private readonly nint library;
    private nuint handle;
    private readonly Disasm disasm;
    private readonly RegName regName;
    private readonly Free free;
    private readonly Close close;
    private readonly Registers registers;
    public Arm64Decoder(string libraryPath)
    {
        if (IntPtr.Size != 8) throw new PlatformNotSupportedException("Capstone 适配器需要 64 位进程");
        library = NativeLibrary.Load(libraryPath);
        Fn<Version>("cs_version")(out var major, out _);
        if (major != 5) throw new InvalidOperationException("当前适配器仅支持 Capstone 5");
        if (Fn<Open>("cs_open")(1, 0, out handle) != 0 || Fn<Option>("cs_option")(handle, 2, 3) != 0)
            throw new InvalidOperationException("Capstone ARM64 初始化失败");
        disasm = Fn<Disasm>("cs_disasm"); regName = Fn<RegName>("cs_reg_name"); free = Fn<Free>("cs_free"); close = Fn<Close>("cs_close");
        registers = Fn<Registers>("cs_regs_access");
    }
    private T Fn<T>(string name) where T : Delegate => Marshal.GetDelegateForFunctionPointer<T>(NativeLibrary.GetExport(library, name));
    private string? Name(int id) => id == 0 ? null : Marshal.PtrToStringAnsi(regName(handle, (uint)id));
    public Instruction[] Decode(byte[] bytes, ulong address)
    {
        var count = disasm(handle, bytes, (nuint)bytes.Length, address, 0, out var pointer);
        var output = new List<Instruction>();
        for (nuint n = 0; n < count; n++)
        {
            var p = pointer + checked((int)n * 248);
            var detail = Marshal.ReadIntPtr(p, 240) + 96;
            var operands = new List<Operand>();
            for (var i = 0; i < Marshal.ReadByte(detail, 7); i++)
            {
                var op = detail + 8 + i * 56;
                var kind = Marshal.ReadInt32(op, 20);
                operands.Add(new(kind, kind == 1 ? Name(Marshal.ReadInt32(op, 32)) : null,
                    kind == 2 ? Marshal.ReadInt64(op, 32) : 0,
                    kind == 3 ? Name(Marshal.ReadInt32(op, 32)) : null,
                    kind == 3 ? Name(Marshal.ReadInt32(op, 36)) : null,
                    kind == 3 ? Marshal.ReadInt32(op, 40) : 0,
                    (uint)Marshal.ReadInt32(op, 12), (uint)Marshal.ReadInt32(op, 8), (uint)Marshal.ReadInt32(op, 16))
                    { FloatingPoint = kind == 4 ? BitConverter.Int64BitsToDouble(Marshal.ReadInt64(op, 32)) : null });
            }
            var size = Marshal.ReadInt16(p, 16);
            var raw = new byte[size]; Marshal.Copy(p + 18, raw, 0, size);
            var reads = new ushort[64]; var writes = new ushort[64];
            if (registers(handle, p, reads, out var nr, writes, out var nw) != 0) throw new InvalidDataException("缺少指令寄存器访问记录");
            var mnemonic = Marshal.PtrToStringAnsi(p + 42)!;
            var readNames = reads.Take(nr).Select(r => Name(r)!).ToHashSet(); var writeNames = writes.Take(nw).Select(r => Name(r)!).ToHashSet();
            // Capstone 5 将部分 CMP 别名的第一个源标为写入；架构上比较只写 NZCV。
            if (mnemonic is "cmp" or "cmn" or "tst" or "fcmp")
            { readNames.UnionWith(operands.Where(o => o.Kind == 1).Select(o => o.Register!)); writeNames.RemoveWhere(r => r != "nzcv"); }
            output.Add(new((ulong)Marshal.ReadInt64(p, 8), mnemonic, Marshal.PtrToStringAnsi(p + 74)!,
                operands.ToArray(), Marshal.ReadByte(detail, 5) != 0, Marshal.ReadByte(detail, 6) != 0, Convert.ToHexString(raw))
                { ConditionCode = Marshal.ReadInt32(detail, 0), Reads = readNames.ToArray(), Writes = writeNames.ToArray() });
        }
        free(pointer, count);
        if (output.Count * 4 != bytes.Length) throw new InvalidDataException("机器码未完整解码，拒绝跳过未知指令");
        return output.ToArray();
    }
    public void Dispose() { close(ref handle); NativeLibrary.Free(library); }
}
