using System.Runtime.InteropServices;

namespace Cpp2CS.Tests.Execution;

/// <summary>
/// libunicorn（2.x，ARM64）的最小 P/Invoke 封装。库路径取环境变量 UNICORN_LIB，否则在 ~/.venv 的 Python unicorn 包中查找。
/// 钩子委托由本对象持有，避免被回收。
/// </summary>
internal sealed class Unicorn : IDisposable
{
    public const int RegNzcv = 3, RegSp = 4, RegPc = 260, RegTpidrEl0 = 262;
    public const int HookCode = 4, HookBlock = 8, HookMemWrite = 2048, HookMemUnmapped = 112;
    public const uint ProtAll = 7;

    public delegate void CodeHook(IntPtr uc, ulong address, uint size, IntPtr user);
    public delegate void MemoryHook(IntPtr uc, int type, ulong address, int size, long value, IntPtr user);
    [return: MarshalAs(UnmanagedType.I1)]
    public delegate bool InvalidMemoryHook(IntPtr uc, int type, ulong address, int size, long value, IntPtr user);

    private readonly IntPtr handle;
    private readonly List<Delegate> hooks = [];

    static Unicorn() => NativeLibrary.SetDllImportResolver(typeof(Unicorn).Assembly, (name, _, _) =>
        name == "unicorn" ? NativeLibrary.Load(LibraryPath()) : IntPtr.Zero);

    public Unicorn()
    {
        Check(uc_open(2, 0, out handle), "uc_open");
    }

    /// <summary>X0–X30 的寄存器编号（X29、X30 另有编号）。</summary>
    public static int X(int index) => index switch { <= 28 => 199 + index, 29 => 1, 30 => 2, _ => throw new ArgumentOutOfRangeException(nameof(index)) };
    /// <summary>Dn（64 位）与 Sn（32 位）浮点寄存器的编号。</summary>
    public static int D(int index) => 40 + index;
    public static int S(int index) => 136 + index;

    public void Map(ulong address, ulong size) => Check(uc_mem_map(handle, address, (nuint)size, ProtAll), $"uc_mem_map 0x{address:x}+0x{size:x}");

    public void Write(ulong address, ReadOnlySpan<byte> bytes)
    {
        unsafe
        {
            fixed (byte* p = bytes) Check(uc_mem_write(handle, address, p, (nuint)bytes.Length), $"uc_mem_write 0x{address:x}");
        }
    }

    public void Read(ulong address, Span<byte> bytes)
    {
        unsafe
        {
            fixed (byte* p = bytes) Check(uc_mem_read(handle, address, p, (nuint)bytes.Length), $"uc_mem_read 0x{address:x}");
        }
    }

    public bool TryRead(ulong address, Span<byte> bytes)
    {
        unsafe
        {
            fixed (byte* p = bytes) return uc_mem_read(handle, address, p, (nuint)bytes.Length) == 0;
        }
    }

    public ulong Reg(int id)
    {
        ulong value = 0;
        unsafe { Check(uc_reg_read(handle, id, &value), "uc_reg_read"); }
        return value;
    }

    public void SetReg(int id, ulong value)
    {
        unsafe { Check(uc_reg_write(handle, id, &value), "uc_reg_write"); }
    }

    public unsafe void SetVectorHigh(int index, ulong high)
    {
        ulong* value = stackalloc ulong[2];
        Check(uc_reg_read(handle, 104 + index, value), "uc_reg_read Q");
        value[1] = high;
        Check(uc_reg_write(handle, 104 + index, value), "uc_reg_write Q");
    }

    public void OnCode(CodeHook hook) => Add(HookCode, hook);
    public void OnBlock(CodeHook hook) => Add(HookBlock, hook);
    public void OnWrite(MemoryHook hook) => Add(HookMemWrite, hook);
    public void OnUnmapped(InvalidMemoryHook hook) => Add(HookMemUnmapped, hook);
    public void OnNullPage(MemoryHook hook) => Add(1024 | HookMemWrite, hook, 0, 0xfff);
    public void OnAccess(ulong first, ulong last, MemoryHook hook) => Add(1024 | HookMemWrite, hook, first, last);

    private void Add(int type, Delegate hook, ulong begin = 1, ulong end = 0)
    {
        hooks.Add(hook);
        Check(uc_hook_add(handle, out _, type, Marshal.GetFunctionPointerForDelegate(hook), IntPtr.Zero, begin, end), "uc_hook_add");
    }

    /// <summary>从 begin 执行，最多 count 条指令；返回错误码（0 为正常结束或被 Stop）。</summary>
    public int Start(ulong begin, ulong count) => uc_emu_start(handle, begin, 0, 0, (nuint)count);

    public void Stop() => uc_emu_stop(handle);

    public static string Error(int code) => Marshal.PtrToStringAnsi(uc_strerror(code)) ?? code.ToString();

    public void Dispose() => uc_close(handle);

    private static void Check(int error, string what)
    {
        if (error != 0) throw new InvalidOperationException($"{what}: {Error(error)}");
    }

    private static string LibraryPath()
    {
        if (Environment.GetEnvironmentVariable("UNICORN_LIB") is { Length: > 0 } path) return path;
        var lib = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.UserProfile), ".venv", "lib");
        return Directory.Exists(lib)
            ? Directory.GetDirectories(lib, "python3*").Select(d => Path.Combine(d, "site-packages", "unicorn", "lib", "libunicorn.so.2")).FirstOrDefault(File.Exists)
                ?? throw new FileNotFoundException("找不到 libunicorn.so.2；请设置 UNICORN_LIB")
            : throw new FileNotFoundException("找不到 ~/.venv/lib；请设置 UNICORN_LIB");
    }

    [DllImport("unicorn")] private static extern int uc_open(int arch, int mode, out IntPtr uc);
    [DllImport("unicorn")] private static extern int uc_close(IntPtr uc);
    [DllImport("unicorn")] private static extern int uc_mem_map(IntPtr uc, ulong address, nuint size, uint perms);
    [DllImport("unicorn")] private static extern unsafe int uc_mem_write(IntPtr uc, ulong address, byte* bytes, nuint size);
    [DllImport("unicorn")] private static extern unsafe int uc_mem_read(IntPtr uc, ulong address, byte* bytes, nuint size);
    [DllImport("unicorn")] private static extern unsafe int uc_reg_write(IntPtr uc, int regid, void* value);
    [DllImport("unicorn")] private static extern unsafe int uc_reg_read(IntPtr uc, int regid, void* value);
    [DllImport("unicorn")] private static extern int uc_emu_start(IntPtr uc, ulong begin, ulong until, ulong timeout, nuint count);
    [DllImport("unicorn")] private static extern int uc_emu_stop(IntPtr uc);
    [DllImport("unicorn")] private static extern int uc_hook_add(IntPtr uc, out IntPtr hook, int type, IntPtr callback, IntPtr userData, ulong begin, ulong end);
    [DllImport("unicorn")] private static extern IntPtr uc_strerror(int error);
}
