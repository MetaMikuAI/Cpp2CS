using System.Runtime.InteropServices;

namespace Cpp2CS.Tests.Execution;

/// <summary>独立调用宿主 C 数学库；不复用恢复器的数学表达式或 CLR 取整实现。</summary>
internal static class NativeMathLibrary
{
    [UnmanagedFunctionPointer(CallingConvention.Cdecl)]
    internal delegate double ModfFunction(double value, out double integral);
    [UnmanagedFunctionPointer(CallingConvention.Cdecl)]
    internal delegate float SingleFunction(float value);
    [UnmanagedFunctionPointer(CallingConvention.Cdecl)]
    internal delegate float SingleBinaryFunction(float value, float divisor);

    internal static readonly IntPtr Library = NativeLibrary.Load(OperatingSystem.IsWindows() ? "ucrtbase.dll"
        : OperatingSystem.IsMacOS() ? "/usr/lib/libSystem.B.dylib" : "libm.so.6");
    internal static readonly ModfFunction Modf = Marshal.GetDelegateForFunctionPointer<ModfFunction>(NativeLibrary.GetExport(Library, "modf"));
    internal static readonly SingleFunction Sinf = Marshal.GetDelegateForFunctionPointer<SingleFunction>(NativeLibrary.GetExport(Library, "sinf"));
    internal static readonly SingleBinaryFunction Fmodf = Marshal.GetDelegateForFunctionPointer<SingleBinaryFunction>(NativeLibrary.GetExport(Library, "fmodf"));
}
