namespace Cpp2CS.Tests.Execution;

internal sealed partial class NativeMachine
{
    internal const ulong ThreadBase = 0x7190_0000_0000;
    internal const ulong ThreadCanary = 0x9e3779b97f4a7c00;

    /// <summary>Android ARM64 线程区只建模已识别的栈保护槽；其他 TLS 读取仍报告不可检查。</summary>
    internal static void MapThread(Unicorn engine, Action<string> unsupported)
    {
        engine.Map(ThreadBase, 0x1000);
        engine.OnAccess(ThreadBase, ThreadBase + 0xfff, (_, kind, address, size, _, _) =>
        {
            if (kind == 16 && size > 0 && address >= ThreadBase + 0x28 && address + (ulong)size <= ThreadBase + 0x30) return;
            unsupported($"未建模的线程区访问 +0x{address - ThreadBase:x}，宽度 {size}，种类 {kind}");
            engine.Stop();
        });
    }

    internal static void InitializeThread(Unicorn engine)
    {
        engine.Write(ThreadBase + 0x28, StructAbi.Bytes(ThreadCanary, 8));
        engine.SetReg(Unicorn.RegTpidrEl0, ThreadBase);
    }
}
