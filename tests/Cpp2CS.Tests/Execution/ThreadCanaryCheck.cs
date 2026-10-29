using System.Buffers.Binary;

namespace Cpp2CS.Tests.Execution;

internal static class ThreadCanaryCheck
{
    [Command("thread-canary", "ARM64 线程寄存器与栈保护槽的读取、隔离和拒绝边界", Gate = Gate.Unit)]
    public static int Run()
    {
        using var engine = new Unicorn();
        string? problem = null;
        NativeMachine.MapThread(engine, detail => problem = detail);
        engine.Map(0x10000, 0x1000);
        var a = new Assertions();
        var entry = 0x10000UL;
        foreach (var mode in new[] { "read", "unknown", "write", "reset" })
        {
            problem = null;
            engine.Write(NativeMachine.ThreadBase + 0x28, new byte[8]);
            NativeMachine.InitializeThread(engine);
            var code = new byte[8];
            BinaryPrimitives.WriteUInt32LittleEndian(code, 0xd53bd040); // mrs x0, tpidr_el0
            BinaryPrimitives.WriteUInt32LittleEndian(code.AsSpan(4), mode switch
            {
                "unknown" => 0xf9400c01u, // ldr x1, [x0, #0x18]
                "write" => 0xf9001401u, // str x1, [x0, #0x28]
                _ => 0xf9401401u, // ldr x1, [x0, #0x28]
            });
            engine.Write(entry, code);
            a.Equal(0, engine.Start(entry, 2), "指令正常执行或由边界钩子停止");
            entry += 0x100;
            a.Equal(NativeMachine.ThreadBase, engine.Reg(Unicorn.X(0)), "MRS 读取本用例线程指针");
            a.Equal(mode is "unknown" or "write", problem is not null, mode);
            if (problem is null) a.Equal(NativeMachine.ThreadCanary, engine.Reg(Unicorn.X(1)), "栈保护槽不会残留上次写入");
        }
        return a.Finish("thread-canary");
    }
}
