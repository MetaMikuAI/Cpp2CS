namespace Cpp2CS.Tests.Execution;

internal static class RuntimeIsolationCheck
{
    [Command("runtime-isolation", "原生执行用例之间的已分配区与未分配区均不残留字节", Gate = Gate.Unit)]
    public static int Run()
    {
        using var engine = new Unicorn();
        engine.Map(World.RuntimeBase, World.RuntimeSize);
        NativeMachine.InitializeRuntime(engine, [1, 2, 3, 4]);
        engine.Write(World.RuntimeBase + 4096, [0x42]);
        NativeMachine.InitializeRuntime(engine, [7]);
        var bytes = new byte[4];
        engine.Read(World.RuntimeBase, bytes);
        var a = new Assertions();
        a.True(bytes.SequenceEqual(new byte[] { 7, 0, 0, 0 }), "较短用例不会保留旧数据尾部");
        engine.Read(World.RuntimeBase + 4096, bytes);
        a.True(bytes.All(b => b == 0), "原生指针写到的未分配区也恢复初值");
        return a.Finish("runtime-isolation");
    }
}
