using System.Buffers.Binary;

namespace Cpp2CS.Tests.Execution;

internal static class NullPageCheck
{
    [Command("native-null-page", "独立 ARM64 访存检查：映像头不得充当空指针页")]
    public static int Run()
    {
        using var machine = new Unicorn();
        machine.Map(0, 0x1000);
        machine.Map(0x10000, 0x1000);
        Span<byte> instructions = stackalloc byte[4];
        BinaryPrimitives.WriteUInt32LittleEndian(instructions, 0xf9400000); // ldr x0, [x0]
        machine.Write(0x10000, instructions);
        machine.Write(0, new byte[] { 0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0 });
        var enabled = false;
        var invalid = false;
        machine.OnNullPage((_, _, address, _, _, _) =>
        {
            if (!enabled) return;
            invalid = address == 0;
            machine.Stop();
        });
        machine.SetReg(Unicorn.X(0), 0);
        var a = new Assertions();
        a.Equal(0, machine.Start(0x10000, 1), "映射零页时，错误的空指针读取会成功");
        a.Equal(0x00010102464c457fUL, machine.Reg(Unicorn.X(0)), "空指针实际读到了 ELF 头");
        enabled = true;
        machine.SetReg(Unicorn.X(0), 0);
        machine.Start(0x10000, 1);
        a.True(invalid, "零页访问被单独识别并中断");
        invalid = false;
        machine.SetReg(Unicorn.X(0), 0x10000);
        a.Equal(0, machine.Start(0x10000, 1), "其他已映射页仍可读取");
        a.True(!invalid, "普通地址不触发零页检查");
        return a.Finish("native-null-page");
    }
}
