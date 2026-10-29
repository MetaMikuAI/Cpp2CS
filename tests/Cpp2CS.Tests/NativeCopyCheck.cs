using Cpp2CS.Facts;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class NativeCopyCheck
{
    [Command("native-copy", "完整指令副本的返回值、分支目标和地址边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var left = new CodeFunction(0x1000, 0x1010, CodeRegion.Managed, default);
        var right = new CodeFunction(0x2000, 0x2010, CodeRegion.Managed, default);
        var words = new Dictionary<ulong, uint>();
        uint Branch(ulong pc, ulong target) => 0x94000000u | ((uint)((long)target - (long)pc) >> 2 & 0x03ffffff);
        bool Equal() => NativeCopy.Equal(left, right, address => words.TryGetValue(address, out var word) ? word : null);
        foreach (var mode in new[] { "copy", "return", "call", "condition", "adr", "adrp", "literal", "missing" })
        {
            uint[] body = [0x34000040, 0x52800020, 0x94000000, 0xd65f03c0];
            for (var i = 0; i < body.Length; i++)
            {
                words[left.Start + (ulong)i * 4] = body[i];
                words[right.Start + (ulong)i * 4] = body[i];
            }
            words[0x1008] = Branch(0x1008, 0x4000);
            words[0x2008] = Branch(0x2008, mode == "call" ? 0x4004UL : 0x4000UL);
            if (mode == "return") words[0x2004] = 0x52800040;
            if (mode == "condition") words[0x2000] = 0x35000040;
            if (mode is "adr" or "adrp" or "literal")
                words[0x1004] = words[0x2004] = mode == "adr" ? 0x10000000u : mode == "adrp" ? 0x90000000u : 0x58000000u;
            if (mode == "missing") words.Remove(0x200c);
            a.Equal(mode == "copy", Equal(), mode);
        }
        return a.Finish("native-copy");
    }
}
