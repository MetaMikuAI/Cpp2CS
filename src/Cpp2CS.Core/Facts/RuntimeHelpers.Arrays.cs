namespace Cpp2CS.Facts;

public sealed partial class RuntimeHelpers
{
    /// <summary>完整函数只保存返回地址、检查数组长度、读取元素并返回；末尾调用的异常身份另行核对。</summary>
    internal static bool CheckedByteArrayBody(IReadOnlyList<uint> w) => w.Count == 9
        && w[0] == 0xf81f0ffe // str x30, [sp, -16]!
        && w[1] == (0xb9400008u | (uint)(RuntimeLayout.ArrayMaxLength / 4) << 10) // ldr w8, [x0, length]
        && w[2] == 0x6b08003f // cmp w1, w8
        && w[3] == 0x540000a2 // b.hs bounds
        && w[4] == 0x8b010008 // add x8, x0, x1
        && w[5] == (0x39400100u | (uint)RuntimeLayout.ArrayData << 10) // ldrb w0, [x8, data]
        && w[6] == 0xf84107fe // ldr x30, [sp], 16
        && w[7] == 0xd65f03c0 // ret
        && A64.IsBl(w[8]);
}
