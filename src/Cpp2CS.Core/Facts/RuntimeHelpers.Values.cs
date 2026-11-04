namespace Cpp2CS.Facts;

public sealed partial class RuntimeHelpers
{
    internal static bool GenericHasValueBody(IReadOnlyList<uint> w) => w.Count == 15
        && w[0] == (0xb9400008u | (uint)((RuntimeLayout.ClassByvalArg + 8) / 4) << 10)
        && w[1] == 0x37f800a8 // tbnz w8, 31, value
        && w[2] == 0xf9400028 // ldr x8, [x1]
        && w[3] == 0xf100011f // cmp x8, 0
        && w[4] == 0x1a9f07e0 // cset w0, ne
        && w[5] == 0xd65f03c0
        && w[6] == (0xf9400008u | (uint)(RuntimeLayout.ClassGenericClass / 8) << 10)
        && w[7] == 0xb4000068 // cbz x8, present
        && w[8] == (0x39400008u | (uint)RuntimeLayout.ClassBitflags1 << 10)
        && w[9] == 0x37180068 // tbnz w8, 3, nullable
        && w[10] == 0x52800020 // mov w0, 1
        && w[11] == 0xd65f03c0
        && w[12] == 0x39400028 // ldrb w8, [x1]
        && w[13] == 0x7100011f // cmp w8, 0
        && w[14] == 0x17fffff6; // b compare-result
}
