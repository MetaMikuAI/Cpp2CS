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

    /// <summary>
    /// 受约束调用：引用类型取 *objBuffer 并查虚方法；值类型在方法声明在 T 上时以 objBuffer 为接收者，否则装箱（盒头写 klass 和 monitor=-1）。
    /// 三条路径都以 (指针, method, 接收者, args, ret) 尾调用 invoker_method。
    /// </summary>
    internal static bool ConstrainedCallBody(IReadOnlyList<uint> w) => w.Count >= 67
        && w[3] == (0xb9400008u | (uint)((RuntimeLayout.ClassByvalArg + 8) / 4) << 10) // ldr w8, [x0, byval_arg 标志]
        && w[6] == 0xaa0303f6 // mov x22, x3：objBuffer
        && w[7] == 0xaa0103f5 // mov x21, x1：method
        && w[8] == 0x37f80148 // tbnz w8, 31, 值类型
        && w[9] == 0xf94002d6 // ldr x22, [x22]：取对象
        && w[15] == (0xa9400000u | (uint)(RuntimeLayout.MethodVirtualPointer / 8) << 15 | 5u << 10) // ldp x0, x5, [x0, virtualMethodPointer]
        && w[18] == (0xf94002a8u | (uint)(RuntimeLayout.MethodKlass / 8) << 10) // ldr x8, [x21, klass]
        && w[19] == 0xeb00011f // cmp x8, x0
        && w[30] == 0xf94002a8 // ldr x8, [x21]：methodPointer
        && w[31] == (0xf94002a5u | (uint)(RuntimeLayout.MethodInvoker / 8) << 10) // ldr x5, [x21, invoker_method]
        && w[40] == 0xd61f00a0 // br x5
        && w[56] == 0x92800008 // mov x8, -1
        && w[57] == 0xa90022e0 // stp x0, x8, [x23]：盒头
        && w[58] == (0xb9400002u | (uint)(RuntimeLayout.ClassStackSlotSize / 4) << 10); // ldr w2, [x0, stack_slot_size]

    /// <summary>unbox.any：引用做实例检查后写入 storage 并返回其地址；值类型比较 element_class，失败抛出，成功返回盒内地址；Nullable 写入 storage。</summary>
    internal static bool UnboxAnyBody(IReadOnlyList<uint> w) => w.Count >= 49
        && w[2] == (0xb9400028u | (uint)((RuntimeLayout.ClassByvalArg + 8) / 4) << 10) // ldr w8, [x1, byval_arg 标志]
        && w[3] == 0xaa0203f5 // mov x21, x2：storage
        && w[6] == 0x37f800e8 // tbnz w8, 31, 值类型
        && w[13] == (0xf9400268u | (uint)(RuntimeLayout.ClassGenericClass / 8) << 10) // ldr x8, [x19, generic_class]
        && w[15] == (0x39400268u | (uint)RuntimeLayout.ClassBitflags1 << 10) // ldrb w8, [x19, bitflags1]
        && w[16] == 0x37180228 // tbnz w8, 3, Nullable
        && w[19] == (0xf9400269u | (uint)(RuntimeLayout.ClassElementClass / 8) << 10) // ldr x9, [x19, element_class]
        && w[20] == (0xf9400108u | (uint)(RuntimeLayout.ClassElementClass / 8) << 10) // ldr x8, [x8, element_class]
        && w[21] == 0xeb09011f // cmp x8, x9
        && w[28] == 0xf90002a0 // str x0, [x21]
        && w[30] == 0xaa1503e0 // mov x0, x21
        && w[32] == 0xd65f03c0;
}
