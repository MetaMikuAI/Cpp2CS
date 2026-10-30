using Cpp2CS.Facts;
using Cpp2CS.Image;
using Cpp2CS.Model;

namespace Cpp2CS.Tests.Execution;

/// <summary>从运行时函数自身的完整指令核对泛型分派契约，不使用被测方法的 L2/L3 识别结果。</summary>
[ShapeModel("泛型虚方法实例化", Basis = "ARM64 helper 完整 18 条指令：取虚表方法的定义与类实参、请求方法的 method_inst，再由运行时方法表取封闭 MethodInfo；CIL 按 ECMA-335 callvirt 保留方法实参")]
internal static class GenericVirtualDispatch
{
    public static bool Matches(ProgramFacts facts, ulong address)
    {
        var image = facts.Model.Image;
        for (var hop = 0; hop < 4; hop++)
        {
            if (image.Resolve(address).Kind != AddressKind.FileBacked) return false;
            var word = image.ReadU32(address);
            if ((word & 0xfc000000) != 0x14000000) break;
            address = (ulong)((long)address + ((int)(word << 6) >> 4));
        }
        if (facts.Code.At(address) is not { } function || function.Start != address || function.End - address != 18 * 4) return false;
        ReadOnlySpan<uint> words =
        [
            0xd100c3ff, 0xf90013fe, // 栈帧与 LR
            0x39414c08, 0x37080068, 0xaa1f03e8, 0x14000003, // method->is_inflated
            0xf9402009, 0xa9402120, // 定义与类实参来自 vtable 方法
            0xf9402029, 0x52800021, 0xf9400929, // 方法实参来自请求的实例
            0xa900a3e0, 0x910023e0, 0xf9000fe9, // Il2CppGenericMethod 三指针键
            0, // 唯一 BL：运行时实例化/查表
            0xf94013fe, 0x9100c3ff, 0xd65f03c0,
        ];
        for (var i = 0; i < words.Length; i++)
        {
            var word = image.ReadU32(address + (ulong)i * 4);
            if (i == 14 ? (word & 0xfc000000) != 0x94000000 : word != words[i]) return false;
        }
        return true;
    }

    public static ulong Resolve(World world, ulong slotInfo, ulong requestedInfo)
    {
        var slot = world.MethodOfInfo(slotInfo) ?? throw new Unsupported("泛型虚方法的虚表 MethodInfo 未合成");
        var requested = world.MethodOfInfo(requestedInfo) ?? throw new Unsupported("泛型虚方法的请求 MethodInfo 未合成");
        if (!slot.Method.IsVirtual || requested.MethodArguments.Count == 0
            || slot.Method.GenericParameters.Count != requested.MethodArguments.Count || slot.Method.Slot != requested.Method.Slot)
            throw new Unsupported("泛型虚方法的槽位或实参数量不匹配");
        return world.MethodInfo(slot with { MethodArguments = requested.MethodArguments });
    }
}
