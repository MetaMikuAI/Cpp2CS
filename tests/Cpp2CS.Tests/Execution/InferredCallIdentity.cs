using Cpp2CS.Facts;
using Cpp2CS.Model;

namespace Cpp2CS.Tests.Execution;

/// <summary>F8 核对失败是对照器错误，不能作为普通不可检查用例吞掉。</summary>
internal sealed class InferredCallError(string message) : Exception(message);

[ShapeModel("调用身份", Basis = "F8：共享泛型代码以 MethodInfo 实参确定被调用方法的身份；对照时逐次核对运行时身份")]
internal static class InferredCallIdentity
{
    /// <summary>
    /// 身份只取自运行时实际的 MethodInfo 指针→槽位元数据映射，不用 L1 的见证实例列表。
    /// 独立依据：UsageSlots 的 MethodDef/MethodRef 编码与注册调整器普查证明同一定义可共享不同实例；
    /// IL2CPP 的最后一个隐藏参数及合成映射见 ManagedAbi、World.SlotValue/MethodInfo。
    /// </summary>
    public static MethodRef Resolve(World world, UnregisteredMethod identity, ulong pointer, MethodRef? expected)
    {
        var actual = world.MethodOfInfo(pointer)
            ?? throw new InferredCallError($"0x{identity.Address:x}：实际 MethodInfo 0x{pointer:x} 没有元数据映射");
        if (actual.Method != identity.Definition || !UnregisteredMethods.IsClosed(actual))
            throw new InferredCallError($"0x{identity.Address:x}：实际 MethodInfo {actual} 不是定义 {identity.Definition} 的封闭实例");
        if (actual != expected)
            throw new InferredCallError($"0x{identity.Address:x}：实际 MethodInfo {actual} 与 CIL 调用 {expected} 不同");
        if (world.Index.Abi.Classify(actual, out _) is not { } signature || UnregisteredMethods.Shape(signature) != UnregisteredMethods.Shape(identity.Abi))
            throw new InferredCallError($"0x{identity.Address:x}：运行时实例 ABI 与入口不吻合");
        return actual;
    }
}
