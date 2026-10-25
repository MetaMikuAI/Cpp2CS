using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests.Execution;

internal sealed partial class CilInterpreter
{
    // ECMA-335 I.8.2.1、I.12.1.6：值类型复制值，托管指针保持存储身份；字节数组不原地修改。
    private bool Aggregate(TypeRef type) => Types.Kind(type) == TypeKind.Struct && !IsHandle(type);

    public StackValue FromBytes(TypeRef type, byte[] bytes) => Aggregate(type)
        ? new(StackKind.Struct, 0, bytes.ToArray()) : Load(type, StructAbi.Bits(bytes));

    private byte[] ToBytes(TypeRef type, StackValue value)
    {
        if (!Aggregate(type)) return StructAbi.Bytes(Raw(type, value), index.StructAbi.Classifier.Describe(type).Size);
        if (value.Kind != StackKind.Struct || value.Data!.Length != Types.Size(type)) throw new Unsupported($"值类型 {type} 的字节表示不符");
        return value.Data.ToArray();
    }

    private StackValue ReadValue(CilSide side, TypeRef type, ulong address)
    {
        var bytes = new byte[side.World.StorageSize(type)];
        side.Read(address, bytes);
        return FromBytes(type, bytes);
    }

    private void WriteValue(CilSide side, TypeRef type, ulong address, StackValue value) => side.Write(address, ToBytes(type, value));
}
