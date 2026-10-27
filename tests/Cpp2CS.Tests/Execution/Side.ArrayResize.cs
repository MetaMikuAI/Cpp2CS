using Cpp2CS.Facts;
using Cpp2CS.Model;

namespace Cpp2CS.Tests.Execution;

internal abstract partial class Side
{
    /// <summary>Array.Resize 的数组身份、前缀复制和新增元素清零；超出合成堆范围的长度不冒充执行成功。</summary>
    public bool ResizeArray(MethodRef method, IReadOnlyList<byte[]> arguments)
    {
        if (method.Method is not { IsStatic: true, Owner.FullName: "System.Array", Name: "Resize", GenericParameters.Count: 1 }
            || method.MethodArguments is not [var element]
            || StructAbi.ArgumentTypes(method) is not [ByRefRef { Element: ArrayRef { IsVector: true } array }, var lengthType]
            || !array.Element.Equals(element) || !lengthType.Equals(World.Types.Int32)) return false;
        var slot = StructAbi.Bits(arguments[0]);
        var length = unchecked((int)StructAbi.Bits(arguments[1]));
        var size = World.StorageSize(element);
        if (length < 0 || (ulong)length > (World.HeapSize - RuntimeLayout.ArrayData) / (ulong)size)
            throw new Unsupported("Array.Resize 长度超出非负合成堆范围");
        var original = Read64(slot);
        var oldLength = original == 0 ? 0 : checked((int)Read64(original + RuntimeLayout.ArrayMaxLength));
        if (original != 0 && oldLength == length) return true;
        var resized = NewArray(array, length);
        var bytes = new byte[Math.Min(oldLength, length) * size];
        if (bytes.Length != 0)
        {
            Read(original + RuntimeLayout.ArrayData, bytes);
            Write(resized + RuntimeLayout.ArrayData, bytes);
        }
        WriteValue(slot, resized, 8);
        return true;
    }
}
