using System.Buffers.Binary;
using Cpp2CS.Model;
namespace Cpp2CS.Tests.Execution;
internal sealed partial class ManagedValues(WorldIndex index)
{
    public static TypeRef[] ArgumentTypes(MethodRef method) =>
        [.. method.Method.IsStatic ? Array.Empty<TypeRef>() : [method.Method.Owner.IsValueType ? new ByRefRef(method.DeclaringType) : method.DeclaringType],
         .. method.Method.Parameters.Select(p => p.Type.Substitute(method.TypeArguments, method.MethodArguments))];

    public static ulong Bits(ReadOnlySpan<byte> bytes)
    {
        Span<byte> word = stackalloc byte[8];
        word.Clear();
        bytes.CopyTo(word);
        return BinaryPrimitives.ReadUInt64LittleEndian(word);
    }

    public static byte[] Bytes(ulong bits, int size)
    {
        var result = new byte[size];
        for (var i = 0; i < size; i++) result[i] = (byte)(bits >> (8 * i));
        return result;
    }

    /// <summary>ECMA-335 I.8.2.1：值由字段组成；存储可能含填充，调用/返回事件只记录叶子。</summary>
    public IEnumerable<ulong> ObservableArgument(Side side, TypeRef type, byte[] bytes)
    {
        if (type is ByRefRef b && Bits(bytes) is var address && side.ArgumentPointer(address) is var logical && logical != address)
        {
            yield return logical;
            var value = new byte[side.World.StorageSize(b.Element)];
            side.Read(address, value);
            foreach (var leaf in Observable(b.Element, value)) yield return leaf;
        }
        else foreach (var leaf in Observable(type, bytes)) yield return leaf;
    }

    public IEnumerable<ulong> Observable(TypeRef type, byte[] bytes) => Leaves(type)
        .Select(l => Bits(bytes.AsSpan(l.Offset, l.Size)));
    public IEnumerable<(string Path, TypeRef Type, int Offset, int Size)> Leaves(TypeRef type)
    {
        if (index.Types.Kind(type) == TypeKind.Struct && type is DefinitionRef d)
        {
            foreach (var leaf in index.Types.Leaves(d))
                yield return (string.Join(".", leaf.Path.Select(f => f.Field.Name)), leaf.Type, leaf.Offset, index.Types.Size(leaf.Type));
        }
        else yield return ("", type, 0, index.Types.Size(type));
    }
}
