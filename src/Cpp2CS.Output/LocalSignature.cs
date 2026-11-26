using System.Collections.Immutable;
using System.Reflection.Metadata;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;

namespace Cpp2CS.Output;

internal static class LocalSignature
{
    /// <summary>ECMA-335 II.23.2.6。具名类型保留类型签名；入栈时已扩宽的小整数按局部自己的存储类型写。</summary>
    public static ImmutableArray<byte> Encode(ImmutableArray<TypeShape> locals, IMetadataView metadata,
        Func<EntityRef, ImmutableArray<byte>> typeSignature)
    {
        if (locals.IsEmpty) return [];
        if (locals.Length > 0xfffe) throw new InvalidDataException($"局部变量个数 {locals.Length} 超出 LocalVarSig 的范围");
        var blob = new BlobBuilder();
        blob.WriteByte(0x07);
        blob.WriteCompressedInteger(locals.Length);
        foreach (var local in locals)
        {
            if (local.Entity != default)
            {
                var element = metadata.Type(local.Entity);
                if (local.Kind == StackKind.ByRef || (element.Kind, element.StorageBits, element.Signed, element.TwoValued)
                    == (local.Kind, local.StorageBits, local.Signed, local.TwoValued))
                {
                    if (local.Kind == StackKind.ByRef) blob.WriteByte((byte)SignatureTypeCode.ByReference);
                    var type = typeSignature(local.Entity);
                    if (type.IsDefaultOrEmpty) throw new InvalidDataException($"局部变量类型 {local.Entity} 没有签名");
                    blob.WriteBytes(type);
                    continue;
                }
                if (local.Kind != StackKind.Int32 || local.StorageBits != 32 || element.Kind != StackKind.Int32 || element.StorageBits >= 32)
                    throw new InvalidDataException($"局部变量形状与类型 {local.Entity} 不符");
            }
            var scalar = (local.Kind, local.StorageBits, local.Signed) switch
            {
                (StackKind.Int32, 8, false) when local.TwoValued => SignatureTypeCode.Boolean,
                (StackKind.Int32, 8, true) => SignatureTypeCode.SByte,
                (StackKind.Int32, 8, false) => SignatureTypeCode.Byte,
                (StackKind.Int32, 16, true) => SignatureTypeCode.Int16,
                (StackKind.Int32, 16, false) => SignatureTypeCode.UInt16,
                (StackKind.Int32, 32, true) => SignatureTypeCode.Int32,
                (StackKind.Int32, 32, false) => SignatureTypeCode.UInt32,
                (StackKind.Int64, 64, true) => SignatureTypeCode.Int64,
                (StackKind.Int64, 64, false) => SignatureTypeCode.UInt64,
                (StackKind.NativeInt, 32 or 64, true) => SignatureTypeCode.IntPtr,
                (StackKind.NativeInt, 32 or 64, false) => SignatureTypeCode.UIntPtr,
                (StackKind.Float32, 32, _) => SignatureTypeCode.Single,
                (StackKind.Float64, 64, _) => SignatureTypeCode.Double,
                (StackKind.Object, 32 or 64, _) => SignatureTypeCode.Object,
                (StackKind.Value, _, _) => throw new InvalidDataException("值类型局部变量缺少类型实体"),
                (StackKind.ByRef, _, _) => throw new InvalidDataException("托管指针局部变量缺少元素类型实体"),
                _ => throw new InvalidDataException($"不能编码局部变量 {local.Kind}/{local.StorageBits}"),
            };
            blob.WriteByte((byte)scalar);
        }
        return blob.ToImmutableArray();
    }
}
