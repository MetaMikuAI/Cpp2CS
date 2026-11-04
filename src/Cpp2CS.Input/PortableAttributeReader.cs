#nullable enable
using System.Collections.Generic;
using System.IO;
using Cpp2CS.Input.Portable;
using Il2CppDumper;

namespace Cpp2CS.Input
{
    /// <summary>v29+ 的自定义特性编码读取，语义与 Il2CppDumper.CustomAttributeDataReader 一致。</summary>
    internal static class PortableAttributeReader
    {
        public static IReadOnlyList<CustomAttributeReaderVisitor> VisitAll(PortableMetadata metadata, Il2Cpp il2Cpp, byte[] buffer)
        {
            if (buffer.Length == 0) return [];
            using var reader = new BinaryReader(new MemoryStream(buffer));
            var count = (int)reader.ReadCompressedUInt32();
            var ctorAt = reader.BaseStream.Position;
            var dataAt = ctorAt + count * 4L;
            var result = new List<CustomAttributeReaderVisitor>(count);
            for (var i = 0; i < count; i++)
            {
                var visitor = new CustomAttributeReaderVisitor();
                reader.BaseStream.Position = ctorAt;
                var constructor = reader.ReadInt32();
                // v106 的构造器槽写成带 0x60 前缀的令牌；低 24 位是方法定义索引。
                visitor.CtorIndex = constructor >= 0 && constructor < metadata.methodDefs.Length
                    ? constructor
                    : constructor & 0x00FFFFFF;
                ctorAt = reader.BaseStream.Position;
                if (visitor.CtorIndex < 0 || visitor.CtorIndex >= metadata.methodDefs.Length) break;
                var method = metadata.methodDefs[visitor.CtorIndex];
                var type = metadata.typeDefs[method.declaringType];

                reader.BaseStream.Position = dataAt;
                var argumentCount = (int)reader.ReadCompressedUInt32();
                var fieldCount = (int)reader.ReadCompressedUInt32();
                var propertyCount = (int)reader.ReadCompressedUInt32();
                // v106 的带实参/命名实参编码尚未接入；保留已解析的无参特性，避免错误解释后续字节。
                if (argumentCount != 0 || fieldCount != 0 || propertyCount != 0) break;

                visitor.Arguments = new AttributeArgument[argumentCount];
                for (var a = 0; a < argumentCount; a++)
                {
                    var argument = visitor.Arguments[a] = new AttributeArgument();
                    argument.Value = ReadValue(metadata, il2Cpp, reader)!;
                    argument.Index = a;
                }

                visitor.Fields = new AttributeArgument[fieldCount];
                for (var f = 0; f < fieldCount; f++)
                {
                    var field = visitor.Fields[f] = new AttributeArgument();
                    field.Value = ReadValue(metadata, il2Cpp, reader)!;
                    var (declaring, index) = NamedArgument(metadata, reader, type);
                    field.Index = declaring.fieldStart + index;
                }

                visitor.Properties = new AttributeArgument[propertyCount];
                for (var p = 0; p < propertyCount; p++)
                {
                    var property = visitor.Properties[p] = new AttributeArgument();
                    property.Value = ReadValue(metadata, il2Cpp, reader)!;
                    var (declaring, index) = NamedArgument(metadata, reader, type);
                    property.Index = declaring.propertyStart + index;
                }

                dataAt = reader.BaseStream.Position;
                result.Add(visitor);
            }
            return result;
        }

        private static BlobValue? ReadValue(PortableMetadata metadata, Il2Cpp il2Cpp, BinaryReader reader)
        {
            var type = PortableValueReader.ReadEncodedTypeEnum(metadata, il2Cpp, reader, out var enumType);
            PortableValueReader.GetConstantValueFromBlob(metadata, il2Cpp, type, reader, out var value);
            if (value is not null && enumType is not null) value.EnumType = enumType;
            return value;
        }

        private static (Il2CppTypeDefinition Declaring, int Index) NamedArgument(PortableMetadata metadata, BinaryReader reader, Il2CppTypeDefinition owner)
        {
            var index = reader.ReadCompressedInt32();
            if (index >= 0) return (owner, index);
            index = -(index + 1);
            var typeIndex = (int)reader.ReadCompressedUInt32();
            return (metadata.typeDefs[typeIndex], index);
        }
    }
}
