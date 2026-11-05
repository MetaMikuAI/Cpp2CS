#nullable enable
using System;
using System.IO;
using System.Text;
using Cpp2CS.Input.Portable;
using Il2CppDumper;

namespace Cpp2CS.Input
{
    /// <summary>从 v38+ 元数据的默认值/特性 blob 读取常量，不依赖 Il2CppExecutor。</summary>
    internal static class PortableValueReader
    {
        public static bool TryGetDefaultValue(PortableMetadata metadata, Il2Cpp il2Cpp, int typeIndex, int dataIndex, out object? value)
        {
            var pointer = metadata.GetDefaultValueFromIndex(dataIndex);
            if ((uint)typeIndex >= (uint)il2Cpp.types.Length || il2Cpp.types[typeIndex] is not { } type)
                throw new InvalidDataException($"默认值类型索引无效：{typeIndex}");

            using var reader = new BinaryReader(new MemoryStream(metadata.RawBytes));
            reader.BaseStream.Position = (long)pointer;
            if (GetConstantValueFromBlob(metadata, il2Cpp, type.type, reader, out var blob) && blob is not null)
            {
                value = blob.Value;
                return true;
            }
            value = pointer;
            return false;
        }

        public static bool GetConstantValueFromBlob(PortableMetadata metadata, Il2Cpp il2Cpp, Il2CppTypeEnum type, BinaryReader reader, out BlobValue? value)
        {
            value = new BlobValue { il2CppTypeEnum = type };
            switch (type)
            {
                case Il2CppTypeEnum.IL2CPP_TYPE_BOOLEAN: value.Value = reader.ReadBoolean(); return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_U1: value.Value = reader.ReadByte(); return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_I1: value.Value = reader.ReadSByte(); return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_CHAR: value.Value = BitConverter.ToChar(reader.ReadBytes(2), 0); return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_U2: value.Value = reader.ReadUInt16(); return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_I2: value.Value = reader.ReadInt16(); return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_U4: value.Value = reader.ReadCompressedUInt32(); return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_I4: value.Value = reader.ReadCompressedInt32(); return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_U8: value.Value = reader.ReadUInt64(); return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_I8: value.Value = reader.ReadInt64(); return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_R4: value.Value = reader.ReadSingle(); return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_R8: value.Value = reader.ReadDouble(); return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_STRING:
                    {
                        var length = reader.ReadCompressedInt32();
                        value.Value = length == -1 ? null : Encoding.UTF8.GetString(reader.ReadBytes(length));
                        return true;
                    }
                case Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY:
                    {
                        var length = reader.ReadCompressedInt32();
                        if (length == -1)
                        {
                            value.Value = null;
                            return true;
                        }
                        var array = new BlobValue[length];
                        var elementType = ReadEncodedTypeEnum(metadata, il2Cpp, reader, out var elementEnum);
                        var different = reader.ReadByte();
                        for (var i = 0; i < length; i++)
                        {
                            var current = elementType;
                            var currentEnum = elementEnum;
                            if (different == 1) current = ReadEncodedTypeEnum(metadata, il2Cpp, reader, out currentEnum);
                            GetConstantValueFromBlob(metadata, il2Cpp, current, reader, out var item);
                            item!.il2CppTypeEnum = current;
                            item.EnumType = currentEnum!;
                            array[i] = item;
                        }
                        value.Value = array;
                        return true;
                    }
                case Il2CppTypeEnum.IL2CPP_TYPE_IL2CPP_TYPE_INDEX:
                    {
                        var index = reader.ReadCompressedInt32();
                        value.Value = index == -1 ? null : il2Cpp.types[index];
                        return true;
                    }
                default:
                    value = null;
                    return false;
            }
        }

        public static Il2CppTypeEnum ReadEncodedTypeEnum(PortableMetadata metadata, Il2Cpp il2Cpp, BinaryReader reader, out Il2CppType? enumType)
        {
            enumType = null;
            var type = (Il2CppTypeEnum)reader.ReadByte();
            if (type != Il2CppTypeEnum.IL2CPP_TYPE_ENUM) return type;
            var index = reader.ReadCompressedInt32();
            enumType = il2Cpp.types[index];
            var definition = TypeDefinition(metadata, enumType);
            for (var i = definition.fieldStart; i < definition.fieldStart + definition.field_count; i++)
            {
                var field = metadata.fieldDefs[i];
                if (metadata.GetStringFromIndex(field.nameIndex) != "value__") continue;
                return il2Cpp.types[field.typeIndex].type;
            }
            return Il2CppTypeEnum.IL2CPP_TYPE_I4;
        }

        public static Il2CppTypeDefinition TypeDefinition(PortableMetadata metadata, Il2CppType type) => type.type switch
        {
            Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE => metadata.typeDefs[type.data.klassIndex],
            _ => throw new NotSupportedException($"类型 {type.type} 不是类型定义"),
        };
    }
}
