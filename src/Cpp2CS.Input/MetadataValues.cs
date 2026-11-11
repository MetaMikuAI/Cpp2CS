#nullable disable
using System;
using System.IO;
using System.Text;
using Cpp2CS.Input;
namespace Il2CppDumper;
// 从 Il2CppDumper 的 Il2CppExecutor 保留元数据常量解码；不读取可执行文件。
internal sealed class Il2CppExecutor(Metadata metadata, RuntimeData il2Cpp)
{
    internal readonly Metadata metadata = metadata;
    private readonly RuntimeData il2Cpp = il2Cpp;
    public Il2CppTypeDefinition GetTypeDefinitionFromIl2CppType(Il2CppType type) => metadata.typeDefs[type.data.klassIndex];
    public Il2CppGenericParameter GetGenericParameteFromIl2CppType(Il2CppType type) => metadata.genericParameters[type.data.genericParameterIndex];
        public bool TryGetDefaultValue(int typeIndex, int dataIndex, out object value)
        {
            var pointer = metadata.GetDefaultValueFromIndex(dataIndex);
            var defaultValueType = il2Cpp.types[typeIndex];
            metadata.Position = pointer;
            if (GetConstantValueFromBlob(defaultValueType.type, metadata.Reader, out var blobValue))
            {
                value = blobValue.Value;
                return true;
            }
            else
            {
                value = pointer;
                return false;
            }
        }
        public bool GetConstantValueFromBlob(Il2CppTypeEnum type, BinaryReader reader, out BlobValue value)
        {
            value = new BlobValue
            {
                il2CppTypeEnum = type
            };
            switch (type)
            {
                case Il2CppTypeEnum.IL2CPP_TYPE_BOOLEAN:
                    value.Value = reader.ReadBoolean();
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_U1:
                    value.Value = reader.ReadByte();
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_I1:
                    value.Value = reader.ReadSByte();
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_CHAR:
                    value.Value = BitConverter.ToChar(reader.ReadBytes(2), 0);
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_U2:
                    value.Value = reader.ReadUInt16();
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_I2:
                    value.Value = reader.ReadInt16();
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_U4:
                    if (il2Cpp.Version >= 29)
                    {
                        value.Value = reader.ReadCompressedUInt32();
                    }
                    else
                    {
                        value.Value = reader.ReadUInt32();
                    }
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_I4:
                    if (il2Cpp.Version >= 29)
                    {
                        value.Value = reader.ReadCompressedInt32();
                    }
                    else
                    {
                        value.Value = reader.ReadInt32();
                    }
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_U8:
                    value.Value = reader.ReadUInt64();
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_I8:
                    value.Value = reader.ReadInt64();
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_R4:
                    value.Value = reader.ReadSingle();
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_R8:
                    value.Value = reader.ReadDouble();
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_STRING:
                    int length;
                    if (il2Cpp.Version >= 29)
                    {
                        length = reader.ReadCompressedInt32();
                        if (length == -1)
                        {
                            value.Value = null;
                        }
                        else
                        {
                            value.Value = Encoding.UTF8.GetString(reader.ReadBytes(length));
                        }
                    }
                    else
                    {
                        length = reader.ReadInt32();
                        value.Value = reader.ReadString(length);
                    }
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY:
                    var arrayLen = reader.ReadCompressedInt32();
                    if (arrayLen == -1)
                    {
                        value.Value = null;
                    }
                    else
                    {
                        var array = new BlobValue[arrayLen];
                        var arrayElementType = ReadEncodedTypeEnum(reader, out var enumType);
                        var arrayElementsAreDifferent = reader.ReadByte();
                        for (int i = 0; i < arrayLen; i++)
                        {
                            var elementType = arrayElementType;
                            if (arrayElementsAreDifferent == 1)
                            {
                                elementType = ReadEncodedTypeEnum(reader, out enumType);
                            }
                            GetConstantValueFromBlob(elementType, reader, out var data);
                            data.il2CppTypeEnum = elementType;
                            data.EnumType = enumType;
                            array[i] = data;
                        }
                        value.Value = array;
                    }
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_IL2CPP_TYPE_INDEX:
                    var typeIndex = reader.ReadCompressedInt32();
                    if (typeIndex == -1)
                    {
                        value.Value = null;
                    }
                    else
                    {
                        value.Value = il2Cpp.types[typeIndex];
                    }
                    return true;
                default:
                    throw new NotSupportedException($"不支持的元数据常量类型：{type}。");
            }
        }
        public Il2CppTypeEnum ReadEncodedTypeEnum(BinaryReader reader, out Il2CppType enumType)
        {
            enumType = null;
            var type = (Il2CppTypeEnum)reader.ReadByte();
            if (type == Il2CppTypeEnum.IL2CPP_TYPE_ENUM)
            {
                var enumTypeIndex = reader.ReadCompressedInt32();
                enumType = il2Cpp.types[enumTypeIndex];
                var typeDef = GetTypeDefinitionFromIl2CppType(enumType);
                type = il2Cpp.types[typeDef.elementTypeIndex].type;
            }
            return type;
        }
}
