#nullable enable
using System;
using System.Collections.Generic;
using Cpp2CS.Input.Portable;
using Il2CppDumper;

namespace Cpp2CS.Input
{
    /// <summary>
    /// ModelBuilder 使用的元数据视图。旧版本沿用 Il2CppDumper 的解析结果，
    /// 新版本由 <see cref="PortableMetadata"/> 读取后提供同样的对象。
    /// </summary>
    internal sealed class MetadataSource
    {
        private readonly Metadata? dumper;
        private readonly PortableMetadata? portable;
        private Il2Cpp il2Cpp;
        private readonly Il2CppExecutor? executor;

        private MetadataSource(Metadata? dumper, PortableMetadata? portable, Il2Cpp il2Cpp, Il2CppExecutor? executor)
        {
            this.dumper = dumper;
            this.portable = portable;
            this.il2Cpp = il2Cpp;
            this.executor = executor;
        }

        public static MetadataSource FromDumper(Metadata metadata, Il2Cpp il2Cpp)
            => new(metadata, null, il2Cpp, new Il2CppExecutor(metadata, il2Cpp));

        public static MetadataSource FromPortable(PortableMetadata metadata, Il2Cpp il2Cpp)
            => new(null, metadata, il2Cpp, null);

        public void SetRuntime(Il2Cpp runtime) => il2Cpp = runtime;

        public bool IsPortable => portable is not null;
        public Metadata? Dumper => dumper;
        public Il2CppExecutor? Executor => executor;

        public double Version => portable?.Version ?? dumper!.Version;
        public Il2CppGlobalMetadataHeader header => portable?.header ?? dumper!.header;
        public Il2CppImageDefinition[] imageDefs => portable?.imageDefs ?? dumper!.imageDefs;
        public Il2CppAssemblyDefinition[] assemblyDefs => portable?.assemblyDefs ?? dumper!.assemblyDefs;
        public Il2CppTypeDefinition[] typeDefs => portable?.typeDefs ?? dumper!.typeDefs;
        public Il2CppMethodDefinition[] methodDefs => portable?.methodDefs ?? dumper!.methodDefs;
        public Il2CppParameterDefinition[] parameterDefs => portable?.parameterDefs ?? dumper!.parameterDefs;
        public Il2CppFieldDefinition[] fieldDefs => portable?.fieldDefs ?? dumper!.fieldDefs;
        public Il2CppPropertyDefinition[] propertyDefs => portable?.propertyDefs ?? dumper!.propertyDefs;
        public Il2CppEventDefinition[] eventDefs => portable?.eventDefs ?? dumper!.eventDefs;
        public Il2CppFieldRef[] fieldRefs => portable?.fieldRefs ?? dumper!.fieldRefs;
        public Il2CppStringLiteral[] stringLiterals => portable?.stringLiterals ?? dumper!.stringLiterals;
        public Il2CppGenericContainer[] genericContainers => portable?.genericContainers ?? dumper!.genericContainers;
        public Il2CppGenericParameter[] genericParameters => portable?.genericParameters ?? dumper!.genericParameters;
        public int[] constraintIndices => portable?.constraintIndices ?? dumper!.constraintIndices;
        public int[] interfaceIndices => portable?.interfaceIndices ?? dumper!.interfaceIndices;
        public int[] nestedTypeIndices => portable?.nestedTypeIndices ?? dumper!.nestedTypeIndices;
        public uint[] vtableMethods => portable?.vtableMethods ?? dumper!.vtableMethods;
        public Il2CppCustomAttributeDataRange[] attributeDataRanges => portable?.attributeDataRanges ?? dumper!.attributeDataRanges;
        public Il2CppCustomAttributeTypeRange[] attributeTypeRanges => portable is null ? dumper!.attributeTypeRanges : [];
        public int[] attributeTypes => portable is null ? dumper!.attributeTypes : [];
        public Dictionary<Il2CppMetadataUsage, SortedDictionary<uint, uint>> metadataUsageDic =>
            portable is null ? dumper!.metadataUsageDic ?? new() : portable.metadataUsageDic;
        public long metadataUsagesCount => portable?.metadataUsagesCount ?? dumper!.metadataUsagesCount;

        public string GetStringFromIndex(uint index) => portable?.GetStringFromIndex(index) ?? dumper!.GetStringFromIndex(index);
        public string GetStringLiteralFromIndex(uint index) => portable?.GetStringLiteralFromIndex(index) ?? dumper!.GetStringLiteralFromIndex(index);

        public bool GetFieldDefaultValueFromIndex(int index, out Il2CppFieldDefaultValue value) =>
            portable is null ? dumper!.GetFieldDefaultValueFromIndex(index, out value) : portable.GetFieldDefaultValueFromIndex(index, out value);

        public bool GetParameterDefaultValueFromIndex(int index, out Il2CppParameterDefaultValue value) =>
            portable is null ? dumper!.GetParameterDefaultValueFromIndex(index, out value) : portable.GetParameterDefaultValueFromIndex(index, out value);

        public ulong GetDefaultValueFromIndex(int index) =>
            portable?.GetDefaultValueFromIndex(index) ?? dumper!.GetDefaultValueFromIndex(index);

        public ulong Position
        {
            get => portable?.Position ?? dumper!.Position;
            set
            {
                if (portable is not null) portable.Position = value;
                else dumper!.Position = value;
            }
        }

        public byte[] ReadBytes(int count) => portable?.ReadBytes(count) ?? dumper!.ReadBytes(count);
        public uint ReadCompressedUInt32() => portable?.ReadCompressedUInt32() ?? dumper!.ReadCompressedUInt32();
        public int ReadInt32() => portable?.ReadInt32() ?? dumper!.ReadInt32();

        public int InterfaceOffsetPairSize => portable is null ? 8 : portable.TypeIndexSize + sizeof(int);
        public int ReadTypeIndex() => portable?.ReadIndex(portable.TypeIndexSize) ?? dumper!.ReadInt32();

        public uint GetDecodedMethodIndex(uint index) => portable is null
            ? dumper!.GetDecodedMethodIndex(index)
            : (index & 0x1FFFFFFEU) >> 1;

        public bool TryGetDefaultValue(int typeIndex, int dataIndex, out object? value)
        {
            if (executor is not null) return executor.TryGetDefaultValue(typeIndex, dataIndex, out value!);
            return PortableValueReader.TryGetDefaultValue(portable!, il2Cpp, typeIndex, dataIndex, out value);
        }

        public Il2CppGenericParameter GetGenericParameterFromType(Il2CppType type)
        {
            if (executor is not null) return executor.GetGenericParameteFromIl2CppType(type);
            var index = il2Cpp.Version >= 27 && il2Cpp.IsDumped
                ? (int)((type.data.genericParameterHandle - il2Cpp.ImageBase - (ulong)header.genericParametersOffset) / (ulong)portable!.GenericParameterSize)
                : type.data.genericParameterIndex;
            return portable!.genericParameters[index];
        }

        public IReadOnlyList<CustomAttributeReaderVisitor> VisitCustomAttributes(byte[] data)
        {
            if (executor is not null)
            {
                var reader = new CustomAttributeDataReader(executor, data);
                var values = new CustomAttributeReaderVisitor[reader.Count];
                for (var i = 0; i < values.Length; i++) values[i] = reader.VisitCustomAttributeData();
                return values;
            }
            return PortableAttributeReader.VisitAll(portable!, il2Cpp, data);
        }
    }
}
