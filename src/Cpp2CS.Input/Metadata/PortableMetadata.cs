#nullable enable
using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using Il2CppDumper;

namespace Cpp2CS.Input.Portable
{
    /// <summary>
    /// 读取 v106/v107 按 SECTION(offset,size,count) 组织的元数据。布局取自 LibCpp2IL 的元数据定义
    /// （MIT，https://github.com/SamboyCoding/Cpp2IL），输出沿用 Il2CppDumper 的元数据对象，
    /// 避免恢复管线跟着换类型。
    /// </summary>
    internal sealed class PortableMetadata
    {
        public const uint Magic = 0xFAB11BAF;
        private const int Free = -1;

        private readonly byte[] bytes;
        private readonly Dictionary<string, SectionInfo> sections = new(StringComparer.Ordinal);
        private readonly Dictionary<uint, string> strings = new();
        private readonly Dictionary<uint, string> literals = new();
        private readonly Dictionary<int, Il2CppFieldDefaultValue> fieldDefaults = new();
        private readonly Dictionary<int, Il2CppParameterDefaultValue> parameterDefaults = new();

        public int Version { get; }
        public byte[] RawBytes => bytes;
        public Il2CppGlobalMetadataHeader header { get; } = new();
        public Il2CppTypeDefinition[] typeDefs { get; private set; } = [];
        public Il2CppMethodDefinition[] methodDefs { get; private set; } = [];
        public Il2CppParameterDefinition[] parameterDefs { get; private set; } = [];
        public Il2CppFieldDefinition[] fieldDefs { get; private set; } = [];
        public Il2CppPropertyDefinition[] propertyDefs { get; private set; } = [];
        public Il2CppEventDefinition[] eventDefs { get; private set; } = [];
        public Il2CppImageDefinition[] imageDefs { get; private set; } = [];
        public Il2CppAssemblyDefinition[] assemblyDefs { get; private set; } = [];
        public Il2CppFieldRef[] fieldRefs { get; private set; } = [];
        public Il2CppStringLiteral[] stringLiterals { get; private set; } = [];
        public Il2CppGenericContainer[] genericContainers { get; private set; } = [];
        public Il2CppGenericParameter[] genericParameters { get; private set; } = [];
        public int[] constraintIndices { get; private set; } = [];
        public int[] interfaceIndices { get; private set; } = [];
        public int[] nestedTypeIndices { get; private set; } = [];
        public uint[] vtableMethods { get; private set; } = [];
        public Il2CppCustomAttributeDataRange[] attributeDataRanges { get; private set; } = [];
        public Dictionary<Il2CppMetadataUsage, SortedDictionary<uint, uint>> metadataUsageDic { get; } = new();
        public int metadataUsagesCount => 0;
        public int GenericParameterSize { get; private set; } = 14;
        public int TypeIndexSize { get; private set; }
        public ulong Position { get; set; }

        private PortableMetadata(byte[] bytes)
        {
            this.bytes = bytes;
            if (bytes.Length < 8) throw new InvalidDataException("元数据文件过短");
            var sanity = BinaryPrimitives.ReadUInt32LittleEndian(bytes);
            if (sanity != Magic) throw new InvalidDataException($"元数据 magic 不符：0x{sanity:x8}");
            Version = BinaryPrimitives.ReadInt32LittleEndian(bytes.AsSpan(4));
            if (Version is < 106 or > 107) throw new NotSupportedException($"PortableMetadata 只处理 v106/v107，实际 {Version}");
            ReadHeader();
        }

        public static PortableMetadata Read(string path) => new(File.ReadAllBytes(path));

        public static PortableMetadata Read(byte[] bytes) => new(bytes);

        private void ReadHeader()
        {
            var at = 8;
            SectionInfo Next()
            {
                var width = Version >= 38 ? 12 : 8;
                var section = new SectionInfo(
                    BinaryPrimitives.ReadInt32LittleEndian(bytes.AsSpan(at)),
                    BinaryPrimitives.ReadInt32LittleEndian(bytes.AsSpan(at + 4)),
                    width == 12 ? BinaryPrimitives.ReadInt32LittleEndian(bytes.AsSpan(at + 8)) : 0);
                at += width;
                return section;
            }

            sections["stringLiteral"] = Next();
            sections["stringLiteralData"] = Next();
            sections["string"] = Next();
            sections["events"] = Next();
            sections["properties"] = Next();
            if (Version >= 111) sections["methodSigs"] = Next();
            sections["methods"] = Next();
            sections["parameterDefaultValues"] = Next();
            sections["fieldDefaultValues"] = Next();
            sections["fieldAndParameterDefaultValueData"] = Next();
            sections["fieldMarshaledSizes"] = Next();
            sections["parameters"] = Next();
            sections["fields"] = Next();
            sections["genericParameters"] = Next();
            sections["genericParameterConstraints"] = Next();
            sections["genericContainers"] = Next();
            sections["nestedTypes"] = Next();
            sections["interfaces"] = Next();
            sections["vtableMethods"] = Next();
            sections["interfaceOffsets"] = Next();
            sections["typeDefinitions"] = Next();
            if (Version >= 104) sections["typeInlineArrays"] = Next();
            if (Version <= 24.15f) sections["rgctxEntries"] = Next();
            sections["images"] = Next();
            sections["assemblies"] = Next();
            if (Version < 27)
            {
                sections["metadataUsageLists"] = Next();
                sections["metadataUsagePairs"] = Next();
            }
            sections["fieldRefs"] = Next();
            sections["referencedAssemblies"] = Next();
            if (Version < 29)
            {
                sections["attributesInfo"] = Next();
                sections["attributeTypes"] = Next();
            }
            else
            {
                sections["attributeData"] = Next();
                sections["attributeDataRange"] = Next();
            }
            sections["unresolvedVirtualCallParameterTypes"] = Next();
            sections["unresolvedVirtualCallParameterRanges"] = Next();
            sections["windowsRuntimeTypeNames"] = Next();
            if (Version >= 27) sections["windowsRuntimeStrings"] = Next();
            if (Version >= 24) sections["exportedTypeDefinitions"] = Next();
            if (Version >= 108)
            {
                sections["methodSpecsOnGenericType"] = Next();
                sections["genericMethodSpecsOnType"] = Next();
                sections["methodSpecs"] = Next();
                sections["genericMethodFunctionsDefinitions"] = Next();
                sections["genericMethodFunctionsDefinitionsWithAdjustor"] = Next();
                sections["invokerIndices"] = Next();
                sections["rgctxRanges"] = Next();
                sections["rgctxValues"] = Next();
                sections["staticConstructorTypeIndices"] = Next();
            }
            if (Version >= 111)
            {
                sections["generatedMethodTypeInfos"] = Next();
                sections["generatedMethodTokens"] = Next();
            }

            FillHeader();
            ReadWidths();
        }

        private SectionInfo GetSection(string name) => sections.TryGetValue(name, out var section)
            ? section : throw new InvalidDataException($"元数据缺少段 {name}");

        private void FillHeader()
        {
            header.sanity = Magic;
            header.version = Version;
            header.stringLiteralOffset = (uint)GetSection("stringLiteral").Offset;
            header.stringLiteralSize = GetSection("stringLiteral").Size;
            header.stringLiteralDataOffset = (uint)GetSection("stringLiteralData").Offset;
            header.stringLiteralDataSize = GetSection("stringLiteralData").Size;
            header.stringOffset = (uint)GetSection("string").Offset;
            header.stringSize = GetSection("string").Size;
            header.eventsOffset = (uint)GetSection("events").Offset;
            header.eventsSize = GetSection("events").Size;
            header.propertiesOffset = (uint)GetSection("properties").Offset;
            header.propertiesSize = GetSection("properties").Size;
            header.methodsOffset = (uint)GetSection("methods").Offset;
            header.methodsSize = GetSection("methods").Size;
            header.parameterDefaultValuesOffset = (uint)GetSection("parameterDefaultValues").Offset;
            header.parameterDefaultValuesSize = GetSection("parameterDefaultValues").Size;
            header.fieldDefaultValuesOffset = (uint)GetSection("fieldDefaultValues").Offset;
            header.fieldDefaultValuesSize = GetSection("fieldDefaultValues").Size;
            header.fieldAndParameterDefaultValueDataOffset = (uint)GetSection("fieldAndParameterDefaultValueData").Offset;
            header.fieldAndParameterDefaultValueDataSize = GetSection("fieldAndParameterDefaultValueData").Size;
            header.fieldMarshaledSizesOffset = GetSection("fieldMarshaledSizes").Offset;
            header.fieldMarshaledSizesSize = GetSection("fieldMarshaledSizes").Size;
            header.parametersOffset = (uint)GetSection("parameters").Offset;
            header.parametersSize = GetSection("parameters").Size;
            header.fieldsOffset = (uint)GetSection("fields").Offset;
            header.fieldsSize = GetSection("fields").Size;
            header.genericParametersOffset = (uint)GetSection("genericParameters").Offset;
            header.genericParametersSize = GetSection("genericParameters").Size;
            header.genericParameterConstraintsOffset = (uint)GetSection("genericParameterConstraints").Offset;
            header.genericParameterConstraintsSize = GetSection("genericParameterConstraints").Size;
            header.genericContainersOffset = (uint)GetSection("genericContainers").Offset;
            header.genericContainersSize = GetSection("genericContainers").Size;
            header.nestedTypesOffset = (uint)GetSection("nestedTypes").Offset;
            header.nestedTypesSize = GetSection("nestedTypes").Size;
            header.interfacesOffset = (uint)GetSection("interfaces").Offset;
            header.interfacesSize = GetSection("interfaces").Size;
            header.vtableMethodsOffset = (uint)GetSection("vtableMethods").Offset;
            header.vtableMethodsSize = GetSection("vtableMethods").Size;
            header.interfaceOffsetsOffset = GetSection("interfaceOffsets").Offset;
            header.interfaceOffsetsSize = GetSection("interfaceOffsets").Size;
            header.typeDefinitionsOffset = (uint)GetSection("typeDefinitions").Offset;
            header.typeDefinitionsSize = GetSection("typeDefinitions").Size;
            header.imagesOffset = (uint)GetSection("images").Offset;
            header.imagesSize = GetSection("images").Size;
            header.assembliesOffset = (uint)GetSection("assemblies").Offset;
            header.assembliesSize = GetSection("assemblies").Size;
            header.fieldRefsOffset = (uint)GetSection("fieldRefs").Offset;
            header.fieldRefsSize = GetSection("fieldRefs").Size;
            header.referencedAssembliesOffset = GetSection("referencedAssemblies").Offset;
            header.referencedAssembliesSize = GetSection("referencedAssemblies").Size;
            if (Version >= 29)
            {
                header.attributeDataOffset = (uint)GetSection("attributeData").Offset;
                header.attributeDataSize = GetSection("attributeData").Size;
                header.attributeDataRangeOffset = (uint)GetSection("attributeDataRange").Offset;
                header.attributeDataRangeSize = GetSection("attributeDataRange").Size;
            }
            if (Version >= 24)
            {
                header.exportedTypeDefinitionsOffset = GetSection("exportedTypeDefinitions").Offset;
                header.exportedTypeDefinitionsSize = GetSection("exportedTypeDefinitions").Size;
            }
        }

        private int Width(int count) => count switch
        {
            <= byte.MaxValue => 1,
            <= ushort.MaxValue => 2,
            _ => 4,
        };

        private void ReadWidths()
        {
            var interfaceOffsets = GetSection("interfaceOffsets");
            if (interfaceOffsets.Count <= 0 || interfaceOffsets.Size % interfaceOffsets.Count != 0)
                throw new InvalidDataException($"interfaceOffsets 段无法推导类型索引宽度：{interfaceOffsets.Size}/{interfaceOffsets.Count}");
            TypeIndexSize = interfaceOffsets.Size / interfaceOffsets.Count - sizeof(int);
            if (TypeIndexSize is not (1 or 2 or 4)) throw new InvalidDataException($"类型索引宽度无效：{TypeIndexSize}");

            int typeDefWidth = Width(GetSection("typeDefinitions").Count);
            int genericContainerWidth = Width(GetSection("genericContainers").Count);
            int parameterWidth = Width(GetSection("parameters").Count);
            int interfaceOffsetWidth = Width(interfaceOffsets.Count);
            int eventWidth = Width(GetSection("events").Count);
            int propertyWidth = Width(GetSection("properties").Count);
            int nestedStartWidth = Width(GetSection("nestedTypes").Count);
            int methodWidth = Width(GetSection("methods").Count);
            int genericParameterWidth = Width(GetSection("genericParameters").Count);
            int fieldWidth = Width(GetSection("fields").Count);
            int defaultValueWidth = Width(GetSection("fieldAndParameterDefaultValueData").Count);
            GenericParameterSize = genericContainerWidth + 4 + 2 + 2 + 2 + 2;

            ReadArrays(typeDefWidth, genericContainerWidth, parameterWidth, interfaceOffsetWidth, eventWidth, propertyWidth,
                nestedStartWidth, methodWidth, genericParameterWidth, fieldWidth, defaultValueWidth);
        }

        private void ReadArrays(int typeDefWidth, int genericContainerWidth, int parameterWidth, int interfaceOffsetWidth,
            int eventWidth, int propertyWidth, int nestedStartWidth, int methodWidth, int genericParameterWidth, int fieldWidth,
            int defaultValueWidth)
        {
            typeDefs = Read(GetSection("typeDefinitions"), r =>
            {
                var d = new Il2CppTypeDefinition
                {
                    nameIndex = r.U32(),
                    namespaceIndex = r.U32(),
                };
                d.byvalTypeIndex = r.Var(TypeIndexSize);
                d.declaringTypeIndex = r.Var(TypeIndexSize);
                d.parentIndex = r.Var(TypeIndexSize);
                d.genericContainerIndex = r.Var(genericContainerWidth);
                d.flags = r.U32();
                d.fieldStart = r.Var(fieldWidth);
                d.methodStart = r.Var(methodWidth);
                d.eventStart = r.Var(eventWidth);
                d.propertyStart = r.Var(propertyWidth);
                d.nestedTypesStart = r.Var(nestedStartWidth);
                d.interfacesStart = r.Var(interfaceOffsetWidth);
                d.vtableStart = r.I32();
                d.interfaceOffsetsStart = r.Var(interfaceOffsetWidth);
                d.method_count = r.U16();
                d.property_count = r.U16();
                d.field_count = r.U16();
                d.event_count = r.U16();
                d.nested_type_count = r.U16();
                d.vtable_count = r.U16();
                d.interfaces_count = r.U16();
                d.interface_offsets_count = r.U16();
                d.bitfield = r.U32();
                d.token = r.U32();
                return d;
            });

            methodDefs = Read(GetSection("methods"), r =>
            {
                var d = new Il2CppMethodDefinition
                {
                    nameIndex = r.U32(),
                    declaringType = r.Var(typeDefWidth),
                    returnType = r.Var(TypeIndexSize),
                    returnParameterToken = r.I32(),
                    parameterStart = r.Var(parameterWidth),
                    genericContainerIndex = r.Var(genericContainerWidth),
                    token = r.U32(),
                    flags = r.U16(),
                    iflags = r.U16(),
                    slot = r.U16(),
                    parameterCount = r.U16(),
                };
                return d;
            });

            parameterDefs = Read(GetSection("parameters"), r => new Il2CppParameterDefinition
            {
                nameIndex = r.U32(),
                token = r.U32(),
                typeIndex = r.Var(TypeIndexSize),
            });

            fieldDefs = Read(GetSection("fields"), r => new Il2CppFieldDefinition
            {
                nameIndex = r.U32(),
                typeIndex = r.Var(TypeIndexSize),
                token = r.U32(),
            });

            propertyDefs = Read(GetSection("properties"), r => new Il2CppPropertyDefinition
            {
                nameIndex = r.U32(),
                get = r.Var(methodWidth),
                set = r.Var(methodWidth),
                attrs = r.U32(),
                token = r.U32(),
            });

            eventDefs = Read(GetSection("events"), r => new Il2CppEventDefinition
            {
                nameIndex = r.U32(),
                typeIndex = r.Var(TypeIndexSize),
                add = r.Var(methodWidth),
                remove = r.Var(methodWidth),
                raise = r.Var(methodWidth),
                token = r.U32(),
            });

            genericContainers = Read(GetSection("genericContainers"), r => new Il2CppGenericContainer
            {
                ownerIndex = r.I32(),
                type_argc = r.U16(),
                is_method = r.U8() != 0 ? 1 : 0,
                genericParameterStart = r.Var(genericParameterWidth),
            });

            genericParameters = Read(GetSection("genericParameters"), r => new Il2CppGenericParameter
            {
                ownerIndex = r.Var(genericContainerWidth),
                nameIndex = r.U32(),
                constraintsStart = r.I16(),
                constraintsCount = r.I16(),
                num = r.U16(),
                flags = (ushort)r.U16(),
            });

            imageDefs = Read(GetSection("images"), r => new Il2CppImageDefinition
            {
                nameIndex = r.U32(),
                assemblyIndex = r.I32(),
                typeStart = r.Var(typeDefWidth),
                typeCount = r.U32(),
                exportedTypeStart = r.Var(typeDefWidth),
                exportedTypeCount = r.U32(),
                entryPointIndex = r.Var(methodWidth),
                token = r.U32(),
                customAttributeStart = r.I32(),
                customAttributeCount = r.U32(),
            });

            assemblyDefs = Read(GetSection("assemblies"), r =>
            {
                var d = new Il2CppAssemblyDefinition { imageIndex = r.I32(), token = r.U32() };
                // v106 在 token 之后还有 moduleToken；Il2CppAssemblyDefinition 没有对应字段，跳过。
                _ = r.U32();
                d.referencedAssemblyStart = r.I32();
                d.referencedAssemblyCount = r.I32();
                d.aname = new Il2CppAssemblyNameDefinition
                {
                    nameIndex = r.U32(),
                    cultureIndex = r.U32(),
                    publicKeyIndex = r.U32(),
                    hash_alg = r.U32(),
                    hash_len = r.I32(),
                    flags = r.U32(),
                    major = r.I32(),
                    minor = r.I32(),
                    build = r.I32(),
                    revision = r.I32(),
                    public_key_token = r.Bytes(8),
                };
                return d;
            });

            fieldRefs = Read(GetSection("fieldRefs"), r => new Il2CppFieldRef
            {
                typeIndex = r.Var(TypeIndexSize),
                fieldIndex = r.Var(fieldWidth),
            });

            var literalSection = GetSection("stringLiteral");
            var literalData = GetSection("stringLiteralData");
            stringLiterals = Read(literalSection, r => new Il2CppStringLiteral { dataIndex = r.I32() });
            for (var i = 0; i < stringLiterals.Length; i++)
            {
                var begin = stringLiterals[i].dataIndex;
                var end = i + 1 < stringLiterals.Length ? stringLiterals[i + 1].dataIndex : literalData.Size;
                stringLiterals[i].length = (uint)Math.Max(0, end - begin);
            }

            ReadDefaultValues(fieldWidth, defaultValueWidth);
            ReadAttributeRanges();

            var vtable = GetSection("vtableMethods");
            vtableMethods = new uint[vtable.Count];
            for (var i = 0; i < vtableMethods.Length; i++)
                vtableMethods[i] = BinaryPrimitives.ReadUInt32LittleEndian(bytes.AsSpan(vtable.Offset + i * 4));

            var interfaces = GetSection("interfaces");
            interfaceIndices = ReadVariableArray(interfaces, TypeIndexSize);
            var constraints = GetSection("genericParameterConstraints");
            constraintIndices = ReadVariableArray(constraints, TypeIndexSize);
            var nested = GetSection("nestedTypes");
            // nestedTypes 表项固定为 int32，与 typeDefinitions 中的 nestedTypesStart 宽度无关。
            nestedTypeIndices = ReadVariableArray(nested, sizeof(int));
        }

        private void ReadDefaultValues(int fieldWidth, int defaultValueWidth)
        {
            var parameterWidth = Width(GetSection("parameters").Count);
            var fieldStride = fieldWidth + TypeIndexSize + defaultValueWidth;
            var fields = GetSection("fieldDefaultValues");
            for (var i = 0; i < fields.Count; i++)
            {
                var r = new Reader(bytes, fields.Offset + i * fieldStride);
                var value = new Il2CppFieldDefaultValue
                {
                    fieldIndex = r.Var(fieldWidth),
                    typeIndex = r.Var(TypeIndexSize),
                    dataIndex = r.Var(defaultValueWidth),
                };
                if (value.fieldIndex >= 0) fieldDefaults[value.fieldIndex] = value;
            }

            var parameterStride = parameterWidth + TypeIndexSize + defaultValueWidth;
            var parameters = GetSection("parameterDefaultValues");
            for (var i = 0; i < parameters.Count; i++)
            {
                var r = new Reader(bytes, parameters.Offset + i * parameterStride);
                var value = new Il2CppParameterDefaultValue
                {
                    parameterIndex = r.Var(parameterWidth),
                    typeIndex = r.Var(TypeIndexSize),
                    dataIndex = r.Var(defaultValueWidth),
                };
                if (value.parameterIndex >= 0) parameterDefaults[value.parameterIndex] = value;
            }
        }

        private void ReadAttributeRanges()
        {
            if (Version < 29) return;
            var SectionInfo = GetSection("attributeDataRange");
            attributeDataRanges = new Il2CppCustomAttributeDataRange[SectionInfo.Count];
            for (var i = 0; i < attributeDataRanges.Length; i++)
            {
                var at = SectionInfo.Offset + i * 8;
                attributeDataRanges[i] = new Il2CppCustomAttributeDataRange
                {
                    token = BinaryPrimitives.ReadUInt32LittleEndian(bytes.AsSpan(at)),
                    startOffset = BinaryPrimitives.ReadUInt32LittleEndian(bytes.AsSpan(at + 4)),
                };
            }
        }

        private int[] ReadVariableArray(SectionInfo section, int width)
        {
            var count = width == 0 ? 0 : section.Size / width;
            var values = new int[count];
            for (var i = 0; i < count; i++)
                values[i] = new Reader(bytes, section.Offset + i * width).Var(width);
            return values;
        }

        private T[] Read<T>(SectionInfo section, Func<Reader, T> read)
        {
            if (section.Count <= 0 || section.Size <= 0) return [];
            var result = new T[section.Count];
            var stride = section.Size / section.Count;
            for (var i = 0; i < result.Length; i++)
                result[i] = read(new Reader(bytes, section.Offset + i * stride));
            return result;
        }

        public string GetStringFromIndex(uint index)
        {
            if (strings.TryGetValue(index, out var cached)) return cached;
            var at = (int)header.stringOffset + (int)index;
            var end = at;
            while (end < bytes.Length && bytes[end] != 0) end++;
            var value = Encoding.UTF8.GetString(bytes, at, end - at);
            strings[index] = value;
            return value;
        }

        public string GetStringLiteralFromIndex(uint index)
        {
            if (literals.TryGetValue(index, out var cached)) return cached;
            var literal = stringLiterals[index];
            var at = (int)header.stringLiteralDataOffset + literal.dataIndex;
            // 字符串字面量按表中相邻 dataIndex 的差值定长；末尾可能带一个终止符，不能扫描到文件末尾。
            var length = (int)Math.Min(literal.length, (uint)Math.Max(0, bytes.Length - at));
            if (length > 0 && bytes[at + length - 1] == 0) length--;
            var value = Encoding.UTF8.GetString(bytes, at, length);
            literals[index] = value;
            return value;
        }

        public bool GetFieldDefaultValueFromIndex(int index, out Il2CppFieldDefaultValue value)
            => fieldDefaults.TryGetValue(index, out value!);

        public bool GetParameterDefaultValueFromIndex(int index, out Il2CppParameterDefaultValue value)
            => parameterDefaults.TryGetValue(index, out value!);

        public ulong GetDefaultValueFromIndex(int index) => (ulong)(header.fieldAndParameterDefaultValueDataOffset + (uint)index);

        public byte[] ReadBytes(int count)
        {
            var at = (int)Position;
            var value = bytes.AsSpan(at, count).ToArray();
            Position += (ulong)count;
            return value;
        }

        public uint ReadCompressedUInt32()
        {
            var at = (int)Position;
            var read = bytes[at++];
            uint value;
            if ((read & 0x80) == 0) value = read;
            else if ((read & 0xC0) == 0x80)
            {
                value = (uint)((read & ~0x80u) << 8);
                value |= bytes[at++];
            }
            else if ((read & 0xE0) == 0xC0)
            {
                value = (uint)((read & ~0xC0u) << 24);
                value |= (uint)bytes[at++] << 16;
                value |= (uint)bytes[at++] << 8;
                value |= bytes[at++];
            }
            else if ((read & 0xF0) == 0xE0)
            {
                value = (uint)((read & ~0xE0u) << 24);
                value |= (uint)bytes[at++] << 24;
                value |= (uint)bytes[at++] << 16;
                value |= (uint)bytes[at++] << 8;
                value |= bytes[at++];
            }
            else if (read == 0xF0)
            {
                value = uint.MaxValue;
            }
            else throw new InvalidDataException("压缩整数格式无效");
            Position = (ulong)at;
            return value;
        }

        public int ReadInt32()
        {
            var value = BinaryPrimitives.ReadInt32LittleEndian(bytes.AsSpan((int)Position));
            Position += 4;
            return value;
        }

        public int ReadIndex(int width)
        {
            var at = (int)Position;
            var value = width switch
            {
                1 => bytes[at] == byte.MaxValue ? Free : bytes[at],
                2 => BinaryPrimitives.ReadUInt16LittleEndian(bytes.AsSpan(at)) is var v && v == ushort.MaxValue ? Free : v,
                4 => BinaryPrimitives.ReadInt32LittleEndian(bytes.AsSpan(at)),
                _ => throw new InvalidDataException($"索引宽度无效：{width}"),
            };
            Position += (ulong)width;
            return value;
        }

        private readonly record struct SectionInfo(int Offset, int Size, int Count);

        private ref struct Reader
        {
            private readonly byte[] bytes;
            private int at;

            public Reader(byte[] bytes, int at)
            {
                this.bytes = bytes;
                this.at = at;
            }

            public byte U8() => bytes[at++];

            public ushort U16()
            {
                var value = BinaryPrimitives.ReadUInt16LittleEndian(bytes.AsSpan(at));
                at += 2;
                return value;
            }

            public short I16()
            {
                var value = BinaryPrimitives.ReadInt16LittleEndian(bytes.AsSpan(at));
                at += 2;
                return value;
            }

            public uint U32()
            {
                var value = BinaryPrimitives.ReadUInt32LittleEndian(bytes.AsSpan(at));
                at += 4;
                return value;
            }

            public int I32()
            {
                var value = BinaryPrimitives.ReadInt32LittleEndian(bytes.AsSpan(at));
                at += 4;
                return value;
            }

            public int Var(int width)
            {
                switch (width)
                {
                    case 1:
                        {
                            var value = bytes[at++];
                            return value == byte.MaxValue ? Free : value;
                        }
                    case 2:
                        {
                            var value = BinaryPrimitives.ReadUInt16LittleEndian(bytes.AsSpan(at));
                            at += 2;
                            return value == ushort.MaxValue ? Free : value;
                        }
                    case 4:
                        return I32();
                    default:
                        throw new InvalidDataException($"索引宽度无效：{width}");
                }
            }

            public byte[] Bytes(int count)
            {
                var value = bytes.AsSpan(at, count).ToArray();
                at += count;
                return value;
            }
        }
    }
}




