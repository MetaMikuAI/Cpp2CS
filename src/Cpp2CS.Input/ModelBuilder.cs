#nullable enable
using System.Reflection;
using System.Collections.Immutable;
using Cpp2CS.Model;
using Cpp2CS.Native.Images;
using Cpp2CS.Runtime;
using Il2CppDumper;
namespace Cpp2CS.Input
{
    /// <summary>
    /// 从映像与元数据建立 <see cref="ProgramModel"/>。
    /// Il2CppDumper 提供元数据解析及结构容器；映像地址和指针均经 <see cref="IImage"/> 读取。
    /// </summary>
    public sealed class ModelBuilder
    {
        private readonly Metadata metadata;
        private readonly RuntimeData il2Cpp;
        private readonly Il2CppExecutor executor;
        private readonly TypeDef[] types;
        private readonly Dictionary<Il2CppType, TypeRef> converted = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<int, GenericParameterDef> genericParameters = new();

        private ModelBuilder(Metadata metadata, RuntimeData il2Cpp)
        {
            this.metadata = metadata;
            this.il2Cpp = il2Cpp;
            executor = new Il2CppExecutor(metadata, il2Cpp);
            types = new TypeDef[metadata.typeDefs.Length];
        }

        public static (ProgramModel Model, ModelRegistration Registration) Load(IImage image, string metadataPath, RuntimeSpec spec)
        {
            using var stream = File.OpenRead(metadataPath);
            return Read(image, stream, spec);
        }

        public static (ProgramModel Model, ModelRegistration Registration) Read(IImage image, Stream metadataStream, RuntimeSpec spec)
        {
            using var bytes = new MemoryStream();
            metadataStream.CopyTo(bytes);
            bytes.Position = 0;
            using (var header = new BinaryReader(bytes, System.Text.Encoding.UTF8, true))
            {
                if (bytes.Length < 8 || header.ReadUInt32() != 0xFAB11BAF)
                    throw new InvalidDataException("元数据文件头无效。");
                var version = header.ReadInt32();
                if (version != 31) throw new NotSupportedException($"不支持的元数据版本 {version}；当前支持 v31。");
            }
            bytes.Position = 0;
            using var metadata = new Metadata(bytes);
            var data = new RuntimeData(image, spec);
            var addresses = RegistrationLocator.Find(data, metadata);
            data.Initialize(addresses.Metadata, metadata);
            var builder = new ModelBuilder(metadata, data);
            var model = builder.Build(data.Read<Il2CppMetadataRegistration>(addresses.Metadata));
            var instances = data.methodSpecs.Select((s, i) => new GenericInstantiation(i, s.classIndexIndex, s.methodIndexIndex, model.MethodSpecs[i])).ToImmutableArray();
            return (model, new ModelRegistration(addresses.Code, addresses.Metadata, instances));
        }

        private string String(uint index) => metadata.GetStringFromIndex(index);

        private static int DecodePackingSize(uint bitfield)
        {
            var encoded = (int)((bitfield >> 6) & 15);
            if (encoded > 8) throw new InvalidDataException($"未知 packing 编码 {encoded}");
            return encoded == 0 ? 0 : 1 << (encoded - 1);
        }

        private ProgramModel Build(Il2CppMetadataRegistration registration)
        {
            foreach (var imageDef in metadata.imageDefs)
            {
                var assembly = String(imageDef.nameIndex);
                for (var i = imageDef.typeStart; i < imageDef.typeStart + imageDef.typeCount; i++)
                {
                    var def = metadata.typeDefs[i];
                    var flags = (TypeAttributes)def.flags;
                    types[i] = new TypeDef
                    {
                        Index = i,
                        Assembly = assembly,
                        Namespace = String(def.namespaceIndex),
                        Name = String(def.nameIndex),
                        Token = def.token,
                        Attributes = flags,
                        IsValueType = def.IsValueType,
                        IsEnum = def.IsEnum,
                        PackingSize = DecodePackingSize(def.bitfield),
                        ClassSizeIsDefault = ((def.bitfield >> 11) & 1) != 0,
                    };
                }
            }
            if (types.Any(t => t is null)) throw new InvalidDataException("存在不属于任何 image 的类型定义");

            var fields = new FieldDef[metadata.fieldDefs.Length];
            var methods = new MethodDef[metadata.methodDefs.Length];
            for (var i = 0; i < types.Length; i++)
            {
                var def = metadata.typeDefs[i];
                var type = types[i];
                if (def.declaringTypeIndex >= 0) type.DeclaringType = Definition(il2Cpp.types[def.declaringTypeIndex]);
                if (def.genericContainerIndex >= 0) type.GenericParameters = GenericParameters(def.genericContainerIndex);
                if (def.parentIndex >= 0) type.BaseType = Convert(il2Cpp.types[def.parentIndex]);
                type.Interfaces = Enumerable.Range(def.interfacesStart, def.interfaces_count)
                    .Select(k => Convert(il2Cpp.types[metadata.interfaceIndices[k]])).ToArray();
                type.NestedTypes = Enumerable.Range(def.nestedTypesStart, def.nested_type_count)
                    .Select(k => types[metadata.nestedTypeIndices[k]]).ToArray();

                var typeFields = new List<FieldDef>();
                for (var f = def.fieldStart; f < def.fieldStart + def.field_count; f++)
                {
                    var fieldDef = metadata.fieldDefs[f];
                    var fieldType = il2Cpp.types[fieldDef.typeIndex];
                    var attributes = (FieldAttributes)fieldType.attrs;
                    // 默认值项的 dataIndex 为 -1 表示 null（libil2cpp 的 kDefaultValueIndexNull）
                    object? constant = null;
                    if ((attributes & FieldAttributes.HasFieldRVA) == 0
                        && metadata.GetFieldDefaultValueFromIndex(f, out var defaultValue) && defaultValue.dataIndex != -1
                        && executor.TryGetDefaultValue(defaultValue.typeIndex, defaultValue.dataIndex, out var value))
                        constant = value;
                    var isStatic = (attributes & FieldAttributes.Static) != 0;
                    var offset = (attributes & FieldAttributes.Literal) != 0 ? -1
                        : il2Cpp.GetFieldOffsetFromIndex(i, f - def.fieldStart, f, type.IsValueType, isStatic);
                    var field = new FieldDef
                    {
                        Index = f,
                        Owner = type,
                        Name = String(fieldDef.nameIndex),
                        Type = Convert(fieldType, ignoreByRef: true),
                        Attributes = attributes,
                        Offset = offset,
                        Constant = constant,
                        Token = fieldDef.token,
                    };
                    fields[f] = field;
                    typeFields.Add(field);
                }
                type.Fields = typeFields;

                var typeMethods = new List<MethodDef>();
                for (var m = def.methodStart; m < def.methodStart + def.method_count; m++)
                {
                    var methodDef = metadata.methodDefs[m];
                    var method = new MethodDef
                    {
                        Index = m,
                        Owner = type,
                        Name = String(methodDef.nameIndex),
                        Token = methodDef.token,
                        ReturnParameterToken = (uint)methodDef.returnParameterToken,
                        Attributes = (MethodAttributes)methodDef.flags,
                        ImplAttributes = (MethodImplAttributes)methodDef.iflags,
                        Slot = methodDef.slot == ushort.MaxValue ? -1 : methodDef.slot,
                        ReturnType = Convert(il2Cpp.types[methodDef.returnType]),
                        
                    };
                    if (methodDef.genericContainerIndex >= 0) method.GenericParameters = GenericParameters(methodDef.genericContainerIndex);
                    var parameters = new ParameterDef[methodDef.parameterCount];
                    for (var p = 0; p < parameters.Length; p++)
                    {
                        var parameterDef = metadata.parameterDefs[methodDef.parameterStart + p];
                        var parameterType = il2Cpp.types[parameterDef.typeIndex];
                        object? defaultValue = null;
                        var hasDefault = metadata.GetParameterDefaultValueFromIndex(methodDef.parameterStart + p, out var parameterDefault)
                            && (parameterDefault.dataIndex == -1
                                || executor.TryGetDefaultValue(parameterDefault.typeIndex, parameterDefault.dataIndex, out defaultValue));
                        parameters[p] = new ParameterDef(String(parameterDef.nameIndex), Convert(parameterType), (ParameterAttributes)parameterType.attrs, defaultValue, hasDefault)
                        {
                            Token = parameterDef.token,
                        };
                    }
                    method.Parameters = parameters;
                    methods[m] = method;
                    typeMethods.Add(method);
                }
                type.Methods = typeMethods;
            }

            var properties = new PropertyDef[metadata.propertyDefs.Length];
            var sizes = il2Cpp.Read<ulong>(registration.typeDefinitionsSizes, registration.typeDefinitionsSizesCount);
            for (var i = 0; i < types.Length; i++)
            {
                var def = metadata.typeDefs[i];
                types[i].Properties = Enumerable.Range(def.propertyStart, def.property_count).Select(k =>
                {
                    var property = metadata.propertyDefs[k];
                    return properties[k] = new PropertyDef
                    {
                        Name = String(property.nameIndex),
                        Attributes = (PropertyAttributes)property.attrs,
                        Token = property.token,
                        Getter = property.get >= 0 ? methods[def.methodStart + property.get] : null,
                        Setter = property.set >= 0 ? methods[def.methodStart + property.set] : null,
                    };
                }).ToArray();
                types[i].Events = Enumerable.Range(def.eventStart, def.event_count).Select(k =>
                {
                    var definition = metadata.eventDefs[k];
                    var eventType = il2Cpp.types[definition.typeIndex];
                    return new EventDef
                    {
                        Name = String(definition.nameIndex),
                        Type = Convert(eventType),
                        Attributes = (EventAttributes)eventType.attrs,
                        Token = definition.token,
                        Add = definition.add >= 0 ? methods[def.methodStart + definition.add] : null,
                        Remove = definition.remove >= 0 ? methods[def.methodStart + definition.remove] : null,
                        Raise = definition.raise >= 0 ? methods[def.methodStart + definition.raise] : null,
                    };
                }).ToArray();
                // Il2CppTypeDefinitionSizes.instance_size：值类型也按装箱对象计（含对象头）
                if (i < sizes.Length && sizes[i] != 0)
                {
                    var instanceSize = checked((int)il2Cpp.Number(sizes[i], "Il2CppTypeDefinitionSizes", "instance_size"));
                    types[i].Size = types[i].IsValueType ? instanceSize - ObjectHeaderSize : instanceSize;
                }
            }

            var runtimeTypes = il2Cpp.types.Select(t => Convert(t)).ToArray();
            var methodSpecs = il2Cpp.methodSpecs.Select(spec => new MethodRef(
                methods[spec.methodDefinitionIndex],
                spec.classIndexIndex >= 0 ? Instantiation(il2Cpp.genericInsts[spec.classIndexIndex]) : [],
                spec.methodIndexIndex >= 0 ? Instantiation(il2Cpp.genericInsts[spec.methodIndexIndex]) : [])).ToArray();
            var fieldRefs = metadata.fieldRefs.Select(r =>
            {
                var owner = Convert(il2Cpp.types[r.typeIndex]);
                var definition = owner is DefinitionRef d ? d.Definition : throw new InvalidDataException($"FieldRef 所有者不是类型定义：{owner}");
                return new FieldRef(fields[metadata.typeDefs[definition.Index].fieldStart + r.fieldIndex], owner);
            }).ToArray();
            var literals = Enumerable.Range(0, metadata.stringLiterals.Length).Select(k => metadata.GetStringLiteralFromIndex((uint)k)).ToArray();

            ReadInitialValues(fields);

            var assemblies = metadata.imageDefs.Select(imageDef =>
            {
                var name = metadata.assemblyDefs[imageDef.assemblyIndex].aname;
                return new AssemblyDef
                {
                    Name = String(imageDef.nameIndex),
                    AssemblyName = String(name.nameIndex),
                    // 生成的程序集（__Generated）的 build/revision 为 -1
                    Version = name.build < 0 ? new Version(name.major, name.minor) : new Version(name.major, name.minor, name.build, name.revision),
                    Culture = String(name.cultureIndex),
                    PublicKey = PublicKey(name),
                    Types = Enumerable.Range(imageDef.typeStart, (int)imageDef.typeCount).Select(k => types[k]).ToArray(),
                };
            }).ToArray();
            ReadCustomAttributes(assemblies, methods, fields, properties);
            foreach (var field in fields)
                field.IsThreadStatic = field.CustomAttributes.Any(a => a.Constructor.Owner.FullName == "System.ThreadStaticAttribute"
                    && a.Constructor.Owner.Assembly == "mscorlib.dll");

            var model = new ProgramModel
            {
                MetadataVersion = metadata.Version,
                Assemblies = assemblies,
                Types = types,
                Methods = methods,
                Fields = fields,
                RuntimeTypes = runtimeTypes,
                MethodSpecs = methodSpecs,
                FieldRefs = fieldRefs,
                StringLiterals = literals,
            };

            for (var i = 0; i < types.Length; i++)
            {
                var def = metadata.typeDefs[i];
                types[i].VTable = Enumerable.Range(def.vtableStart, def.vtable_count).Select(k =>
                {
                    var encoded = metadata.vtableMethods[k];
                    // 编码种类 0 为空槽位（v27+ 空槽位写作 1）
                    if (Metadata.GetEncodedIndexType(encoded) == 0) return null;
                    var usage = MetadataTokens.Decode(model, Metadata.GetEncodedIndexType(encoded), metadata.GetDecodedMethodIndex(encoded));
                    return usage?.Value as MethodRef ?? throw new InvalidDataException($"vtable 槽位编码无法解析：0x{encoded:x}");
                }).ToArray();
                types[i].InterfaceOffsets = InterfaceOffsets(def);
            }
            // 抽象虚方法没有代码入口，元数据虚表可留空；托管 callvirt 仍需其声明与槽位。
            foreach (var type in types)
            {
                var table = type.VTable.ToArray();
                for (var current = new DefinitionRef(type, type.GenericParameters.Select(p => (TypeRef)new GenericParameterRef(p.Name, false, p.Position) { Parameter = p }).ToArray());
                    current is not null; current = current.Definition.BaseType?.Substitute(current.Arguments, []) as DefinitionRef)
                    foreach (var method in current.Definition.Methods.Where(m => m.IsVirtual && m.Slot >= 0 && m.Slot < table.Length))
                        if (table[method.Slot] is null && method.IsAbstract)
                            table[method.Slot] = new MethodRef(method, current.Arguments, []);
                type.VTable = table;
            }
            return model;
        }

        /// <summary>
        /// 公钥在字符串区按 blob 存放：压缩长度 + 原始字节（中间可能有 0，不能按字符串读）。
        /// 用 SHA-1 末 8 字节倒序与元数据里的公钥标记核对。
        /// </summary>
        private byte[] PublicKey(Il2CppAssemblyNameDefinition name)
        {
            metadata.Position = (ulong)metadata.header.stringOffset + name.publicKeyIndex;
            var key = metadata.ReadBytes((int)metadata.ReadCompressedUInt32());
            var token = key.Length == 0 ? new byte[8] : System.Security.Cryptography.SHA1.HashData(key)[^8..].Reverse().ToArray();
            if (!token.SequenceEqual(name.public_key_token))
                throw new InvalidDataException($"{String(name.nameIndex)} 的公钥与公钥标记不符");
            return key;
        }

        // 元数据文件中的两项 int32 编码，与运行时含指针的接口偏移结构不同。
        private (TypeRef Interface, int Offset)[] InterfaceOffsets(Il2CppTypeDefinition def)
        {
            const int PairSize = 8;
            if ((long)(def.interfaceOffsetsStart + def.interface_offsets_count) * PairSize > metadata.header.interfaceOffsetsSize)
                throw new InvalidDataException($"接口偏移区间越界：{def.interfaceOffsetsStart}+{def.interface_offsets_count}");
            var pairs = new (TypeRef, int)[def.interface_offsets_count];
            metadata.Position = (ulong)metadata.header.interfaceOffsetsOffset + (ulong)def.interfaceOffsetsStart * PairSize;
            for (var k = 0; k < pairs.Length; k++)
            {
                var typeIndex = metadata.ReadInt32();
                var offset = metadata.ReadInt32();
                pairs[k] = (Convert(il2Cpp.types[typeIndex]), offset);
            }
            return pairs;
        }

        private int ObjectHeaderSize => checked((int)il2Cpp.Spec.Layout.ObjectHeaderSize);

        private IReadOnlyList<GenericParameterDef> GenericParameters(int containerIndex)
        {
            var container = metadata.genericContainers[containerIndex];
            return Enumerable.Range(container.genericParameterStart, container.type_argc).Select(GenericParameter).ToArray();
        }

        private GenericParameterDef GenericParameter(int index)
        {
            if (genericParameters.TryGetValue(index, out var cached)) return cached;
            var parameter = metadata.genericParameters[index];
            var result = new GenericParameterDef
            {
                Name = String(parameter.nameIndex),
                Position = parameter.num,
                Attributes = (GenericParameterAttributes)parameter.flags,
            };
            genericParameters[index] = result;
            result.Constraints = Enumerable.Range(parameter.constraintsStart, parameter.constraintsCount)
                .Select(c => Convert(il2Cpp.types[metadata.constraintIndices[c]])).ToArray();
            return result;
        }

        /// <summary>
        /// v29+ 的自定义特性数据：每个 image 的 attributeDataRanges 按令牌给出数据区间，
        /// 区间内是 构造函数索引表 + 逐个特性的 (实参, 字段, 属性) 编码值。
        /// </summary>
        private void ReadCustomAttributes(AssemblyDef[] assemblies, MethodDef[] methods, FieldDef[] fields, PropertyDef[] properties)
        {
            if (metadata.Version < 29) throw new NotSupportedException($"元数据版本 {metadata.Version} 的特性由生成函数构造，尚未支持");
            var byToken = new Dictionary<uint, Action<IReadOnlyList<CustomAttributeDef>>>();
            for (var a = 0; a < assemblies.Length; a++)
            {
                var imageDef = metadata.imageDefs[a];
                byToken.Clear();
                var assembly = assemblies[a];
                var assemblyDef = metadata.assemblyDefs[imageDef.assemblyIndex];
                byToken[assemblyDef.token] = list => assembly.CustomAttributes = list;
                foreach (var type in assembly.Types)
                {
                    byToken[type.Token] = list => type.CustomAttributes = list;
                    foreach (var field in type.Fields) byToken[field.Token] = list => field.CustomAttributes = list;
                    foreach (var method in type.Methods)
                    {
                        byToken[method.Token] = list => method.CustomAttributes = list;
                        if (method.ReturnParameterToken != 0) byToken[method.ReturnParameterToken] = list => method.ReturnAttributes = list;
                        foreach (var parameter in method.Parameters) byToken[parameter.Token] = list => parameter.CustomAttributes = list;
                    }
                    foreach (var property in type.Properties) byToken[property.Token] = list => property.CustomAttributes = list;
                    foreach (var definition in type.Events) byToken[definition.Token] = list => definition.CustomAttributes = list;
                }
                for (var r = imageDef.customAttributeStart; r < imageDef.customAttributeStart + imageDef.customAttributeCount; r++)
                {
                    var range = metadata.attributeDataRanges[r];
                    var end = metadata.attributeDataRanges[r + 1].startOffset;
                    metadata.Position = metadata.header.attributeDataOffset + range.startOffset;
                    using var reader = new CustomAttributeDataReader(executor, metadata.ReadBytes((int)(end - range.startOffset)));
                    var list = new List<CustomAttributeDef>();
                    for (var k = 0; k < reader.Count; k++)
                    {
                        var visitor = reader.VisitCustomAttributeData();
                        var constructor = methods[visitor.CtorIndex];
                        list.Add(new CustomAttributeDef(
                            constructor,
                            visitor.Arguments.Select(x => AttributeValueOf(x.Value)).ToArray(),
                            visitor.Fields.Select(x => (fields[x.Index], AttributeValueOf(x.Value))).ToArray(),
                            visitor.Properties.Select(x => (properties[x.Index], AttributeValueOf(x.Value))).ToArray()));
                    }
                    if (!byToken.TryGetValue(range.token, out var assign))
                        throw new InvalidDataException($"{assembly.Name} 的特性令牌 0x{range.token:x8} 没有对应的元素");
                    assign(list);
                }
            }
        }

        /// <summary>
        /// HasFieldRVA 字段的数据与默认值同存于 fieldAndParameterDefaultValueData，按字段类型（值类型）的大小截取。
        /// </summary>
        private void ReadInitialValues(FieldDef[] fields)
        {
            foreach (var field in fields)
            {
                if ((field.Attributes & FieldAttributes.HasFieldRVA) == 0) continue;
                if (!metadata.GetFieldDefaultValueFromIndex(field.Index, out var value) || value.dataIndex == -1)
                    throw new InvalidDataException($"HasFieldRVA 字段 {field} 没有数据");
                if (field.Type is not DefinitionRef { Definition: { IsValueType: true, Size: > 0 } type })
                    throw new InvalidDataException($"HasFieldRVA 字段 {field} 的类型 {field.Type} 大小未知");
                metadata.Position = metadata.GetDefaultValueFromIndex(value.dataIndex);
                field.InitialValue = metadata.ReadBytes(type.Size);
            }
        }

        private readonly Dictionary<string, TypeDef> corlib = new();

        private TypeRef Corlib(string fullName)
        {
            if (corlib.Count == 0)
                foreach (var type in types.Where(t => t.Assembly == "mscorlib.dll" && t.DeclaringType is null)) corlib[type.FullName] = type;
            return new DefinitionRef(corlib[fullName], []);
        }

        private AttributeValue AttributeValueOf(BlobValue blob)
        {
            if (blob.EnumType is not null) return new AttributeValue(Convert(blob.EnumType), blob.Value);
            switch (blob.il2CppTypeEnum)
            {
                case Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY:
                    {
                        var elements = (blob.Value as BlobValue[])?.Select(AttributeValueOf).ToArray();
                        var elementType = elements is [var first, ..] && elements.All(e => e.Type == first.Type) ? first.Type : Corlib("System.Object");
                        return new AttributeValue(new ArrayRef(elementType, 1), elements);
                    }
                case Il2CppTypeEnum.IL2CPP_TYPE_IL2CPP_TYPE_INDEX:
                    return new AttributeValue(Corlib("System.Type"), blob.Value is Il2CppType t ? Convert(t) : null);
                default:
                    var name = Builtins.TryGetValue(blob.il2CppTypeEnum, out var builtin) ? builtin
                        : throw new NotSupportedException($"特性值类型 {blob.il2CppTypeEnum}");
                    return new AttributeValue(Corlib(name), blob.Value);
            }
        }


        private TypeDef Definition(Il2CppType type) =>
            Convert(type) is DefinitionRef d ? d.Definition : throw new InvalidDataException($"不是类型定义：{type.type}");

        private TypeRef[] Instantiation(ulong pointer) => Instantiation(il2Cpp.Read<Il2CppGenericInst>(pointer));

        private TypeRef[] Instantiation(Il2CppGenericInst inst) =>
            il2Cpp.Read<ulong>(inst.type_argv, inst.type_argc).Select(p => Convert(Runtime(p))).ToArray();

        private Il2CppType Runtime(ulong pointer) => il2Cpp.GetIl2CppType(pointer) ?? throw new InvalidDataException($"Il2CppType 指针无效：0x{pointer:x}");

        private TypeRef Convert(Il2CppType type, bool ignoreByRef = false)
        {
            if (!ignoreByRef && type.byref != 0) return new ByRefRef(Convert(type, ignoreByRef: true));
            if (converted.TryGetValue(type, out var cached)) return cached;
            TypeRef result = type.type switch
            {
                Il2CppTypeEnum.IL2CPP_TYPE_FNPTR => new PrimitiveRef("nint"),
                Il2CppTypeEnum.IL2CPP_TYPE_PTR => new PointerRef(Convert(Runtime(type.data.type))),
                Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY => new ArrayRef(Convert(Runtime(type.data.type)), 1),
                Il2CppTypeEnum.IL2CPP_TYPE_ARRAY => ConvertArray(type),
                Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST => ConvertGenericInstance(type),
                Il2CppTypeEnum.IL2CPP_TYPE_VAR or Il2CppTypeEnum.IL2CPP_TYPE_MVAR => ConvertGenericParameter(type),
                _ => new DefinitionRef(DefinitionOf(type), []),
            };
            converted[type] = result;
            return result;
        }

        private static readonly Dictionary<Il2CppTypeEnum, string> Builtins = new()
        {
            [Il2CppTypeEnum.IL2CPP_TYPE_VOID] = "System.Void",
            [Il2CppTypeEnum.IL2CPP_TYPE_BOOLEAN] = "System.Boolean",
            [Il2CppTypeEnum.IL2CPP_TYPE_CHAR] = "System.Char",
            [Il2CppTypeEnum.IL2CPP_TYPE_I1] = "System.SByte",
            [Il2CppTypeEnum.IL2CPP_TYPE_U1] = "System.Byte",
            [Il2CppTypeEnum.IL2CPP_TYPE_I2] = "System.Int16",
            [Il2CppTypeEnum.IL2CPP_TYPE_U2] = "System.UInt16",
            [Il2CppTypeEnum.IL2CPP_TYPE_I4] = "System.Int32",
            [Il2CppTypeEnum.IL2CPP_TYPE_U4] = "System.UInt32",
            [Il2CppTypeEnum.IL2CPP_TYPE_I8] = "System.Int64",
            [Il2CppTypeEnum.IL2CPP_TYPE_U8] = "System.UInt64",
            [Il2CppTypeEnum.IL2CPP_TYPE_R4] = "System.Single",
            [Il2CppTypeEnum.IL2CPP_TYPE_R8] = "System.Double",
            [Il2CppTypeEnum.IL2CPP_TYPE_STRING] = "System.String",
            [Il2CppTypeEnum.IL2CPP_TYPE_OBJECT] = "System.Object",
            [Il2CppTypeEnum.IL2CPP_TYPE_I] = "System.IntPtr",
            [Il2CppTypeEnum.IL2CPP_TYPE_U] = "System.UIntPtr",
            [Il2CppTypeEnum.IL2CPP_TYPE_TYPEDBYREF] = "System.TypedReference",
        };

        /// <summary>CLASS/VALUETYPE 与内建类型的 data 都是类型定义索引；内建类型额外核对名称。</summary>
        private TypeDef DefinitionOf(Il2CppType type)
        {
            var expected = Builtins.GetValueOrDefault(type.type);
            if (expected is null && type.type is not (Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE))
                throw new NotSupportedException($"Il2CppType {type.type}");
            var index = type.data.klassIndex;
            if (index < 0 || index >= types.Length) throw new InvalidDataException($"{type.type} 的类型定义索引越界：{index}");
            var definition = types[index];
            if (expected is not null && definition.FullName != expected)
                throw new InvalidDataException($"{type.type} 指向 {definition.FullName}，期望 {expected}");
            return definition;
        }

        private TypeRef ConvertArray(Il2CppType type)
        {
            var array = il2Cpp.Read<Il2CppArrayType>(type.data.array);
            return new ArrayRef(Convert(Runtime(array.etype)), array.rank) { IsVector = false };
        }

        private TypeRef ConvertGenericInstance(Il2CppType type)
        {
            var genericClass = il2Cpp.Read<Il2CppGenericClass>(type.data.generic_class);
            var definition = Definition(Runtime(genericClass.type));
            return new DefinitionRef(definition, Instantiation(genericClass.context.class_inst));
        }

        private TypeRef ConvertGenericParameter(Il2CppType type)
        {
            var parameter = executor.GetGenericParameteFromIl2CppType(type);
            var container = metadata.genericContainers[parameter.ownerIndex];
            return new GenericParameterRef(String(parameter.nameIndex), container.is_method != 0, parameter.num)
            { Parameter = GenericParameter(container.genericParameterStart + parameter.num) };
        }
    }
}
