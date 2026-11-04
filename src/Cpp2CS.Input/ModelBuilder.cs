#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Buffers.Binary;
using Cpp2CS.Image;
using Cpp2CS.Input.Portable;
using Cpp2CS.Model;
using Il2CppDumper;

namespace Il2CppDumper
{
    /// <summary>Dumper 源码引用 Resource1.Il2CppDummyDll；这里用嵌入资源替代其 resx 生成类。</summary>
    internal static class Resource1
    {
        internal static byte[] Il2CppDummyDll
        {
            get
            {
                using var source = typeof(Resource1).Assembly.GetManifestResourceStream("Il2CppDummyDll")
                    ?? throw new InvalidOperationException("缺少嵌入资源 Il2CppDummyDll");
                using var output = new MemoryStream();
                source.CopyTo(output);
                return output.ToArray();
            }
        }
    }
}

namespace Cpp2CS.Input
{
    /// <summary>
    /// 从磁盘上的二进制与 global-metadata.dat 建立 <see cref="ProgramModel"/>。
    /// Il2CppDumper 仅用作元数据与注册表的解析库；地址、指针读取以 <see cref="ImageDocument"/> 为准。
    /// </summary>
    public sealed class ModelBuilder
    {
        private readonly MetadataSource metadata;
        private readonly Il2Cpp il2Cpp;
        private readonly ImageDocument image;
        private readonly TypeDef[] types;
        private readonly Dictionary<Il2CppType, TypeRef> converted = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<int, GenericParameterDef> genericParameters = new();

        public Il2CppExecutor? Executor => metadata.Executor;

        /// <summary>定位到的 Il2CppCodeRegistration / Il2CppMetadataRegistration 虚拟地址（已含 Il2CppDumper 的版本修正）。</summary>
        public ulong CodeRegistration { get; private init; }
        public ulong MetadataRegistration { get; private init; }

        private ModelBuilder(MetadataSource metadata, Il2Cpp il2Cpp, ImageDocument image)
        {
            this.metadata = metadata;
            this.il2Cpp = il2Cpp;
            this.image = image;
            types = new TypeDef[metadata.typeDefs.Length];
        }

        public static (ProgramModel Model, ModelBuilder Builder) Load(string binaryPath, string metadataPath)
        {
            var image = ImageDocument.Load(binaryPath);
            var bytes = File.ReadAllBytes(binaryPath);
            Il2Cpp il2Cpp = image.Architecture switch
            {
                Cpp2CS.Model.Architecture.Arm64 => new Elf64(new MemoryStream(bytes)),
                Cpp2CS.Model.Architecture.X64 => new PE(new MemoryStream(bytes)),
                _ => throw new NotSupportedException(image.Architecture.ToString()),
            };
            var metadataBytes = File.ReadAllBytes(metadataPath);
            var metadataVersion = metadataBytes.Length >= 8 ? BinaryPrimitives.ReadInt32LittleEndian(metadataBytes.AsSpan(4)) : 0;
            var metadata = metadataVersion >= 38
                ? MetadataSource.FromPortable(PortableMetadata.Read(metadataBytes), il2Cpp)
                : MetadataSource.FromDumper(new Metadata(new MemoryStream(metadataBytes)), il2Cpp);
            il2Cpp.SetProperties(BinaryVersion(metadata), metadata.metadataUsagesCount);
            var (codeRegistration, metadataRegistration, runtime) = FindRegistration(il2Cpp, metadata, binaryPath);
            metadata.SetRuntime(runtime);
            if (runtime.IsDumped) throw new NotSupportedException("只支持磁盘映像，不支持内存转储");
            var builder = new ModelBuilder(metadata, runtime, image) { CodeRegistration = codeRegistration, MetadataRegistration = metadataRegistration };
            return (builder.Build(runtime.MapVATR<Il2CppMetadataRegistration>(metadataRegistration)), builder);
        }

        /// <summary>
        /// 定位 CodeRegistration/MetadataRegistration 并初始化 il2Cpp，返回 MetadataRegistration 地址。
        /// Il2CppDumper 的 PlusSearch 在大映像上需要几十秒；它把交给 Init 的两个地址打印到控制台（AutoPlusInit），
        /// 这里从输出取回，连同最终版本号按 文件名+大小+修改时间 缓存在工作目录的 .cpp2cs/registration，之后直接以缓存值调用 Init。
        /// 以最终版本号重放 Init 与原过程等价：Init 内只有从旧版本号出发的修正分支。
        /// </summary>
        private static (ulong Code, ulong Metadata, Il2Cpp Runtime) FindRegistration(Il2Cpp il2Cpp, MetadataSource metadata, string binaryPath)
        {
            Il2Cpp Fresh()
            {
                var stream = new MemoryStream(File.ReadAllBytes(binaryPath));
                var runtime = il2Cpp is Elf64 ? (Il2Cpp)new Elf64(stream) : new PE(stream);
                runtime.SetProperties(BinaryVersion(metadata), metadata.metadataUsagesCount);
                return runtime;
            }
            var invariant = System.Globalization.CultureInfo.InvariantCulture;
            var file = new FileInfo(binaryPath);
            var cache = Path.Combine(".cpp2cs", "registration", $"{file.Name}-{file.Length}-{file.LastWriteTimeUtc.Ticks}.txt");
            if (File.Exists(cache))
            {
                var parts = File.ReadAllText(cache).Split(' ');
                il2Cpp.Version = double.Parse(parts[0], invariant);
                var cachedMeta = System.Convert.ToUInt64(parts[2], 16);
                var cachedCode = System.Convert.ToUInt64(parts[1], 16);
                il2Cpp.Init(cachedCode, cachedMeta);
                return (cachedCode, cachedMeta, il2Cpp);
            }
            var console = Console.Out;
            var captured = new StringWriter();
            var found = false;
            Exception? failure = null;
            Console.SetOut(captured);
            try
            {
                found = il2Cpp.PlusSearch(metadata.methodDefs.Count(m => m.methodIndex >= 0), metadata.typeDefs.Length, metadata.imageDefs.Length);
            }
            catch (Exception exception) when (exception is OverflowException or InvalidDataException or ArgumentOutOfRangeException or IndexOutOfRangeException)
            {
                failure = exception;
            }
            finally
            {
                Console.SetOut(console);
            }
            var lines = captured.ToString().Split('\n');
            if (Environment.GetEnvironmentVariable("CPP2CS_DEBUG_REG") is not null)
                Console.Error.WriteLine(captured.ToString());
            ulong? Printed(string prefix)
            {
                var line = lines.LastOrDefault(l => l.StartsWith(prefix, StringComparison.Ordinal));
                return line is null ? null : System.Convert.ToUInt64(line[prefix.Length..].Trim(), 16);
            }
            var printedCode = Printed("CodeRegistration : ");
            var printedMeta = Printed("MetadataRegistration : ");
            if (!metadata.IsPortable)
            {
                if (!found || printedCode is null || printedMeta is null) throw new InvalidDataException("PlusSearch 无法定位 IL2CPP CodeRegistration/MetadataRegistration", failure);
                return Cache(printedCode.Value, printedMeta.Value, il2Cpp);
            }

            // v106 的 CodeRegistration 比 PlusSearch 的 v29 偏移多了两个指针；在打印出的地址附近核对
            // codeGenModules 数量，找到能完整初始化的那个地址。
            if (printedCode is { } start && printedMeta is { } meta)
            {
                foreach (var delta in new[] { 0L, -8, 8, -16, 16, -24, 24, -32, 32, -40, 40 })
                {
                    var candidate = (ulong)((long)start + delta);
                    var probe = Fresh();
                    if (Environment.GetEnvironmentVariable("CPP2CS_DEBUG_REG") is not null)
                        Console.Error.WriteLine($"candidate 0x{candidate:x}");
                    if (TryInit(probe, candidate, meta, metadata.imageDefs.Length)) return Cache(candidate, meta, probe);
                }
            }
            throw new InvalidDataException("v106 的 CodeRegistration 定位失败", failure);

            (ulong Code, ulong Metadata, Il2Cpp Runtime) Cache(ulong code, ulong meta, Il2Cpp runtime)
            {
                Directory.CreateDirectory(Path.GetDirectoryName(cache)!);
                File.WriteAllText(cache, $"{runtime.Version.ToString(invariant)} {code:x} {meta:x}");
                return (code, meta, runtime);
            }
        }

        private static bool TryInit(Il2Cpp il2Cpp, ulong code, ulong metaAddress, int imageCount)
        {
            try
            {
                il2Cpp.Init(code, metaAddress);
                return il2Cpp.codeGenModules is { Count: > 0 } modules && modules.Count <= imageCount
                    && il2Cpp.types is { Length: > 0 } && il2Cpp.methodSpecs is { Length: > 0 };
            }
            catch (Exception exception) when (exception is OverflowException or InvalidDataException or ArgumentOutOfRangeException or IndexOutOfRangeException)
            {
                if (Environment.GetEnvironmentVariable("CPP2CS_DEBUG_REG") is not null)
                    Console.Error.WriteLine($"  {exception.GetType().Name}: {exception.Message}\n{exception.StackTrace}");
                return false;
            }
        }

        /// <summary>Il2CppDumper 的版本门上限是 99；v106 的二进制结构与 31.1 相同，元数据仍按 106 读取。</summary>
        private static double BinaryVersion(MetadataSource metadata) =>
            metadata.IsPortable && metadata.Version >= 106 ? 31.1 : metadata.Version;

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
                    if (metadata.GetFieldDefaultValueFromIndex(f, out var defaultValue) && defaultValue.dataIndex != -1
                        && metadata.TryGetDefaultValue(defaultValue.typeIndex, defaultValue.dataIndex, out var value))
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
                        Address = il2Cpp.GetMethodPointer(type.Assembly, methodDef),
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
                                || metadata.TryGetDefaultValue(parameterDefault.typeIndex, parameterDefault.dataIndex, out defaultValue));
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
            var sizes = il2Cpp.MapVATR<ulong>(registration.typeDefinitionsSizes, registration.typeDefinitionsSizesCount);
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
                    var instanceSize = (int)il2Cpp.MapVATR<uint>(sizes[i]);
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
                Image = image,
                MetadataVersion = metadata.Version,
                Il2CppVersion = il2Cpp.Version,
                Assemblies = assemblies,
                Types = types,
                Methods = methods,
                Fields = fields,
                RuntimeTypes = runtimeTypes,
                MetadataUsageSlots = il2Cpp.metadataUsages ?? Array.Empty<ulong>(),
                MethodSpecs = methodSpecs,
                FieldRefs = fieldRefs,
                StringLiterals = literals,
                Code = CodeOwners(methods, methodSpecs),
            };
            RegisterMetadataUsages(model);

            for (var i = 0; i < types.Length; i++)
            {
                var def = metadata.typeDefs[i];
                types[i].VTable = Enumerable.Range(def.vtableStart, def.vtable_count).Select(k =>
                {
                    var encoded = metadata.vtableMethods[k];
                    // 编码种类 0 为空槽位（v27+ 空槽位写作 1）
                    if (Metadata.GetEncodedIndexType(encoded) == 0) return null;
                    var usage = model.DecodeToken(Metadata.GetEncodedIndexType(encoded), metadata.GetDecodedMethodIndex(encoded));
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

        /// <summary>Il2CppInterfaceOffsetPair { int32 interfaceTypeIndex; int32 offset; }，Il2CppDumper 未读取这张表。</summary>
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

        private (TypeRef Interface, int Offset)[] InterfaceOffsets(Il2CppTypeDefinition def)
        {
            var pairSize = metadata.InterfaceOffsetPairSize;
            if ((long)(def.interfaceOffsetsStart + def.interface_offsets_count) * pairSize > metadata.header.interfaceOffsetsSize)
                throw new InvalidDataException($"接口偏移区间越界：{def.interfaceOffsetsStart}+{def.interface_offsets_count}");
            var pairs = new (TypeRef, int)[def.interface_offsets_count];
            metadata.Position = (ulong)metadata.header.interfaceOffsetsOffset + (ulong)def.interfaceOffsetsStart * (ulong)pairSize;
            for (var k = 0; k < pairs.Length; k++)
            {
                var typeIndex = metadata.ReadTypeIndex();
                var offset = metadata.ReadInt32();
                pairs[k] = (Convert(il2Cpp.types[typeIndex]), offset);
            }
            return pairs;
        }

        private Dictionary<ulong, IReadOnlyList<CodeOwner>> CodeOwners(MethodDef[] methods, MethodRef[] methodSpecs)
        {
            var owners = new Dictionary<ulong, List<CodeOwner>>();
            void Add(ulong address, CodeOwner owner)
            {
                if (address == 0) return;
                if (!owners.TryGetValue(address, out var list)) owners.Add(address, list = []);
                list.Add(owner);
            }
            foreach (var method in methods) Add(method.Address, new CodeOwner(new MethodRef(method, [], []), false));
            var specIndex = new Dictionary<Il2CppMethodSpec, int>(ReferenceEqualityComparer.Instance);
            for (var i = 0; i < il2Cpp.methodSpecs.Length; i++) specIndex[il2Cpp.methodSpecs[i]] = i;
            foreach (var (spec, pointer) in il2Cpp.methodSpecGenericMethodPointers)
                Add(pointer, new CodeOwner(methodSpecs[specIndex[spec]], true));
            return owners.ToDictionary(p => p.Key, p => (IReadOnlyList<CodeOwner>)p.Value);
        }

        /// <summary>
        /// 元数据使用对给出每个槽的 (kind, decodedIndex)。旧版本的槽里存的是重定位后的对象指针，
        /// 不能从槽值反推目标；这里按槽序号把 Il2CppDumper 解出的使用对登记到模型，供读取槽时使用。
        /// </summary>
        private void RegisterMetadataUsages(ProgramModel model)
        {
            if (il2Cpp.metadataUsages is not { } slots) return;
            foreach (var (kind, entries) in metadata.metadataUsageDic)
            {
                if (kind == Il2CppMetadataUsage.kIl2CppMetadataUsageInvalid) continue;
                foreach (var (slotIndex, decodedIndex) in entries)
                {
                    if (slotIndex >= slots.Length) continue;
                    if (model.DecodeToken((uint)kind, decodedIndex) is { } usage)
                        model.RegisterUsage(slots[slotIndex], usage);
                }
            }
        }

        private int ObjectHeaderSize => image.Architecture is Cpp2CS.Model.Architecture.Arm64 or Cpp2CS.Model.Architecture.X64 ? 16 : throw new NotSupportedException(image.Architecture.ToString());

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
                if (metadata.Version < 29)
                {
                    // v24-v28 的属性只给出类型和构造器索引，不保存构造实参；只在类型只有一个无参构造器时恢复该属性，
                    // 其余属性保持缺失，避免写出与元数据不一致的构造签名。
                    for (var r = imageDef.customAttributeStart; r < imageDef.customAttributeStart + imageDef.customAttributeCount; r++)
                    {
                        var range = metadata.attributeTypeRanges[r];
                        var list = new List<CustomAttributeDef>();
                        for (var k = 0; k < range.count; k++)
                        {
                            var typeIndex = metadata.attributeTypes[range.start + k];
                            if (typeIndex < 0 || typeIndex >= il2Cpp.types.Length)
                                throw new InvalidDataException($"属性类型索引无效：{typeIndex}");
                            var attributeType = il2Cpp.types[typeIndex];
                            if (attributeType.type is not (Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE))
                                continue;
                            var definition = DefinitionOf(attributeType);
                            var constructors = definition.Methods.Where(m => m.Name == ".ctor").ToArray();
                            if (constructors.Length != 1 || constructors[0].Parameters.Count != 0) continue;
                            list.Add(new CustomAttributeDef(constructors[0], [], [], []));
                        }
                        if (list.Count == 0 || !byToken.TryGetValue(range.token, out var legacyAssign)) continue;
                        legacyAssign(list);
                    }
                    continue;
                }
                for (var r = imageDef.customAttributeStart; r < imageDef.customAttributeStart + imageDef.customAttributeCount; r++)
                {
                    var range = metadata.attributeDataRanges[r];
                    var end = metadata.attributeDataRanges[r + 1].startOffset;
                    metadata.Position = metadata.header.attributeDataOffset + range.startOffset;
                    var visitors = metadata.VisitCustomAttributes(metadata.ReadBytes((int)(end - range.startOffset)));
                    var list = new List<CustomAttributeDef>();
                    foreach (var visitor in visitors)
                    {
                        var constructor = methods[visitor.CtorIndex];
                        list.Add(new CustomAttributeDef(
                            constructor,
                            visitor.Arguments.Select(x => AttributeValueOf(x.Value)).ToArray(),
                            visitor.Fields.Select(x => (fields[x.Index], AttributeValueOf(x.Value))).ToArray(),
                            visitor.Properties.Select(x => (properties[x.Index], AttributeValueOf(x.Value))).ToArray()));
                    }
                    if (!byToken.TryGetValue(range.token, out var assign))
                    {
                        // v106 的 image 级特性以 image token 为键，模型里没有对应元素；其余未知令牌仍视为错误。
                        if (metadata.IsPortable && range.token <= metadata.imageDefs.Length) continue;
                        throw new InvalidDataException($"{assembly.Name} 的特性令牌 0x{range.token:x8} 没有对应的元素");
                    }
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

        private TypeRef[] Instantiation(ulong pointer) => Instantiation(il2Cpp.MapVATR<Il2CppGenericInst>(pointer));

        private TypeRef[] Instantiation(Il2CppGenericInst inst) =>
            il2Cpp.MapVATR<ulong>(inst.type_argv, inst.type_argc).Select(p => Convert(Runtime(p))).ToArray();

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
            var array = il2Cpp.MapVATR<Il2CppArrayType>(type.data.array);
            return new ArrayRef(Convert(Runtime(array.etype)), array.rank) { IsVector = false };
        }

        private TypeRef ConvertGenericInstance(Il2CppType type)
        {
            var genericClass = il2Cpp.MapVATR<Il2CppGenericClass>(type.data.generic_class);
            var definition = il2Cpp.Version >= 27
                ? Definition(Runtime(genericClass.type))
                : genericClass.typeDefinitionIndex is var index && index >= 0 && index < types.Length
                    ? types[index]
                    : throw new InvalidDataException($"泛型实例的类型定义索引无效：{genericClass.typeDefinitionIndex}");
            return new DefinitionRef(definition, Instantiation(genericClass.context.class_inst));
        }

        private TypeRef ConvertGenericParameter(Il2CppType type)
        {
            var parameter = metadata.GetGenericParameterFromType(type);
            var container = metadata.genericContainers[parameter.ownerIndex];
            return new GenericParameterRef(String(parameter.nameIndex), container.is_method != 0, parameter.num)
            { Parameter = GenericParameter(container.genericParameterStart + parameter.num) };
        }
    }
}
