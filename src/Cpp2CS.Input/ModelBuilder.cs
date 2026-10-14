#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using Cpp2CS.Images;
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
        private readonly Metadata metadata;
        private readonly Il2Cpp il2Cpp;
        private readonly Il2CppExecutor executor;
        private readonly ImageDocument image;
        private readonly TypeDef[] types;
        private readonly Dictionary<Il2CppType, TypeRef> converted = new(ReferenceEqualityComparer.Instance);

        public Il2CppExecutor Executor => executor;

        private ModelBuilder(Metadata metadata, Il2Cpp il2Cpp, ImageDocument image)
        {
            this.metadata = metadata;
            this.il2Cpp = il2Cpp;
            this.image = image;
            executor = new Il2CppExecutor(metadata, il2Cpp);
            types = new TypeDef[metadata.typeDefs.Length];
        }

        public static (ProgramModel Model, ModelBuilder Builder) Load(string binaryPath, string metadataPath)
        {
            var image = ImageDocument.Load(binaryPath);
            var metadata = new Metadata(new MemoryStream(File.ReadAllBytes(metadataPath)));
            var bytes = File.ReadAllBytes(binaryPath);
            Il2Cpp il2Cpp = image.Architecture switch
            {
                Architecture.Arm64 => new Elf64(new MemoryStream(bytes)),
                Architecture.X64 => new PE(new MemoryStream(bytes)),
                _ => throw new NotSupportedException(image.Architecture.ToString()),
            };
            il2Cpp.SetProperties(metadata.Version, metadata.metadataUsagesCount);
            if (!il2Cpp.PlusSearch(metadata.methodDefs.Count(m => m.methodIndex >= 0), metadata.typeDefs.Length, metadata.imageDefs.Length)
                && !il2Cpp.Search() && !il2Cpp.SymbolSearch())
                throw new InvalidDataException("无法定位 IL2CPP CodeRegistration/MetadataRegistration");
            if (il2Cpp.IsDumped) throw new NotSupportedException("只支持磁盘映像，不支持内存转储");
            var builder = new ModelBuilder(metadata, il2Cpp, image);
            return (builder.Build(), builder);
        }

        private string String(uint index) => metadata.GetStringFromIndex(index);

        private ProgramModel Build()
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
                if (def.genericContainerIndex >= 0) type.GenericParameters = ContainerNames(def.genericContainerIndex);
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
                    object? constant = null;
                    if (metadata.GetFieldDefaultValueFromIndex(f, out var defaultValue) && defaultValue.dataIndex != -1
                        && executor.TryGetDefaultValue(defaultValue.typeIndex, defaultValue.dataIndex, out var value))
                        constant = value;
                    var isStatic = (attributes & FieldAttributes.Static) != 0;
                    var offset = (attributes & FieldAttributes.Literal) != 0 ? -1
                        : il2Cpp.GetFieldOffsetFromIndex(i, f - def.fieldStart, f, false, isStatic);
                    var field = new FieldDef
                    {
                        Index = f,
                        Owner = type,
                        Name = String(fieldDef.nameIndex),
                        Type = Convert(fieldType, ignoreByRef: true),
                        Attributes = attributes,
                        Offset = offset,
                        Constant = constant,
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
                        Attributes = (MethodAttributes)methodDef.flags,
                        ImplAttributes = (MethodImplAttributes)methodDef.iflags,
                        Slot = methodDef.slot == ushort.MaxValue ? -1 : methodDef.slot,
                        ReturnType = Convert(il2Cpp.types[methodDef.returnType]),
                        Address = il2Cpp.GetMethodPointer(type.Assembly, methodDef),
                    };
                    if (methodDef.genericContainerIndex >= 0) method.GenericParameters = ContainerNames(methodDef.genericContainerIndex);
                    var parameters = new ParameterDef[methodDef.parameterCount];
                    for (var p = 0; p < parameters.Length; p++)
                    {
                        var parameterDef = metadata.parameterDefs[methodDef.parameterStart + p];
                        var parameterType = il2Cpp.types[parameterDef.typeIndex];
                        object? defaultValue = null;
                        var hasDefault = metadata.GetParameterDefaultValueFromIndex(methodDef.parameterStart + p, out var parameterDefault)
                            && parameterDefault.dataIndex != -1
                            && executor.TryGetDefaultValue(parameterDefault.typeIndex, parameterDefault.dataIndex, out defaultValue);
                        parameters[p] = new ParameterDef(String(parameterDef.nameIndex), Convert(parameterType), (ParameterAttributes)parameterType.attrs, defaultValue, hasDefault);
                    }
                    method.Parameters = parameters;
                    methods[m] = method;
                    typeMethods.Add(method);
                }
                type.Methods = typeMethods;
            }

            for (var i = 0; i < types.Length; i++)
            {
                var def = metadata.typeDefs[i];
                types[i].Properties = Enumerable.Range(def.propertyStart, def.property_count).Select(k =>
                {
                    var property = metadata.propertyDefs[k];
                    return new PropertyDef
                    {
                        Name = String(property.nameIndex),
                        Getter = property.get >= 0 ? methods[def.methodStart + property.get] : null,
                        Setter = property.set >= 0 ? methods[def.methodStart + property.set] : null,
                    };
                }).ToArray();
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

            var model = new ProgramModel
            {
                Image = image,
                MetadataVersion = metadata.Version,
                Types = types,
                Methods = methods,
                Fields = fields,
                RuntimeTypes = runtimeTypes,
                MethodSpecs = methodSpecs,
                FieldRefs = fieldRefs,
                StringLiterals = literals,
                Code = CodeOwners(methods, methodSpecs),
            };

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
            }
            return model;
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

        private IReadOnlyList<string> ContainerNames(int containerIndex)
        {
            var container = metadata.genericContainers[containerIndex];
            return Enumerable.Range(container.genericParameterStart, container.type_argc)
                .Select(k => String(metadata.genericParameters[k].nameIndex)).ToArray();
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
            return new ArrayRef(Convert(Runtime(array.etype)), array.rank);
        }

        private TypeRef ConvertGenericInstance(Il2CppType type)
        {
            var genericClass = il2Cpp.MapVATR<Il2CppGenericClass>(type.data.generic_class);
            var definition = Definition(Runtime(genericClass.type));
            return new DefinitionRef(definition, Instantiation(genericClass.context.class_inst));
        }

        private TypeRef ConvertGenericParameter(Il2CppType type)
        {
            var parameter = executor.GetGenericParameteFromIl2CppType(type);
            var container = metadata.genericContainers[parameter.ownerIndex];
            return new GenericParameterRef(String(parameter.nameIndex), container.is_method != 0, parameter.num);
        }
    }
}
