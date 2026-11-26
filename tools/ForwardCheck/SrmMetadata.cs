using System.Collections.Immutable;
using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;
using MethodBody = Cpp2CS.Kernel.Forward.MethodBody;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>一个已打开的程序集。</summary>
internal sealed class Module : IDisposable
{
    public string Name { get; }
    public PEReader Pe { get; }
    public MetadataReader Md { get; }
    private Dictionary<(string Namespace, string Name), TypeDefinitionHandle>? topLevel;

    public Module(string path)
    {
        Name = Path.GetFileNameWithoutExtension(path);
        Pe = new PEReader(File.OpenRead(path));
        Md = Pe.GetMetadataReader();
    }

    public TypeDefinitionHandle? FindTopLevel(string @namespace, string name)
    {
        if (topLevel is null)
        {
            topLevel = [];
            foreach (var handle in Md.TypeDefinitions)
            {
                var definition = Md.GetTypeDefinition(handle);
                if (definition.GetDeclaringType().IsNil)
                    topLevel[(Md.GetString(definition.Namespace), Md.GetString(definition.Name))] = handle;
            }
        }
        return topLevel.TryGetValue((@namespace, name), out var found) ? found : null;
    }

    public void Dispose() => Pe.Dispose();
}

/// <summary>泛型实参：类型的与方法的。</summary>
internal sealed record GenericArguments(ImmutableArray<TypeShape?> Type, ImmutableArray<TypeShape?> Method)
{
    public static GenericArguments None { get; } = new([], []);
}

/// <summary>
/// 用 System.Reflection.Metadata 读托管程序集，给展开提供元数据。只在核对工具里使用；
/// 值类型的布局在这里按顺序布局与自然对齐推算，正式的布局来自元数据模型。
/// 实体的 Key 是定义的身份字符串的散列，与解析的次序无关。核心库里的基本类型、Object 与 String
/// 用签名里基本类型代码的同一个身份，经签名与经类型定义得到同一个 Key。
/// </summary>
internal sealed class SrmMetadata : IDisposable
{
    private readonly string directory;
    private readonly int pointerBits;
    private readonly Dictionary<string, Module?> modules = new(StringComparer.OrdinalIgnoreCase);
    private readonly Dictionary<(Module, TypeDefinitionHandle), (int Size, int Alignment, Dictionary<FieldDefinitionHandle, int> Offsets)> layouts = [];
    private readonly HashSet<(Module, TypeDefinitionHandle)> layingOut = [];

    public SrmMetadata(string directory, int pointerBits)
    {
        this.directory = directory;
        this.pointerBits = pointerBits;
    }

    public void Dispose()
    {
        foreach (var module in modules.Values) module?.Dispose();
    }

    public Module? Load(string assembly)
    {
        if (modules.TryGetValue(assembly, out var known)) return known;
        string path = Path.Combine(directory, assembly + ".dll");
        var module = File.Exists(path) ? new Module(path) : null;
        modules[assembly] = module;
        return module;
    }

    private static ExpansionException Unresolved(string what) => new("元数据解析不了", what);

    private static long Hash(string identity)
    {
        ulong h = 0xcbf29ce484222325UL;
        foreach (char c in identity) { h ^= c; h *= 0x100000001b3UL; }
        return unchecked((long)h);
    }

    private TypeShape Reference(string identity) => new(StackKind.Object, pointerBits, false, new(EntityKind.Type, Hash(identity)));

    // ---- 类型 ----

    private static string TypeName(Module module, TypeDefinitionHandle handle)
    {
        var definition = module.Md.GetTypeDefinition(handle);
        string name = module.Md.GetString(definition.Name);
        var outer = definition.GetDeclaringType();
        if (!outer.IsNil) return TypeName(module, outer) + "/" + name;
        string @namespace = module.Md.GetString(definition.Namespace);
        return @namespace.Length == 0 ? name : @namespace + "." + name;
    }

    // 签名里有专门编码的类型（ECMA-335 II.23.1.16 的 ELEMENT_TYPE_*）：它们在核心库里的定义与签名里的编码是同一个类型。
    private static readonly HashSet<string> builtIn =
    [
        "Boolean", "Char", "SByte", "Byte", "Int16", "UInt16", "Int32", "UInt32", "Int64", "UInt64",
        "Single", "Double", "IntPtr", "UIntPtr", "Object", "String",
    ];

    private readonly Dictionary<Module, bool> core = [];

    /// <summary>核心库：定义了没有基类的 System.Object 的程序集。</summary>
    private bool IsCore(Module module)
    {
        if (core.TryGetValue(module, out bool known)) return known;
        bool result = module.FindTopLevel("System", "Object") is { } handle && module.Md.GetTypeDefinition(handle).BaseType.IsNil;
        return core[module] = result;
    }

    private string TypeIdentity(Module module, TypeDefinitionHandle handle)
    {
        var definition = module.Md.GetTypeDefinition(handle);
        if (definition.GetDeclaringType().IsNil && module.Md.GetString(definition.Namespace) == "System"
            && builtIn.Contains(module.Md.GetString(definition.Name)) && IsCore(module))
            return "T:System." + module.Md.GetString(definition.Name);
        return $"T:{module.Name}:{TypeName(module, handle)}";
    }

    /// <summary>基类的全名，不解析到定义。</summary>
    private static string BaseName(Module module, TypeDefinition definition)
    {
        var parent = definition.BaseType;
        if (parent.IsNil) return "";
        if (parent.Kind == HandleKind.TypeReference)
        {
            var reference = module.Md.GetTypeReference((TypeReferenceHandle)parent);
            return module.Md.GetString(reference.Namespace) + "." + module.Md.GetString(reference.Name);
        }
        if (parent.Kind == HandleKind.TypeDefinition) return TypeName(module, (TypeDefinitionHandle)parent);
        return "";
    }

    public (Module Module, TypeDefinitionHandle Handle) Resolve(Module module, TypeReferenceHandle handle)
    {
        var reference = module.Md.GetTypeReference(handle);
        string @namespace = module.Md.GetString(reference.Namespace), name = module.Md.GetString(reference.Name);
        var scope = reference.ResolutionScope;
        if (scope.Kind == HandleKind.TypeReference)
        {
            var (outerModule, outer) = Resolve(module, (TypeReferenceHandle)scope);
            foreach (var nested in outerModule.Md.GetTypeDefinition(outer).GetNestedTypes())
                if (outerModule.Md.GetString(outerModule.Md.GetTypeDefinition(nested).Name) == name) return (outerModule, nested);
            throw Unresolved($"嵌套类型 {name}");
        }
        Module? target = scope.Kind switch
        {
            HandleKind.AssemblyReference => Load(module.Md.GetString(module.Md.GetAssemblyReference((AssemblyReferenceHandle)scope).Name)),
            HandleKind.ModuleDefinition => module,
            _ => null,
        };
        for (int hops = 0; target is not null && hops < 8; hops++)
        {
            if (target.FindTopLevel(@namespace, name) is { } found) return (target, found);
            // 类型转发。
            Module? next = null;
            foreach (var exportedHandle in target.Md.ExportedTypes)
            {
                var exported = target.Md.GetExportedType(exportedHandle);
                if (!exported.IsForwarder || exported.Implementation.Kind != HandleKind.AssemblyReference) continue;
                if (target.Md.GetString(exported.Name) != name || target.Md.GetString(exported.Namespace) != @namespace) continue;
                next = Load(target.Md.GetString(target.Md.GetAssemblyReference((AssemblyReferenceHandle)exported.Implementation).Name));
                break;
            }
            target = next;
        }
        throw Unresolved($"类型 {@namespace}.{name}");
    }

    public TypeShape ShapeOf(Module module, TypeDefinitionHandle handle)
    {
        var definition = module.Md.GetTypeDefinition(handle);
        string identity = TypeIdentity(module, handle), parent = BaseName(module, definition);
        var entity = new EntityRef(EntityKind.Type, Hash(identity));
        if ((definition.Attributes & TypeAttributes.Interface) != 0) return new(StackKind.Object, pointerBits, false, entity);
        if (parent == "System.Enum")
        {
            foreach (var fieldHandle in definition.GetFields())
            {
                var field = module.Md.GetFieldDefinition(fieldHandle);
                if ((field.Attributes & FieldAttributes.Static) != 0) continue;
                var underlying = field.DecodeSignature(new Provider(this, module), GenericArguments.None) ?? throw Unresolved($"枚举 {identity}");
                return underlying with { Entity = entity };
            }
            throw Unresolved($"枚举 {identity} 没有实例字段");
        }
        if (parent != "System.ValueType") return new(StackKind.Object, pointerBits, false, entity);
        // 核心库里的基本类型以定义的形式出现时，与签名里的基本类型代码同样处理。
        if (definition.GetDeclaringType().IsNil && module.Md.GetString(definition.Namespace) == "System"
            && Primitive(module.Md.GetString(definition.Name)) is { } primitive)
            return primitive with { Entity = entity };
        if (definition.GetGenericParameters().Count > 0) throw new ExpansionException("泛型值类型的布局不在核对工具的范围内", identity);
        return new(StackKind.Value, Layout(module, handle).Size, false, entity);
    }

    private TypeShape? Primitive(string name) => name switch
    {
        "Boolean" => new(StackKind.Int32, 8, false, default),
        "Char" => new(StackKind.Int32, 16, false, default),
        "SByte" => new(StackKind.Int32, 8, true, default),
        "Byte" => new(StackKind.Int32, 8, false, default),
        "Int16" => new(StackKind.Int32, 16, true, default),
        "UInt16" => new(StackKind.Int32, 16, false, default),
        "Int32" => new(StackKind.Int32, 32, true, default),
        "UInt32" => new(StackKind.Int32, 32, false, default),
        "Int64" => new(StackKind.Int64, 64, true, default),
        "UInt64" => new(StackKind.Int64, 64, false, default),
        "Single" => new(StackKind.Float32, 32, false, default),
        "Double" => new(StackKind.Float64, 64, false, default),
        "IntPtr" => new(StackKind.NativeInt, pointerBits, true, default),
        "UIntPtr" => new(StackKind.NativeInt, pointerBits, false, default),
        _ => null,
    };

    private (int Size, int Alignment, Dictionary<FieldDefinitionHandle, int> Offsets) Layout(Module module, TypeDefinitionHandle handle)
    {
        if (layouts.TryGetValue((module, handle), out var known)) return known;
        if (!layingOut.Add((module, handle))) throw Unresolved($"值类型 {TypeIdentity(module, handle)} 的布局递归");
        var definition = module.Md.GetTypeDefinition(handle);
        if ((definition.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout || definition.GetLayout().PackingSize != 0)
            throw new ExpansionException("显式布局的值类型不在核对工具的范围内", TypeIdentity(module, handle));
        var offsets = new Dictionary<FieldDefinitionHandle, int>();
        int at = 0, alignment = 8;
        foreach (var fieldHandle in definition.GetFields())
        {
            var field = module.Md.GetFieldDefinition(fieldHandle);
            if ((field.Attributes & FieldAttributes.Static) != 0) continue;
            var type = field.DecodeSignature(new Provider(this, module), GenericArguments.None) ?? throw Unresolved("字段的类型");
            int align = type.Kind == StackKind.Value ? AlignmentOf(type) : type.StorageBits;
            at = (at + align - 1) / align * align;
            offsets[fieldHandle] = at;
            at += type.StorageBits;
            alignment = Math.Max(alignment, align);
        }
        int size = Math.Max((at + alignment - 1) / alignment * alignment, Math.Max(definition.GetLayout().Size * 8, 8));
        layingOut.Remove((module, handle));
        return layouts[(module, handle)] = (size, alignment, offsets);
    }

    private readonly Dictionary<long, int> alignments = [];

    private int AlignmentOf(TypeShape value) => alignments.TryGetValue(value.Entity.Key, out int a) ? a : 64;

    private TypeShape ShapeOfValue(Module module, TypeDefinitionHandle handle)
    {
        var shape = ShapeOf(module, handle);
        if (shape.Kind == StackKind.Value) alignments[shape.Entity.Key] = Layout(module, handle).Alignment;
        return shape;
    }

    /// <summary>签名里的类型到形状。void 是空。</summary>
    private sealed class Provider(SrmMetadata owner, Module module) : ISignatureTypeProvider<TypeShape?, GenericArguments>
    {
        public TypeShape? GetPrimitiveType(PrimitiveTypeCode code) => code switch
        {
            PrimitiveTypeCode.Void => null,
            PrimitiveTypeCode.Object => owner.Reference("T:System.Object"),
            PrimitiveTypeCode.String => owner.Reference("T:System.String"),
            PrimitiveTypeCode.TypedReference => throw new ExpansionException("TypedReference 不在首批范围内", ""),
            _ => owner.Primitive(code.ToString()) is { } shape ? shape with { Entity = new(EntityKind.Type, Hash("T:System." + code)) }
                : throw Unresolved($"基本类型 {code}"),
        };

        public TypeShape? GetTypeFromDefinition(MetadataReader reader, TypeDefinitionHandle handle, byte rawTypeKind) => owner.ShapeOfValue(module, handle);

        public TypeShape? GetTypeFromReference(MetadataReader reader, TypeReferenceHandle handle, byte rawTypeKind)
        {
            var (target, definition) = owner.Resolve(module, handle);
            return owner.ShapeOfValue(target, definition);
        }

        public TypeShape? GetTypeFromSpecification(MetadataReader reader, GenericArguments context, TypeSpecificationHandle handle, byte rawTypeKind) =>
            reader.GetTypeSpecification(handle).DecodeSignature(this, context);

        private TypeShape Derived(TypeShape? element, string suffix) =>
            owner.Reference($"{element?.Entity.Key ?? 0:x}{suffix}");

        public TypeShape? GetSZArrayType(TypeShape? elementType) => Derived(elementType, "[]");
        public TypeShape? GetArrayType(TypeShape? elementType, ArrayShape shape) => Derived(elementType, $"[{shape.Rank}]");
        public TypeShape? GetByReferenceType(TypeShape? elementType) => Derived(elementType, "&") with { Kind = StackKind.ByRef };
        public TypeShape? GetPointerType(TypeShape? elementType) => Derived(elementType, "*") with { Kind = StackKind.NativeInt };
        public TypeShape? GetFunctionPointerType(MethodSignature<TypeShape?> signature) => owner.Reference("fnptr") with { Kind = StackKind.NativeInt };
        public TypeShape? GetModifiedType(TypeShape? modifier, TypeShape? unmodifiedType, bool isRequired) => unmodifiedType;
        public TypeShape? GetPinnedType(TypeShape? elementType) => elementType;

        public TypeShape? GetGenericInstantiation(TypeShape? genericType, ImmutableArray<TypeShape?> typeArguments)
        {
            if (genericType is not { Kind: StackKind.Object })
                throw new ExpansionException("泛型值类型的布局不在核对工具的范围内", "");
            return Derived(genericType, "<" + string.Join(",", typeArguments.Select(t => (t?.Entity.Key ?? 0).ToString("x"))) + ">");
        }

        public TypeShape? GetGenericMethodParameter(GenericArguments context, int index) =>
            index < context.Method.Length ? context.Method[index] : throw new ExpansionException("开放的泛型参数", $"方法的第 {index} 个");

        public TypeShape? GetGenericTypeParameter(GenericArguments context, int index) =>
            index < context.Type.Length ? context.Type[index] : throw new ExpansionException("开放的泛型参数", $"类型的第 {index} 个");
    }

    // ---- 方法与字段 ----

    private MethodShape MethodOf(Module module, MethodDefinitionHandle handle, GenericArguments arguments, string suffix)
    {
        var definition = module.Md.GetMethodDefinition(handle);
        var owner = definition.GetDeclaringType();
        var ownerDefinition = module.Md.GetTypeDefinition(owner);
        var signature = definition.DecodeSignature(new Provider(this, module), arguments);
        return Shape(module, owner, ownerDefinition, definition.Attributes, module.Md.GetString(definition.Name), signature,
            Convert.ToHexString(module.Md.GetBlobBytes(definition.Signature)) + suffix);
    }

    private MethodShape Shape(Module module, TypeDefinitionHandle owner, TypeDefinition ownerDefinition, MethodAttributes attributes,
        string name, MethodSignature<TypeShape?> signature, string signatureText)
    {
        var parameters = ImmutableArray.CreateBuilder<TypeShape>();
        bool instance = signature.Header.IsInstance;
        string parent = BaseName(module, ownerDefinition);
        bool isValue = parent is "System.ValueType" or "System.Enum";
        bool isInterface = (ownerDefinition.Attributes & TypeAttributes.Interface) != 0;
        if (instance)
        {
            var self = ShapeOf(module, owner);
            parameters.Add(isValue ? new TypeShape(StackKind.ByRef, pointerBits, false, self.Entity) : self);
        }
        foreach (var parameter in signature.ParameterTypes) parameters.Add(parameter ?? throw Unresolved("void 形参"));
        VariantCondition dispatch = !instance ? VariantCondition.StaticMethod
            : isInterface ? VariantCondition.InterfaceMethod
            : (attributes & MethodAttributes.Virtual) != 0 && (attributes & MethodAttributes.Final) == 0
                && (ownerDefinition.Attributes & TypeAttributes.Sealed) == 0 && !isValue ? VariantCondition.ClassVirtual
            : VariantCondition.UniqueTarget;
        var entity = new EntityRef(EntityKind.Method, Hash($"M:{TypeIdentity(module, owner)}::{name}:{signatureText}"));
        return new MethodShape(entity, instance, parameters.ToImmutable(), signature.ReturnType, dispatch);
    }

    /// <summary>成员引用的所属类型：定义所在的模块与句柄，以及类型的泛型实参。</summary>
    private (Module Module, TypeDefinitionHandle Handle, ImmutableArray<TypeShape?> Arguments, string Suffix) Parent(Module module, EntityHandle parent)
    {
        switch (parent.Kind)
        {
            case HandleKind.TypeDefinition: return (module, (TypeDefinitionHandle)parent, [], "");
            case HandleKind.TypeReference:
            {
                var (target, handle) = Resolve(module, (TypeReferenceHandle)parent);
                return (target, handle, [], "");
            }
            case HandleKind.TypeSpecification:
            {
                // 泛型实例：取出泛型定义与各实参。
                var blob = module.Md.GetBlobReader(module.Md.GetTypeSpecification((TypeSpecificationHandle)parent).Signature);
                if (blob.ReadSignatureTypeCode() != SignatureTypeCode.GenericTypeInstance) throw Unresolved("成员引用的所属类型不是泛型实例");
                blob.ReadCompressedInteger();
                var generic = blob.ReadTypeHandle();
                var (target, handle, _, _) = Parent(module, generic);
                int count = blob.ReadCompressedInteger();
                var decoder = new SignatureDecoder<TypeShape?, GenericArguments>(new Provider(this, module), module.Md, GenericArguments.None);
                var builder = ImmutableArray.CreateBuilder<TypeShape?>(count);
                for (int i = 0; i < count; i++) builder.Add(decoder.DecodeType(ref blob));
                var arguments = builder.MoveToImmutable();
                return (target, handle, arguments, "<" + string.Join(",", arguments.Select(t => (t?.Entity.Key ?? 0).ToString("x"))) + ">");
            }
            default:
                throw Unresolved($"成员引用的所属 {parent.Kind}");
        }
    }

    public MethodShape Method(Module module, int token) => Method(module, MetadataTokens.EntityHandle(token), [], "");

    private MethodShape Method(Module module, EntityHandle handle, ImmutableArray<TypeShape?> methodArguments, string suffix)
    {
        switch (handle.Kind)
        {
            case HandleKind.MethodDefinition:
                return MethodOf(module, (MethodDefinitionHandle)handle, new(ImmutableArray<TypeShape?>.Empty, methodArguments), suffix);
            case HandleKind.MethodSpecification:
            {
                var specification = module.Md.GetMethodSpecification((MethodSpecificationHandle)handle);
                var arguments = specification.DecodeSignature(new Provider(this, module), GenericArguments.None);
                string text = "<" + string.Join(",", arguments.Select(t => (t?.Entity.Key ?? 0).ToString("x"))) + ">";
                return Method(module, specification.Method, arguments, text);
            }
            case HandleKind.MemberReference:
            {
                var reference = module.Md.GetMemberReference((MemberReferenceHandle)handle);
                if (reference.GetKind() != MemberReferenceKind.Method) throw Unresolved("成员引用不是方法");
                var (target, owner, typeArguments, typeSuffix) = Parent(module, reference.Parent);
                string name = module.Md.GetString(reference.Name);
                var signature = reference.DecodeMethodSignature(new Provider(this, module), new GenericArguments(typeArguments, methodArguments));
                // 在定义里按名称与形参个数找到方法，取它的属性。
                var ownerDefinition = target.Md.GetTypeDefinition(owner);
                MethodAttributes? attributes = null;
                foreach (var candidateHandle in ownerDefinition.GetMethods())
                {
                    var candidate = target.Md.GetMethodDefinition(candidateHandle);
                    if (target.Md.GetString(candidate.Name) != name) continue;
                    var blob = target.Md.GetBlobReader(candidate.Signature);
                    var header = blob.ReadSignatureHeader();
                    if (header.IsGeneric) blob.ReadCompressedInteger();
                    if (blob.ReadCompressedInteger() != signature.ParameterTypes.Length || header.IsInstance != signature.Header.IsInstance) continue;
                    if (attributes is not null && attributes != candidate.Attributes) throw Unresolved($"方法 {name} 有属性不同的重载，按个数分不开");
                    attributes = candidate.Attributes;
                }
                if (attributes is null) throw Unresolved($"方法 {name}");
                return Shape(target, owner, ownerDefinition, attributes.Value, name, signature,
                    Convert.ToHexString(module.Md.GetBlobBytes(reference.Signature)) + typeSuffix + suffix);
            }
            default:
                throw Unresolved($"方法记号 {handle.Kind}");
        }
    }

    public FieldShape Field(Module module, int token)
    {
        var handle = MetadataTokens.EntityHandle(token);
        Module target = module;
        FieldDefinitionHandle fieldHandle;
        if (handle.Kind == HandleKind.FieldDefinition) fieldHandle = (FieldDefinitionHandle)handle;
        else if (handle.Kind == HandleKind.MemberReference)
        {
            var reference = module.Md.GetMemberReference((MemberReferenceHandle)handle);
            var (ownerModule, owner, typeArguments, _) = Parent(module, reference.Parent);
            if (typeArguments.Length > 0) throw new ExpansionException("泛型类型的字段不在核对工具的范围内", "");
            string name = module.Md.GetString(reference.Name);
            target = ownerModule;
            fieldHandle = default;
            foreach (var candidate in ownerModule.Md.GetTypeDefinition(owner).GetFields())
                if (ownerModule.Md.GetString(ownerModule.Md.GetFieldDefinition(candidate).Name) == name) fieldHandle = candidate;
            if (fieldHandle.IsNil) throw Unresolved($"字段 {name}");
        }
        else throw Unresolved($"字段记号 {handle.Kind}");

        var field = target.Md.GetFieldDefinition(fieldHandle);
        var declaring = field.GetDeclaringType();
        var declaringDefinition = target.Md.GetTypeDefinition(declaring);
        var type = field.DecodeSignature(new Provider(this, target), GenericArguments.None) ?? throw Unresolved("字段的类型");
        bool isStatic = (field.Attributes & FieldAttributes.Static) != 0;
        bool hasInitializer = false;
        foreach (var methodHandle in declaringDefinition.GetMethods())
            hasInitializer |= target.Md.GetString(target.Md.GetMethodDefinition(methodHandle).Name) == ".cctor";
        int offset = -1;
        if (!isStatic && BaseName(target, declaringDefinition) == "System.ValueType" && declaringDefinition.GetGenericParameters().Count == 0)
            offset = Layout(target, declaring).Offsets[fieldHandle];
        string identity = $"F:{TypeIdentity(target, declaring)}::{target.Md.GetString(field.Name)}";
        return new FieldShape(new(EntityKind.Field, Hash(identity)), new(EntityKind.Type, Hash(TypeIdentity(target, declaring))), type, isStatic,
            hasInitializer, (declaringDefinition.Attributes & TypeAttributes.BeforeFieldInit) == 0, offset);
    }

    public TypeShape Type(Module module, int token)
    {
        var handle = MetadataTokens.EntityHandle(token);
        var provider = new Provider(this, module);
        return handle.Kind switch
        {
            HandleKind.TypeDefinition => ShapeOfValue(module, (TypeDefinitionHandle)handle),
            HandleKind.TypeReference => provider.GetTypeFromReference(module.Md, (TypeReferenceHandle)handle, 0)!,
            HandleKind.TypeSpecification => provider.GetTypeFromSpecification(module.Md, GenericArguments.None, (TypeSpecificationHandle)handle, 0)
                ?? throw Unresolved("类型记号是 void"),
            _ => throw Unresolved($"类型记号 {handle.Kind}"),
        };
    }

    /// <summary>读出一个方法定义的方法体。</summary>
    public MethodBody Body(Module module, int token)
    {
        var handle = MetadataTokens.MethodDefinitionHandle(token & 0xFFFFFF);
        var definition = module.Md.GetMethodDefinition(handle);
        if (definition.RelativeVirtualAddress == 0) throw new ExpansionException("方法没有方法体", "");
        var block = module.Pe.GetMethodBody(definition.RelativeVirtualAddress);
        ImmutableArray<TypeShape> locals = [];
        if (!block.LocalSignature.IsNil)
        {
            var decoded = module.Md.GetStandaloneSignature(block.LocalSignature).DecodeLocalSignature(new Provider(this, module), GenericArguments.None);
            locals = [.. decoded.Select(local => local ?? throw Unresolved("void 局部变量"))];
        }
        var code = block.GetILContent();
        return new MethodBody(Method(module, token), locals, code, block.ExceptionRegions.Length, block.LocalVariablesInitialized);
    }

    /// <summary>某个模块上的元数据视图。</summary>
    public IMetadataView View(Module module) => new ModuleView(this, module);

    private sealed class ModuleView(SrmMetadata owner, Module module) : IMetadataView
    {
        public MethodShape Method(int token) => owner.Method(module, token);
        public FieldShape Field(int token) => owner.Field(module, token);
        public TypeShape Type(int token) => owner.Type(module, token);
    }
}
