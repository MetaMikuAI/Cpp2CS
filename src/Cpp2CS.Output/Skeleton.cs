using Cpp2CS.Model;
using Mono.Cecil;
using Mono.Cecil.Cil;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using SR = System.Reflection;

namespace Cpp2CS.Output;

/// <summary>按名称解析内存中的程序集；Cecil 写出枚举类型的特性实参等场合需要解析定义。</summary>
internal sealed class MemoryResolver : IAssemblyResolver
{
    private readonly Dictionary<string, AssemblyDefinition> assemblies = new();

    public void Register(AssemblyDefinition assembly) => assemblies[assembly.Name.Name] = assembly;
    public AssemblyDefinition Resolve(AssemblyNameReference name) =>
        assemblies.TryGetValue(name.Name, out var assembly) ? assembly : throw new AssemblyResolutionException(name);
    public AssemblyDefinition Resolve(AssemblyNameReference name, ReaderParameters parameters) => Resolve(name);
    public void Dispose() { }
}

/// <summary>
/// 由程序模型构造的 Cecil 程序集骨架：类型、嵌套、泛型参数与约束、基类与接口、字段（含常量、显式偏移、RVA 数据）、
/// 方法签名、属性、事件、自定义特性、显式接口实现（.override）齐全。
/// 有方法体的方法先放占位体（引用类型的实例构造函数先调用一个可访问的基类构造函数，再 throw null），由恢复阶段替换。
/// </summary>
public sealed class Skeleton
{
    private readonly ProgramModel model;
    private readonly int headerSize;
    private readonly MemoryResolver resolver = new();
    private readonly AssemblyDefinition[] assemblies;
    private readonly Dictionary<string, AssemblyDefinition> byImage = new();
    private readonly TypeDefinition[] types;
    private readonly MethodDefinition[] methods;
    private readonly FieldDefinition[] fields;
    private readonly Dictionary<string, TypeDef> corlib = new();
    private readonly Dictionary<(ModuleDefinition, NativeImport), MethodDefinition> nativeImports = new();

    public IReadOnlyList<AssemblyDefinition> Assemblies => assemblies;
    public TypeDefinition Type(TypeDef type) => types[type.Index];
    public MethodDefinition Method(MethodDef method) => methods[method.Index];
    public FieldDefinition Field(FieldDef field) => fields[field.Index];
    public AssemblyDefinition Assembly(string imageName) => byImage[imageName];

    public Skeleton(ProgramModel model)
    {
        this.model = model;
        headerSize = model.Image.Architecture is Architecture.Arm64 or Architecture.X64 ? 16 : throw new NotSupportedException(model.Image.Architecture.ToString());
        types = new TypeDefinition[model.Types.Count];
        methods = new MethodDefinition[model.Methods.Count];
        fields = new FieldDefinition[model.Fields.Count];
        foreach (var type in model.Types.Where(t => t.Assembly == "mscorlib.dll" && t.DeclaringType is null)) corlib[type.FullName] = type;

        assemblies = model.Assemblies.Select(CreateAssembly).ToArray();
        MarkPrimitives();
        foreach (var type in model.Types)
            foreach (var nested in type.NestedTypes) types[type.Index].NestedTypes.Add(types[nested.Index]);
        foreach (var type in model.Types)
            foreach (var parameter in type.GenericParameters) types[type.Index].GenericParameters.Add(CreateGenericParameter(parameter, types[type.Index]));
        foreach (var type in model.Types) DefineHierarchy(type);
        foreach (var type in model.Types) DefineMembers(type);
        foreach (var type in model.Types) DefineOverrides(type);
        for (var a = 0; a < model.Assemblies.Count; a++) DefineAttributes(model.Assemblies[a], assemblies[a]);
        foreach (var method in model.Methods)
            if (methods[method.Index].HasBody) SetStubBody(method);
    }

    /// <summary>把所有程序集写到 directory（文件名为映像名）。</summary>
    public void Write(string directory)
    {
        Directory.CreateDirectory(directory);
        foreach (var assembly in assemblies)
        {
            var path = Path.Combine(directory, assembly.MainModule.Name);
            assembly.Write(path);
            using var pe = new PEReader(File.OpenRead(path));
            var metadata = System.Reflection.Metadata.PEReaderExtensions.GetMetadataReader(pe);
            if (metadata.GetHeapSize(HeapIndex.UserString) > 0x1000000)
                throw new InvalidDataException($"{path} 的 #US 字符串堆超过 24 位令牌范围");
        }
    }

    private AssemblyDefinition CreateAssembly(AssemblyDef definition)
    {
        var name = new AssemblyNameDefinition(definition.AssemblyName, definition.Version)
        {
            Culture = definition.Culture,
            PublicKey = definition.PublicKey,
        };
        var assembly = AssemblyDefinition.CreateAssembly(name, definition.Name, new ModuleParameters
        {
            Kind = ModuleKind.Dll,
            AssemblyResolver = resolver,
            Runtime = TargetRuntime.Net_4_0,
        });
        resolver.Register(assembly);
        byImage[definition.Name] = assembly;
        var module = assembly.MainModule;
        module.Types.Clear();
        foreach (var type in definition.Types)
        {
            // 没有声明安全性数据，去掉 HasSecurity
            var attributes = (TypeAttributes)type.Attributes & ~TypeAttributes.HasSecurity;
            var created = new TypeDefinition(type.DeclaringType is null ? type.Namespace : "", type.Name, attributes);
            types[type.Index] = created;
            if (type.DeclaringType is null) module.Types.Add(created);
        }
        return assembly;
    }

    /// <summary>
    /// Cecil 按 TypeReference.etype 写签名与特性实参中的基元类型。从磁盘读入的核心库由 Cecil 的 TypeSystem 标记，
    /// 内存中新建的 mscorlib 没有这一步，这里按 ECMA-335 II.23.1.16 的元素类型码直接标记（etype 是 Cecil 的内部字段）。
    /// </summary>
    private void MarkPrimitives()
    {
        var etype = typeof(TypeReference).GetField("etype", SR.BindingFlags.NonPublic | SR.BindingFlags.Instance)
            ?? throw new MissingFieldException(nameof(TypeReference), "etype");
        (string Name, byte Code)[] primitives =
        [
            ("System.Void", 0x01), ("System.Boolean", 0x02), ("System.Char", 0x03), ("System.SByte", 0x04), ("System.Byte", 0x05),
            ("System.Int16", 0x06), ("System.UInt16", 0x07), ("System.Int32", 0x08), ("System.UInt32", 0x09), ("System.Int64", 0x0a),
            ("System.UInt64", 0x0b), ("System.Single", 0x0c), ("System.Double", 0x0d), ("System.String", 0x0e),
            ("System.TypedReference", 0x16), ("System.IntPtr", 0x18), ("System.UIntPtr", 0x19), ("System.Object", 0x1c),
        ];
        foreach (var (name, code) in primitives) etype.SetValue(types[Corlib(name).Index], Enum.ToObject(etype.FieldType, code));
    }

    private GenericParameter CreateGenericParameter(GenericParameterDef parameter, IGenericParameterProvider owner) =>
        new(parameter.Name, owner) { Attributes = (GenericParameterAttributes)parameter.Attributes };

    private void AddConstraints(IReadOnlyList<GenericParameterDef> parameters, IList<GenericParameter> created, ModuleDefinition module, TypeDefinition type, MethodDefinition? method)
    {
        for (var i = 0; i < parameters.Count; i++)
            foreach (var constraint in parameters[i].Constraints)
                created[i].Constraints.Add(new GenericParameterConstraint(Reference(module, constraint, type, method)));
    }

    private void DefineHierarchy(TypeDef type)
    {
        var created = types[type.Index];
        var module = created.Module;
        if (type.BaseType is not null) created.BaseType = Reference(module, type.BaseType, created, null);
        foreach (var @interface in type.Interfaces) created.Interfaces.Add(new InterfaceImplementation(Reference(module, @interface, created, null)));
        AddConstraints(type.GenericParameters, created.GenericParameters, module, created, null);
        // 无实例字段的值类型（<PrivateImplementationDetails> 的 __StaticArrayInitTypeSize=N 等）靠 .size 表达大小
        if (type.IsValueType && !type.IsEnum && type.Size > 1 && type.Fields.All(f => f.IsStatic))
        {
            created.PackingSize = 0;
            created.ClassSize = type.Size;
        }
    }

    private void DefineMembers(TypeDef type)
    {
        var created = types[type.Index];
        var module = created.Module;
        var explicitLayout = (type.Attributes & SR.TypeAttributes.ExplicitLayout) != 0;
        foreach (var field in type.Fields)
        {
            // 没有封送数据，去掉 HasFieldMarshal
            var attributes = (FieldAttributes)field.Attributes & ~FieldAttributes.HasFieldMarshal;
            var definition = new FieldDefinition(field.Name, attributes, Reference(module, field.Type, created, null));
            if (definition.IsLiteral) definition.Constant = field.Constant;
            if (field.InitialValue is not null) definition.InitialValue = field.InitialValue;
            if (explicitLayout && !field.IsStatic && !definition.IsLiteral)
            {
                if (field.Offset < 0) throw new InvalidDataException($"显式布局类型的字段 {field} 偏移未知");
                definition.Offset = field.Offset - (type.IsValueType ? 0 : headerSize);
            }
            fields[field.Index] = definition;
            created.Fields.Add(definition);
        }
        foreach (var method in type.Methods)
        {
            var attributes = (MethodAttributes)method.Attributes & ~MethodAttributes.HasSecurity;
            // 不经 module.TypeSystem：它会给非核心库模块补一个按默认版本猜测的 mscorlib 引用
            var definition = new MethodDefinition(method.Name, attributes, Import(module, Corlib("System.Void")))
            {
                ImplAttributes = (MethodImplAttributes)method.ImplAttributes,
            };
            created.Methods.Add(definition);
            methods[method.Index] = definition;
            foreach (var parameter in method.GenericParameters) definition.GenericParameters.Add(CreateGenericParameter(parameter, definition));
            AddConstraints(method.GenericParameters, definition.GenericParameters, module, created, definition);
            definition.ReturnType = Reference(module, method.ReturnType, created, definition);
            foreach (var parameter in method.Parameters)
            {
                var parameterAttributes = (ParameterAttributes)parameter.Attributes & ~ParameterAttributes.HasFieldMarshal;
                if (!parameter.HasDefault) parameterAttributes &= ~ParameterAttributes.HasDefault;
                var defined = new ParameterDefinition(parameter.Name, parameterAttributes, Reference(module, parameter.Type, created, definition));
                if (parameter.HasDefault) defined.Constant = parameter.DefaultValue;
                definition.Parameters.Add(defined);
            }
            // 元数据不含 DllImport 的库名与入口；占位的库名在方法体恢复（il2cpp_codegen_resolve_pinvoke 的实参）后替换（待验证）
            if (definition.IsPInvokeImpl)
                definition.PInvokeInfo = new PInvokeInfo(PInvokeAttributes.CallConvWinapi, method.Name, PInvokeModule(module));
        }
        foreach (var property in type.Properties)
        {
            var accessor = property.Getter ?? property.Setter ?? throw new InvalidDataException($"属性 {type}.{property} 没有访问器");
            var definition = new PropertyDefinition(property.Name, (PropertyAttributes)property.Attributes, Reference(module, PropertyType(property), created, null))
            {
                GetMethod = property.Getter is null ? null : methods[property.Getter.Index],
                SetMethod = property.Setter is null ? null : methods[property.Setter.Index],
                HasThis = !accessor.IsStatic,
            };
            if (property.Getter is null && property.Setter is { } setter && setter.CustomAttributes.Any(IsCompilerGenerated))
                definition.GetMethod = SynthesizeGetter(property, setter, created, definition.PropertyType);
            var indexParameters = property.Getter?.Parameters ?? property.Setter!.Parameters.Take(property.Setter.Parameters.Count - 1).ToArray();
            foreach (var parameter in indexParameters) definition.Parameters.Add(new ParameterDefinition(parameter.Name, ParameterAttributes.None, Reference(module, parameter.Type, created, null)));
            created.Properties.Add(definition);
        }
        foreach (var @event in type.Events)
        {
            created.Events.Add(new EventDefinition(@event.Name, (EventAttributes)@event.Attributes, Reference(module, @event.Type, created, null))
            {
                AddMethod = @event.Add is null ? null : methods[@event.Add.Index],
                RemoveMethod = @event.Remove is null ? null : methods[@event.Remove.Index],
                InvokeMethod = @event.Raise is null ? null : methods[@event.Raise.Index],
            });
        }
    }

    private static bool IsCompilerGenerated(CustomAttributeDef attribute) =>
        attribute.Constructor.Owner.FullName == "System.Runtime.CompilerServices.CompilerGeneratedAttribute";

    /// <summary>推断补出的 get 访问器及其依据的 set 访问器（特性在 DefineAttributes 阶段从 set 访问器复制）。</summary>
    private readonly List<(MethodDefinition Getter, MethodDef Setter)> synthesizedGetters = [];

    /// <summary>
    /// 自动属性的 get 访问器被裁剪（属性只剩带 [CompilerGenerated] 的 set）时补一个占位 get：
    /// C# 的自动属性必须有 get，set 上的 [CompilerGenerated] 说明这是自动属性。属于推断，不是元数据中的定义。
    /// 例如特性类的自动属性只在特性实参中被赋值，get 从未调用而被裁剪；缺 get 时 C# 不允许以命名实参赋值。
    /// </summary>
    private MethodDefinition SynthesizeGetter(PropertyDef property, MethodDef setter, TypeDefinition owner, TypeReference propertyType)
    {
        var setterDefinition = methods[setter.Index];
        if (setter.Parameters.Count != 1) throw new InvalidDataException($"自动属性 {property} 的 set 访问器参数个数为 {setter.Parameters.Count}");
        var getter = new MethodDefinition("get_" + property.Name, setterDefinition.Attributes, propertyType)
        {
            ImplAttributes = setterDefinition.ImplAttributes,
        };
        owner.Methods.Add(getter);
        if (getter.HasBody)
        {
            var il = getter.Body.GetILProcessor();
            il.Emit(OpCodes.Ldnull);
            il.Emit(OpCodes.Throw);
        }
        synthesizedGetters.Add((getter, setter));
        return getter;
    }

    private readonly Dictionary<ModuleDefinition, ModuleReference> pinvokeModules = new();

    private ModuleReference PInvokeModule(ModuleDefinition module)
    {
        if (!pinvokeModules.TryGetValue(module, out var reference))
        {
            reference = new ModuleReference("待验证");
            module.ModuleReferences.Add(reference);
            pinvokeModules[module] = reference;
        }
        return reference;
    }

    internal static TypeRef PropertyType(PropertyDef property) =>
        property.Getter?.ReturnType ?? property.Setter?.Parameters[^1].Type ?? throw new InvalidDataException($"属性 {property} 没有访问器");

    /// <summary>
    /// 显式接口实现：接口方法槽位（接口起始槽位 + 接口方法自身槽位）上是本类型声明的方法，
    /// 且名称与接口方法不同或不是 public（C# 的隐式实现必须是 public，如迭代器的 private MoveNext）时，加 .override。
    /// </summary>
    private void DefineOverrides(TypeDef type)
    {
        var created = types[type.Index];
        foreach (var (@interface, offset) in type.InterfaceOffsets)
        {
            if (@interface is not DefinitionRef { Definition: var definition } instance)
                throw new InvalidDataException($"{type} 的接口偏移项不是类型定义：{@interface}");
            foreach (var interfaceMethod in definition.Methods)
            {
                if (interfaceMethod.Slot < 0 || offset + interfaceMethod.Slot >= type.VTable.Count) continue;
                if (type.VTable[offset + interfaceMethod.Slot] is not { Method: var implementation }) continue;
                if (implementation.Owner != type) continue;
                var isPublic = (implementation.Attributes & SR.MethodAttributes.MemberAccessMask) == SR.MethodAttributes.Public;
                if (isPublic && implementation.Name == interfaceMethod.Name) continue;
                var target = methods[implementation.Index];
                var reference = Reference(created.Module, new MethodRef(interfaceMethod, instance.Arguments, []), created, target);
                if (!target.Overrides.Any(o => o.FullName == reference.FullName)) target.Overrides.Add(reference);
            }
        }
    }

    private void DefineAttributes(AssemblyDef assembly, AssemblyDefinition created)
    {
        var module = created.MainModule;
        AddAttributes(created.CustomAttributes, assembly.CustomAttributes, module);
        foreach (var type in assembly.Types)
        {
            AddAttributes(types[type.Index].CustomAttributes, type.CustomAttributes, module);
            foreach (var field in type.Fields) AddAttributes(fields[field.Index].CustomAttributes, field.CustomAttributes, module);
            foreach (var method in type.Methods)
            {
                var definition = methods[method.Index];
                AddAttributes(definition.CustomAttributes, method.CustomAttributes, module);
                AddAttributes(definition.MethodReturnType.CustomAttributes, method.ReturnAttributes, module);
                for (var i = 0; i < method.Parameters.Count; i++) AddAttributes(definition.Parameters[i].CustomAttributes, method.Parameters[i].CustomAttributes, module);
            }
            var properties = types[type.Index].Properties;
            for (var i = 0; i < type.Properties.Count; i++)
            {
                var property = type.Properties[i];
                AddAttributes(properties[i].CustomAttributes, property.CustomAttributes, module);
                // v31 之前元数据不保存返回值特性（补出的 get 也没有）。C# 编译器在属性和 get 的返回值上写同样的类型编码特性（元组元素名等），
                // 缺失时从属性复制；否则重写或实现带元组名的属性时 get 的签名对不上。属于推断。
                if (properties[i].GetMethod is { } getter && getter.MethodReturnType.CustomAttributes.Count == 0 && (model.MetadataVersion < 31 || property.Getter is null))
                    AddAttributes(getter.MethodReturnType.CustomAttributes, property.CustomAttributes.Where(IsTypeEncoding).ToArray(), module);
            }
            var events = types[type.Index].Events;
            for (var i = 0; i < type.Events.Count; i++) AddAttributes(events[i].CustomAttributes, type.Events[i].CustomAttributes, module);
        }
        foreach (var (getter, setter) in synthesizedGetters.Where(g => g.Getter.Module == module))
            AddAttributes(getter.CustomAttributes, setter.CustomAttributes.Where(IsCompilerGenerated).ToArray(), module);
    }

    /// <summary>补充类型信息的编码特性：元组元素名、dynamic、nint。</summary>
    private static bool IsTypeEncoding(CustomAttributeDef attribute) => attribute.Constructor.Owner.FullName is
        "System.Runtime.CompilerServices.TupleElementNamesAttribute" or "System.Runtime.CompilerServices.DynamicAttribute" or "System.Runtime.CompilerServices.NativeIntegerAttribute";

    private void AddAttributes(IList<CustomAttribute> target, IReadOnlyList<CustomAttributeDef> attributes, ModuleDefinition module)
    {
        foreach (var attribute in attributes)
        {
            var constructor = attribute.Constructor;
            if (constructor.Parameters.Count != attribute.Arguments.Count)
                throw new InvalidDataException($"特性 {constructor} 的实参个数 {attribute.Arguments.Count} 与形参 {constructor.Parameters.Count} 不符");
            var created = new CustomAttribute(Reference(module, new MethodRef(constructor, [], []), null, null));
            for (var i = 0; i < attribute.Arguments.Count; i++)
                created.ConstructorArguments.Add(Argument(module, constructor.Parameters[i].Type, attribute.Arguments[i]));
            foreach (var (field, value) in attribute.Fields)
                created.Fields.Add(new CustomAttributeNamedArgument(field.Name, Argument(module, field.Type, value)));
            foreach (var (property, value) in attribute.Properties)
                created.Properties.Add(new CustomAttributeNamedArgument(property.Name, Argument(module, PropertyType(property), value)));
            target.Add(created);
        }
    }

    /// <summary>按声明类型构造特性实参：object 形参装箱编码值；数组按元素声明类型逐个构造；typeof 的值为类型引用。</summary>
    private CustomAttributeArgument Argument(ModuleDefinition module, TypeRef declared, AttributeValue value)
    {
        var reference = Reference(module, declared, null, null);
        if (IsCorlib(declared, "System.Object")) return new CustomAttributeArgument(reference, Argument(module, value.Type, value));
        if (declared is ArrayRef { Element: var element })
            return new CustomAttributeArgument(reference, value.Value is AttributeValue[] items ? items.Select(i => Argument(module, element, i)).ToArray() : null);
        if (IsCorlib(declared, "System.Type")) return new CustomAttributeArgument(reference, value.Value is TypeRef type ? Reference(module, type, null, null) : null);
        return new CustomAttributeArgument(reference, value.Value);
    }

    private static bool IsCorlib(TypeRef type, string fullName) =>
        type is DefinitionRef { Definition: { Assembly: "mscorlib.dll", DeclaringType: null } definition, Arguments.Count: 0 } && definition.FullName == fullName;

    private TypeDef Corlib(string fullName) => corlib[fullName];

    // —— 引用构造 ——

    private readonly Dictionary<(ModuleDefinition, int), TypeReference> imported = new();

    private TypeReference Import(ModuleDefinition module, TypeDef type)
    {
        if (!imported.TryGetValue((module, type.Index), out var reference))
            imported[(module, type.Index)] = reference = module.ImportReference(types[type.Index]);
        return reference;
    }

    /// <summary>模型类型引用到 module 中的 Cecil 引用；泛型参数取自 type（类参数）与 method（方法参数）。</summary>
    public TypeReference Reference(ModuleDefinition module, TypeRef type, IGenericParameterProvider? typeContext, IGenericParameterProvider? methodContext) => type switch
    {
        PrimitiveRef { Name: "nint" } => Import(module, Corlib("System.IntPtr")),
        PrimitiveRef { Name: "void" } => Import(module, Corlib("System.Void")),
        DefinitionRef { Arguments.Count: 0 } d => Import(module, d.Definition),
        DefinitionRef d => Instance(Import(module, d.Definition), d.Arguments.Select(a => Reference(module, a, typeContext, methodContext))),
        ArrayRef a => ArrayReference(a, Reference(module, a.Element, typeContext, methodContext)),
        PointerRef p => new PointerType(Reference(module, p.Element, typeContext, methodContext)),
        ByRefRef r => new ByReferenceType(Reference(module, r.Element, typeContext, methodContext)),
        GenericParameterRef g => GenericParameter(g, g.IsMethod ? methodContext : typeContext),
        _ => throw new NotSupportedException($"类型引用 {type}"),
    };

    internal static ArrayType ArrayReference(ArrayRef type, TypeReference element)
    {
        var result = new ArrayType(element, type.Rank);
        if (type.Rank == 1 && !type.IsVector) result.Dimensions[0] = new ArrayDimension(0, null);
        return result;
    }

    private static GenericInstanceType Instance(TypeReference element, IEnumerable<TypeReference> arguments)
    {
        var instance = new GenericInstanceType(element);
        foreach (var argument in arguments) instance.GenericArguments.Add(argument);
        return instance;
    }

    private static GenericParameter GenericParameter(GenericParameterRef parameter, IGenericParameterProvider? context)
    {
        if (context is null || parameter.Position >= context.GenericParameters.Count)
            throw new InvalidDataException($"泛型参数 {parameter.Name}（{(parameter.IsMethod ? "方法" : "类")} #{parameter.Position}）没有对应的上下文");
        return context.GenericParameters[parameter.Position];
    }

    /// <summary>方法引用：声明类型为泛型实例时以开放签名挂到实例上，有方法实参时再构造泛型方法实例。</summary>
    public MethodReference Reference(ModuleDefinition module, MethodRef method, IGenericParameterProvider? typeContext, IGenericParameterProvider? methodContext)
    {
        if (method.Method.NativeImport is { } imported) return NativeReference(module, method.Method, imported);
        var reference = module.ImportReference(methods[method.Method.Index]);
        if (method.TypeArguments.Count > 0)
        {
            var host = new MethodReference(reference.Name, reference.ReturnType, Reference(module, method.DeclaringType, typeContext, methodContext))
            {
                HasThis = reference.HasThis,
                ExplicitThis = reference.ExplicitThis,
                CallingConvention = reference.CallingConvention,
            };
            foreach (var parameter in reference.Parameters) host.Parameters.Add(new ParameterDefinition(parameter.ParameterType));
            foreach (var parameter in reference.GenericParameters) host.GenericParameters.Add(new GenericParameter(parameter.Name, host));
            reference = host;
        }
        if (method.MethodArguments.Count > 0)
        {
            var instance = new GenericInstanceMethod(reference);
            foreach (var argument in method.MethodArguments) instance.GenericArguments.Add(Reference(module, argument, typeContext, methodContext));
            reference = instance;
        }
        return reference;
    }

    private MethodDefinition NativeReference(ModuleDefinition module, MethodDef method, NativeImport imported)
    {
        if (nativeImports.TryGetValue((module, imported), out var cached)) return cached;
        if (model.Types.Any(t => t.Assembly == module.Name && t.Namespace == "Cpp2CS" && t.Name == "NativeImports"))
            throw new InvalidDataException("原类型与导入声明容器 Cpp2CS.NativeImports 重名");
        var container = module.Types.FirstOrDefault(t => t.Namespace == "Cpp2CS" && t.Name == "NativeImports");
        if (container is null)
        {
            container = new TypeDefinition("Cpp2CS", "NativeImports", TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed
                | TypeAttributes.BeforeFieldInit, Reference(module, new DefinitionRef(Corlib("System.Object"), []), null, null));
            module.Types.Add(container);
        }
        var library = module.ModuleReferences.FirstOrDefault(r => r.Name == imported.Library);
        if (library is null) module.ModuleReferences.Add(library = new ModuleReference(imported.Library));
        var declaration = new MethodDefinition(method.Name, MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.PInvokeImpl,
            Reference(module, method.ReturnType, null, null))
        {
            ImplAttributes = MethodImplAttributes.PreserveSig,
            PInvokeInfo = new(PInvokeAttributes.CallConvCdecl | PInvokeAttributes.NoMangle, imported.EntryPoint, library),
        };
        foreach (var parameter in method.Parameters)
            declaration.Parameters.Add(new ParameterDefinition(parameter.Name, 0, Reference(module, parameter.Type, null, null)));
        container.Methods.Add(declaration);
        nativeImports.Add((module, imported), declaration);
        return declaration;
    }

    public FieldReference Reference(ModuleDefinition module, FieldRef field, IGenericParameterProvider? typeContext, IGenericParameterProvider? methodContext)
    {
        var reference = module.ImportReference(fields[field.Field.Index]);
        return field.DeclaringType is DefinitionRef { Arguments.Count: > 0 }
            ? new FieldReference(reference.Name, reference.FieldType, Reference(module, field.DeclaringType, typeContext, methodContext))
            : reference;
    }

    // —— 占位方法体 ——

    private void SetStubBody(MethodDef method)
    {
        var definition = methods[method.Index];
        var body = definition.Body;
        var il = body.GetILProcessor();
        if (definition.IsConstructor && !definition.IsStatic && !method.Owner.IsValueType && method.Owner.BaseType is DefinitionRef baseType
            && BaseConstructor(method.Owner, baseType.Definition) is { } constructor)
        {
            il.Emit(OpCodes.Ldarg_0);
            foreach (var parameter in constructor.Parameters) EmitDefault(il, definition, parameter.Type.Substitute(baseType.Arguments, []));
            il.Emit(OpCodes.Call, Reference(definition.Module, new MethodRef(constructor, baseType.Arguments, []), definition.DeclaringType, definition));
        }
        il.Emit(OpCodes.Ldnull);
        il.Emit(OpCodes.Throw);
    }

    /// <summary>派生类可访问的基类实例构造函数，优先不含 ref 形参、形参最少者。</summary>
    private static MethodDef? BaseConstructor(TypeDef derived, TypeDef @base)
    {
        bool Encloses(TypeDef outer)
        {
            for (var t = derived.DeclaringType; t is not null; t = t.DeclaringType)
                if (t == outer) return true;
            return false;
        }
        bool Accessible(MethodDef m) => (m.Attributes & SR.MethodAttributes.MemberAccessMask) switch
        {
            SR.MethodAttributes.Public or SR.MethodAttributes.Family or SR.MethodAttributes.FamORAssem => true,
            SR.MethodAttributes.Assembly or SR.MethodAttributes.FamANDAssem => derived.Assembly == @base.Assembly,
            SR.MethodAttributes.Private => Encloses(@base),
            _ => false,
        };
        return @base.Methods
            .Where(m => m.Name == ".ctor" && !m.IsStatic && Accessible(m))
            .OrderBy(m => m.Parameters.Any(p => p.Type is ByRefRef or PointerRef) ? 1 : 0)
            .ThenBy(m => m.Parameters.Count)
            .FirstOrDefault();
    }

    private void EmitDefault(ILProcessor il, MethodDefinition method, TypeRef type)
    {
        var module = method.Module;
        if (type is PointerRef or PrimitiveRef { Name: "nint" })
        {
            il.Emit(OpCodes.Ldc_I4_0);
            il.Emit(OpCodes.Conv_U);
            return;
        }
        var element = type is ByRefRef byRef ? byRef.Element : type;
        var reference = Reference(module, element, method.DeclaringType, method);
        var local = new VariableDefinition(reference);
        method.Body.Variables.Add(local);
        il.Emit(OpCodes.Ldloca, local);
        il.Emit(OpCodes.Initobj, reference);
        il.Emit(type is ByRefRef ? OpCodes.Ldloca : OpCodes.Ldloc, local);
    }
}
