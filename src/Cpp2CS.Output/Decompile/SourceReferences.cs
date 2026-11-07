using Mono.Cecil;
using Mono.Cecil.Cil;
using Mono.Cecil.Rocks;

namespace Cpp2CS.Output;

/// <summary>
/// 源码工程引用和反编译所用的程序集。恢复的方法体带着内联留下的访问：别的类型的私有成员、构造函数之外写只读字段、
/// 只有 get 的自动属性的后备字段。这些 CIL 能表达，C# 不能。这里在副本上按方法体的实际用法放宽主程序集的声明，方法体不变；
/// 外部程序集只补被裁掉、但真实库里存在的成员，访问外部私有成员的写法由反编译阶段折回公开写法。
/// assemblies/ 保持原样，供底层检查和执行对照。
/// </summary>
public static class SourceReferences
{
    /// <summary>把 <paramref name="searchDirectory"/> 的程序集写到 <paramref name="target"/>，只改声明。</summary>
    public static void Prepare(string assemblyPath, string searchDirectory, string target)
    {
        Directory.CreateDirectory(target);
        using var resolver = new DirectoryResolver(searchDirectory);
        var main = resolver.Resolve(Path.GetFileNameWithoutExtension(assemblyPath)).MainModule;
        var changed = new HashSet<ModuleDefinition>();
        new Declarations(main, changed).Apply();
        AddStrippedBuilderMembers(resolver.Modules, changed);
        AddPlaceholderReference(main, changed);
        AddStrippedRuntimeMembers(resolver.Modules, changed);
        AddReadOnlyModifiers(resolver.Modules, changed);
        foreach (var file in Directory.GetFiles(searchDirectory, "*.dll"))
        {
            var destination = Path.Combine(target, Path.GetFileName(file));
            // 模块按绝对路径对应：搜索目录可以是相对路径，这时模块记下的也是相对路径。
            var module = resolver.Modules.FirstOrDefault(m => string.Equals(Path.GetFullPath(m.FileName), Path.GetFullPath(file), StringComparison.OrdinalIgnoreCase));
            if (module is not null && changed.Contains(module)) module.Assembly.Write(destination);
            else File.Copy(file, destination, true);
        }
    }

    /// <summary>
    /// C# 编译 async 方法时要求构建器同时有 AwaitOnCompleted 和 AwaitUnsafeOnCompleted。编译器生成的代码只调用后者，
    /// 前者常被 IL2CPP 裁掉。按后者的签名补一个占位声明，只为源码能绑定。
    /// </summary>
    private static void AddStrippedBuilderMembers(IReadOnlyList<ModuleDefinition> modules, HashSet<ModuleDefinition> changed)
    {
        foreach (var module in modules)
        {
            foreach (var type in module.GetTypes())
            {
                if (type.Methods.FirstOrDefault(m => m is { Name: "AwaitUnsafeOnCompleted", HasGenericParameters: true }) is not { } existing
                    || type.Methods.Any(m => m.Name == "AwaitOnCompleted")) continue;
                var method = new MethodDefinition("AwaitOnCompleted", existing.Attributes & ~(MethodAttributes.Virtual | MethodAttributes.NewSlot | MethodAttributes.Final), existing.ReturnType);
                foreach (var parameter in existing.GenericParameters) method.GenericParameters.Add(new GenericParameter(parameter.Name, method));
                foreach (var parameter in existing.Parameters)
                {
                    var element = ((ByReferenceType)parameter.ParameterType).ElementType;
                    method.Parameters.Add(new ParameterDefinition(parameter.Name, parameter.Attributes, new ByReferenceType(method.GenericParameters[((GenericParameter)element).Position])));
                }
                var il = method.Body.GetILProcessor();
                il.Emit(OpCodes.Ldnull);
                il.Emit(OpCodes.Throw);
                type.Methods.Add(method);
                changed.Add(module);
            }
        }
    }

    /// <summary>生成的源码要用到、但被裁掉的运行时成员：补占位声明，只为源码能绑定。</summary>
    private static void AddStrippedRuntimeMembers(IReadOnlyList<ModuleDefinition> modules, HashSet<ModuleDefinition> changed)
    {
        foreach (var module in modules)
        {
            if (module.GetType("System.Runtime.CompilerServices", "Unsafe") is { IsPublic: true } unsafeType && unsafeType.Methods.All(m => m.Name != "AsPointer"))
            {
                var method = new MethodDefinition("AsPointer", MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.HideBySig, module.TypeSystem.Void);
                var parameter = new GenericParameter("T", method);
                method.GenericParameters.Add(parameter);
                method.ReturnType = new PointerType(module.TypeSystem.Void);
                method.Parameters.Add(new ParameterDefinition("value", ParameterAttributes.None, new ByReferenceType(parameter)));
                Throwing(method);
                unsafeType.Methods.Add(method);
                changed.Add(module);
            }
            if (module.GetType("System", "RuntimeMethodHandle") is { } handle && handle.Methods.All(m => m.Name != "GetFunctionPointer"))
            {
                var method = new MethodDefinition("GetFunctionPointer", MethodAttributes.Public | MethodAttributes.HideBySig, module.TypeSystem.IntPtr);
                Throwing(method);
                handle.Methods.Add(method);
                changed.Add(module);
            }
        }
    }

    /// <summary>
    /// IL2CPP 的类型不带自定义修饰符。C# 读只读引用时要求返回只读引用的方法、虚方法（含接口方法和委托的 Invoke）的 in 形参
    /// 在类型上带 modreq(InAttribute)；只有 IsReadOnlyAttribute 时不认这个成员（CS0570），span 的 fixed 也写不出来。按特性补回修饰符。
    /// 方法体里对这些方法的引用仍不带修饰符；反编译器按擦除修饰符后的签名解析，不受影响。
    /// </summary>
    private static void AddReadOnlyModifiers(IReadOnlyList<ModuleDefinition> modules, HashSet<ModuleDefinition> changed)
    {
        if (modules.Select(m => m.GetType("System.Runtime.InteropServices", "InAttribute")).FirstOrDefault(t => t is not null) is not { } attribute) return;
        static bool ReadOnly(Mono.Collections.Generic.Collection<CustomAttribute> attributes) =>
            attributes.Any(a => a.AttributeType.FullName == "System.Runtime.CompilerServices.IsReadOnlyAttribute");
        foreach (var module in modules)
        {
            TypeReference? modifier = null;
            foreach (var method in module.GetTypes().SelectMany(t => t.Methods))
            {
                if (method.ReturnType is ByReferenceType && ReadOnly(method.MethodReturnType.CustomAttributes))
                    method.MethodReturnType.ReturnType = new RequiredModifierType(modifier ??= module.ImportReference(attribute), method.ReturnType);
                if (!method.IsVirtual) continue;
                foreach (var parameter in method.Parameters.Where(p => p.ParameterType is ByReferenceType && ReadOnly(p.CustomAttributes)))
                    parameter.ParameterType = new RequiredModifierType(modifier ??= module.ImportReference(attribute), parameter.ParameterType);
            }
            if (modifier is not null) changed.Add(module);
        }
    }

    private static void Throwing(MethodDefinition method)
    {
        var il = method.Body.GetILProcessor();
        il.Emit(OpCodes.Ldnull);
        il.Emit(OpCodes.Throw);
    }

    /// <summary>占位值的类型实参不能是按引用类型：按引用的占位写成 Unrecovered.Ref&lt;T&gt;。</summary>
    private static void AddPlaceholderReference(ModuleDefinition main, HashSet<ModuleDefinition> changed)
    {
        if (main.GetType("Cpp2CS", "Unrecovered") is not { } type || type.Methods.FirstOrDefault(m => m.Name == "Value") is not { } value) return;
        var method = new MethodDefinition("Ref", value.Attributes, main.TypeSystem.Void);
        var parameter = new GenericParameter("T", method);
        method.GenericParameters.Add(parameter);
        method.ReturnType = new ByReferenceType(parameter);
        method.Parameters.Add(new ParameterDefinition("address", ParameterAttributes.None, main.TypeSystem.UInt64));
        Throwing(method);
        type.Methods.Add(method);
        changed.Add(main);
    }

    private sealed class DirectoryResolver : IAssemblyResolver
    {
        private readonly Dictionary<string, AssemblyDefinition> assemblies = new(StringComparer.Ordinal);
        private readonly List<ModuleDefinition> modules = [];

        public DirectoryResolver(string directory)
        {
            foreach (var file in Directory.GetFiles(directory, "*.dll"))
            {
                var assembly = AssemblyDefinition.ReadAssembly(file, new ReaderParameters { AssemblyResolver = this, InMemory = true });
                assemblies[assembly.Name.Name] = assembly;
                modules.Add(assembly.MainModule);
            }
        }

        public IReadOnlyList<ModuleDefinition> Modules => modules;
        public AssemblyDefinition Resolve(string name) => assemblies[name];
        public AssemblyDefinition Resolve(AssemblyNameReference name) => assemblies.GetValueOrDefault(name.Name)!;
        public AssemblyDefinition Resolve(AssemblyNameReference name, ReaderParameters parameters) => Resolve(name);
        public void Dispose()
        {
            foreach (var module in modules) module.Dispose();
        }
    }

    /// <summary>按主程序集方法体的用法放宽它自己的声明，放宽到够用为止：写成 internal，虚方法族写成 public。</summary>
    private sealed class Declarations(ModuleDefinition main, HashSet<ModuleDefinition> changed)
    {
        private readonly HashSet<FieldDefinition> demoted = [];
        private readonly HashSet<MethodDefinition> widened = [];
        private readonly List<FieldReference> demotedReferences = [];
        private Dictionary<TypeDefinition, List<TypeDefinition>>? derived;

        public void Apply()
        {
            // 先定自动属性：退回普通属性后，后备字段按普通字段检查。
            foreach (var (method, instruction) in Instructions())
                if (instruction.Operand is FieldReference reference && reference.Resolve() is { } field && field.Module == main && Property(field) is { } property && RequiresField(field, property, method, instruction))
                    demoted.Add(field);
            foreach (var type in main.GetTypes())
            {
                if (type.BaseType is { } baseType) Reference(baseType, type);
                foreach (var implementation in type.Interfaces) Reference(implementation.InterfaceType, type);
                foreach (var field in type.Fields) Reference(field.FieldType, type);
                foreach (var method in type.Methods)
                {
                    Reference(method.ReturnType, type);
                    foreach (var parameter in method.Parameters) Reference(parameter.ParameterType, type);
                    // 编译器生成的方法（局部函数是 internal）签名里可以有更难访问的类型；反编译器折不回去时按普通成员写出，要满足 C# 的一致性。
                    if (method.Name.StartsWith('<') && !method.IsPrivate)
                        foreach (var signature in method.Parameters.Select(p => p.ParameterType).Prepend(method.ReturnType)) Raise(signature, method.IsPublic);
                    if (!method.HasBody) continue;
                    foreach (var variable in method.Body.Variables) Reference(variable.VariableType, type);
                    foreach (var instruction in method.Body.Instructions) Use(instruction, method);
                }
            }
            foreach (var field in demoted) Demote(field);
            // 编译器生成的数据字段的类型是私有的嵌套结构体；只在元数据里合法。
            if (main.GetType("<PrivateImplementationDetails>") is { } details)
                foreach (var field in details.Fields) Raise(field.FieldType, false);
            foreach (var reference in demotedReferences)
                if (reference is not FieldDefinition) reference.Name = PlainName(reference.Name);
        }

        private IEnumerable<(MethodDefinition Method, Instruction Instruction)> Instructions() =>
            main.GetTypes().SelectMany(t => t.Methods).Where(m => m.HasBody).SelectMany(m => m.Body.Instructions.Select(i => (m, i)));

        /// <summary>
        /// 反编译器把闭包、lambda 和状态机折回外层方法：编译器生成的类型（名字以 &lt; 开头）里的方法体，在 C# 里写在外层的普通类型中，
        /// 访问权按那个类型判定。闭包折不回去时代码留在生成的类型里，按外层判定只会多放宽，不会少。
        /// </summary>
        private static TypeDefinition SourceType(MethodDefinition method)
        {
            var type = method.DeclaringType;
            while (type.Name.StartsWith('<') && type.DeclaringType is { } outer) type = outer;
            return type;
        }

        private void Use(Instruction instruction, MethodDefinition method)
        {
            var from = SourceType(method);
            switch (instruction.Operand)
            {
                case TypeReference type: Reference(type, from); break;
                case MethodReference reference:
                    Reference(reference.DeclaringType, from);
                    if (reference is GenericInstanceMethod generic)
                        foreach (var argument in generic.GenericArguments) Reference(argument, from);
                    if (reference.Resolve() is { } target) Member(target, instruction, method);
                    break;
                case FieldReference reference:
                    Reference(reference.DeclaringType, from);
                    if (reference.Resolve() is { } field) Field(field, reference, instruction, method);
                    break;
            }
        }

        private void Field(FieldDefinition field, FieldReference reference, Instruction instruction, MethodDefinition method)
        {
            if (field.Module != main) return;
            if (demoted.Contains(field)) demotedReferences.Add(reference);
            if (!demoted.Contains(field) && Property(field) is { } property)
            {
                // 反编译器把后备字段写成属性：访问权看对应的访问器。
                var accessor = Writes(instruction) ? property.SetMethod : property.GetMethod;
                if (accessor is not null) Member(accessor, instruction, method);
                return;
            }
            // 反编译器把带 DecimalConstant 的只读字段写成 const；方法体里写它时就不是常量。
            if (Writes(instruction) && field.CustomAttributes.Where(a => a.AttributeType.Name == "DecimalConstantAttribute").ToArray() is { Length: > 0 } constants)
            {
                foreach (var attribute in constants) field.CustomAttributes.Remove(attribute);
                changed.Add(field.Module);
            }
            if (field.IsInitOnly && Writes(instruction) && !InOwnInitializer(field, method, instruction))
            {
                field.IsInitOnly = false;
                changed.Add(field.Module);
                // 只读结构体的字段都必须 readonly；有字段不再只读时结构体也不再是只读的。
                var attributes = field.DeclaringType.CustomAttributes;
                foreach (var attribute in attributes.Where(a => a.AttributeType.FullName == "System.Runtime.CompilerServices.IsReadOnlyAttribute").ToArray()) attributes.Remove(attribute);
            }
            if (Accessible(field.Attributes & FieldAttributes.FieldAccessMask, field.DeclaringType, field.IsStatic, instruction, method)) return;
            field.Attributes = field.Attributes & ~FieldAttributes.FieldAccessMask | FieldAttributes.Assembly;
            changed.Add(field.Module);
            Raise(field.FieldType, false);
        }

        /// <summary>成员的签名不能比成员本身更难访问（CS0050～CS0053）：放宽成员时连带放宽签名里的类型。</summary>
        private void Raise(TypeReference type, bool toPublic)
        {
            switch (type)
            {
                case GenericParameter: return;
                case GenericInstanceType generic:
                    Raise(generic.ElementType, toPublic);
                    foreach (var argument in generic.GenericArguments) Raise(argument, toPublic);
                    return;
                case TypeSpecification specification:
                    Raise(specification.ElementType, toPublic);
                    return;
            }
            for (var definition = type.Resolve(); definition is not null; definition = definition.DeclaringType)
            {
                if (definition.Module != main) continue;
                var visibility = definition.Attributes & TypeAttributes.VisibilityMask;
                var enough = definition.IsNested
                    ? visibility == TypeAttributes.NestedPublic || !toPublic && visibility is TypeAttributes.NestedAssembly or TypeAttributes.NestedFamORAssem
                    : visibility == TypeAttributes.Public || !toPublic;
                if (enough) continue;
                definition.Attributes = definition.Attributes & ~TypeAttributes.VisibilityMask | (definition.IsNested
                    ? toPublic ? TypeAttributes.NestedPublic : TypeAttributes.NestedAssembly
                    : TypeAttributes.Public);
                changed.Add(definition.Module);
            }
        }

        private void Member(MethodDefinition target, Instruction instruction, MethodDefinition method)
        {
            if (target.Module != main) return;
            var isFunctionPointer = instruction.OpCode.Code is Code.Ldftn or Code.Ldvirtftn;
            if (Accessible((FieldAttributes)(target.Attributes & MethodAttributes.MemberAccessMask), target.DeclaringType, target.IsStatic || isFunctionPointer, instruction, method)) return;
            if (target.IsVirtual) Family(target);
            else Widen(target, MethodAttributes.Assembly);
        }

        private void Widen(MethodDefinition method, MethodAttributes access)
        {
            method.Attributes = method.Attributes & ~MethodAttributes.MemberAccessMask | access;
            changed.Add(method.Module);
            Raise(method.ReturnType, access == MethodAttributes.Public);
            foreach (var parameter in method.Parameters) Raise(parameter.ParameterType, access == MethodAttributes.Public);
            // 事件的 add 和 remove 共用一个访问级别。
            foreach (var @event in method.DeclaringType.Events.Where(e => e.AddMethod == method || e.RemoveMethod == method))
                foreach (var accessor in new[] { @event.AddMethod, @event.RemoveMethod })
                    if (accessor is not null && accessor != method) accessor.Attributes = accessor.Attributes & ~MethodAttributes.MemberAccessMask | access;
        }

        /// <summary>虚方法和它的重写必须同一访问级别：整个重写族一起改成 public。</summary>
        private void Family(MethodDefinition method)
        {
            if (!widened.Add(method)) return;
            var root = method;
            while (!root.IsNewSlot && Overridden(root) is { } above) root = above;
            // 重写外部方法的访问级别跟外部声明一致，不能放宽。
            if (root.Module != main) return;
            var pending = new Stack<TypeDefinition>([root.DeclaringType]);
            while (pending.TryPop(out var type))
            {
                foreach (var candidate in type.Methods.Where(m => m == root || m.IsVirtual && !m.IsNewSlot && Same(m, root)))
                {
                    widened.Add(candidate);
                    Widen(candidate, MethodAttributes.Public);
                }
                foreach (var below in Derived().GetValueOrDefault(type) ?? []) pending.Push(below);
            }
        }

        private static MethodDefinition? Overridden(MethodDefinition method)
        {
            for (var type = method.DeclaringType.BaseType?.Resolve(); type is not null; type = type.BaseType?.Resolve())
                if (type.Methods.FirstOrDefault(m => m.IsVirtual && Same(m, method)) is { } match) return match;
            return null;
        }

        private static bool Same(MethodDefinition left, MethodDefinition right) =>
            left.Name == right.Name && left.Parameters.Count == right.Parameters.Count && left.GenericParameters.Count == right.GenericParameters.Count
            && left.Parameters.Zip(right.Parameters).All(p => SameParameter(p.First.ParameterType, p.Second.ParameterType));

        /// <summary>重写的形参可能把基类的类型参数换成了实参；含类型参数的位置不比较。</summary>
        private static bool SameParameter(TypeReference left, TypeReference right) =>
            left.ContainsGenericParameter || right.ContainsGenericParameter || left.FullName == right.FullName;

        private Dictionary<TypeDefinition, List<TypeDefinition>> Derived()
        {
            if (derived is not null) return derived;
            derived = [];
            foreach (var type in main.GetTypes())
                if (type.BaseType?.Resolve() is { } parent)
                {
                    if (!derived.TryGetValue(parent, out var list)) derived[parent] = list = [];
                    list.Add(type);
                }
            return derived;
        }

        /// <summary>C# 的访问规则。受保护成员还要求接收者的类型是访问者本身或其派生类（CS1540）。</summary>
        private bool Accessible(FieldAttributes access, TypeDefinition owner, bool isStatic, Instruction instruction, MethodDefinition method)
        {
            var from = SourceType(method);
            var sameModule = owner.Module == from.Module;
            var family = access is FieldAttributes.Family or FieldAttributes.FamORAssem or FieldAttributes.FamANDAssem && Enclosing(from).Any(c => DerivesFrom(c, owner))
                && (isStatic || ReceiverType(instruction, method) is { } receiver && Enclosing(from).Any(c => DerivesFrom(c, owner) && DerivesFrom(receiver, c)));
            return access switch
            {
                FieldAttributes.Public => true,
                FieldAttributes.Private => Enclosing(from).Contains(owner),
                FieldAttributes.Assembly => sameModule,
                FieldAttributes.Family => family,
                FieldAttributes.FamORAssem => sameModule || family,
                FieldAttributes.FamANDAssem => sameModule && family,
                _ => false,
            };
        }

        private void Reference(TypeReference type, TypeDefinition from)
        {
            switch (type)
            {
                case GenericParameter: return;
                case GenericInstanceType generic:
                    Reference(generic.ElementType, from);
                    foreach (var argument in generic.GenericArguments) Reference(argument, from);
                    return;
                case TypeSpecification specification:
                    Reference(specification.ElementType, from);
                    return;
            }
            for (var definition = type.Resolve(); definition is not null; definition = definition.DeclaringType)
            {
                if (definition.Module != main || TypeAccessible(definition, from)) continue;
                definition.Attributes = definition.Attributes & ~TypeAttributes.VisibilityMask | (definition.IsNested ? TypeAttributes.NestedAssembly : TypeAttributes.Public);
                changed.Add(definition.Module);
            }
        }

        private static bool TypeAccessible(TypeDefinition type, TypeDefinition from)
        {
            var sameModule = type.Module == from.Module;
            if (!type.IsNested) return type.IsPublic || sameModule;
            var family = Enclosing(from).Any(c => DerivesFrom(c, type.DeclaringType));
            return (type.Attributes & TypeAttributes.VisibilityMask) switch
            {
                TypeAttributes.NestedPublic => true,
                TypeAttributes.NestedPrivate => Enclosing(from).Contains(type.DeclaringType),
                TypeAttributes.NestedAssembly => sameModule,
                TypeAttributes.NestedFamily => family,
                TypeAttributes.NestedFamORAssem => sameModule || family,
                TypeAttributes.NestedFamANDAssem => sameModule && family,
                _ => false,
            };
        }

        private static IEnumerable<TypeDefinition> Enclosing(TypeDefinition type)
        {
            for (var current = type; current is not null; current = current.DeclaringType) yield return current;
        }

        private static bool DerivesFrom(TypeDefinition? type, TypeDefinition owner)
        {
            for (; type is not null; type = type.BaseType?.Resolve())
                if (type == owner) return true;
            return false;
        }

        private static PropertyDefinition? Property(FieldDefinition field)
        {
            if (!field.Name.StartsWith('<') || !field.Name.EndsWith(">k__BackingField", StringComparison.Ordinal)) return null;
            var name = field.Name[1..field.Name.IndexOf('>')];
            return field.DeclaringType.Properties.FirstOrDefault(p => p.Name == name);
        }

        /// <summary>这次访问只能写成字段：取了会被写的地址，或者写入时属性没有 set 且不在本类构造函数里。</summary>
        private static bool RequiresField(FieldDefinition field, PropertyDefinition property, MethodDefinition method, Instruction instruction)
        {
            if (instruction.OpCode.Code is Code.Ldflda or Code.Ldsflda) return Writes(instruction);
            if (instruction.OpCode.Code is not (Code.Stfld or Code.Stsfld)) return property.GetMethod is null;
            return property.SetMethod is null && !InOwnInitializer(field, method, instruction);
        }

        /// <summary>只读字段和只有 get 的属性只能在本类构造函数里经 this 写入。</summary>
        private static bool InOwnInitializer(FieldDefinition field, MethodDefinition method, Instruction instruction)
        {
            if (method.DeclaringType != field.DeclaringType) return false;
            if (field.IsStatic) return method.Name == ".cctor";
            if (method.Name != ".ctor" || !method.HasThis || ReceiverProducer(instruction, method) is not { } producer) return false;
            if (producer is not ({ OpCode.Code: Code.Ldarg_0 } or { Operand: ParameterDefinition { Index: -1 } })) return false;
            // 紧跟着汇合点时接收者来自条件表达式，不一定是 this。
            return !method.Body.Instructions.Any(i => i.Operand == producer.Next || i.Operand is Instruction[] targets && targets.Contains(producer.Next));
        }

        private static bool Writes(Instruction instruction)
        {
            if (instruction.OpCode.Code is Code.Stfld or Code.Stsfld) return true;
            if (instruction.OpCode.Code is not (Code.Ldflda or Code.Ldsflda)) return false;
            var next = instruction.Next;
            while (next is { OpCode.Code: Code.Ldflda }) next = next.Next;
            return next is not { OpCode.Code: Code.Ldfld or Code.Ldobj };
        }

        /// <summary>退回普通属性：后备字段换成合法名字，反编译器就不再把它写成属性。</summary>
        private void Demote(FieldDefinition field)
        {
            var property = Property(field)!;
            var name = PlainName(field.Name);
            while (field.DeclaringType.Fields.Any(f => f != field && f.Name == name) || field.DeclaringType.Properties.Any(p => p.Name == name)) name = "_" + name;
            field.Name = name;
            changed.Add(field.Module);
            Generated(field.CustomAttributes);
            if (property.GetMethod is { } getter) Generated(getter.CustomAttributes);
            if (property.SetMethod is { } setter) Generated(setter.CustomAttributes);
        }

        private static void Generated(Mono.Collections.Generic.Collection<CustomAttribute> attributes)
        {
            foreach (var attribute in attributes.Where(a => a.AttributeType.Name is "CompilerGeneratedAttribute" or "DebuggerBrowsableAttribute").ToArray()) attributes.Remove(attribute);
        }

        private static string PlainName(string backing) =>
            backing.StartsWith('<') && backing.EndsWith(">k__BackingField", StringComparison.Ordinal) ? "_" + backing[1..backing.IndexOf('>')].Replace('.', '_') : backing;

        /// <summary>沿直线路径找压入接收者的指令，得到接收者的静态类型；找不到时返回空，按不可访问处理。</summary>
        private static TypeDefinition? ReceiverType(Instruction instruction, MethodDefinition method) =>
            ReceiverProducer(instruction, method) is { } producer ? Pushed(producer, method)?.Resolve() : null;

        private static Instruction? ReceiverProducer(Instruction instruction, MethodDefinition method)
        {
            var above = instruction.OpCode.Code switch
            {
                Code.Ldfld or Code.Ldflda => 0,
                Code.Stfld => 1,
                Code.Call or Code.Callvirt => ((MethodReference)instruction.Operand).Parameters.Count,
                _ => -1,
            };
            if (above < 0) return null;
            for (var current = instruction.Previous; current is not null; current = current.Previous)
            {
                if (current.OpCode.FlowControl is FlowControl.Branch or FlowControl.Cond_Branch or FlowControl.Return or FlowControl.Throw) return null;
                var (pop, push) = StackEffect(current);
                if (above < push) return current;
                above += pop - push;
            }
            return null;
        }

        private static (int Pop, int Push) StackEffect(Instruction instruction)
        {
            if (instruction.Operand is MethodReference method && instruction.OpCode.FlowControl is FlowControl.Call)
            {
                var push = method.ReturnType.FullName == "System.Void" ? 0 : 1;
                return instruction.OpCode.Code == Code.Newobj ? (method.Parameters.Count, 1) : (method.Parameters.Count + (method.HasThis ? 1 : 0), push);
            }
            var pops = instruction.OpCode.StackBehaviourPop switch
            {
                StackBehaviour.Pop0 => 0,
                StackBehaviour.Pop1 or StackBehaviour.Popi or StackBehaviour.Popref => 1,
                StackBehaviour.Pop1_pop1 or StackBehaviour.Popi_pop1 or StackBehaviour.Popi_popi or StackBehaviour.Popi_popi8 or StackBehaviour.Popi_popr4 or StackBehaviour.Popi_popr8 or StackBehaviour.Popref_pop1 or StackBehaviour.Popref_popi => 2,
                StackBehaviour.Popi_popi_popi or StackBehaviour.Popref_popi_popi or StackBehaviour.Popref_popi_popi8 or StackBehaviour.Popref_popi_popr4 or StackBehaviour.Popref_popi_popr8 or StackBehaviour.Popref_popi_popref => 3,
                _ => 0,
            };
            var pushes = instruction.OpCode.StackBehaviourPush switch
            {
                StackBehaviour.Push0 => 0,
                StackBehaviour.Push1_push1 => 2,
                _ => 1,
            };
            return (pops, pushes);
        }

        private static TypeReference? Pushed(Instruction producer, MethodDefinition method)
        {
            switch (producer.OpCode.Code)
            {
                case Code.Ldarg_0: return method.HasThis ? method.DeclaringType : method.Parameters[0].ParameterType;
                case Code.Ldarg_1: return method.Parameters[method.HasThis ? 0 : 1].ParameterType;
                case Code.Ldarg_2: return method.Parameters[method.HasThis ? 1 : 2].ParameterType;
                case Code.Ldarg_3: return method.Parameters[method.HasThis ? 2 : 3].ParameterType;
                case Code.Ldarg or Code.Ldarg_S: return producer.Operand is ParameterDefinition { Index: >= 0 } p ? p.ParameterType : method.DeclaringType;
                case Code.Ldloc or Code.Ldloc_S: return ((VariableDefinition)producer.Operand).VariableType;
                case Code.Ldloc_0: return method.Body.Variables[0].VariableType;
                case Code.Ldloc_1: return method.Body.Variables[1].VariableType;
                case Code.Ldloc_2: return method.Body.Variables[2].VariableType;
                case Code.Ldloc_3: return method.Body.Variables[3].VariableType;
                case Code.Ldfld or Code.Ldsfld: return ((FieldReference)producer.Operand).FieldType;
                case Code.Call or Code.Callvirt: return ((MethodReference)producer.Operand).ReturnType;
                case Code.Newobj: return ((MethodReference)producer.Operand).DeclaringType;
                case Code.Castclass or Code.Isinst: return (TypeReference)producer.Operand;
                default: return null;
            }
        }
    }
}
