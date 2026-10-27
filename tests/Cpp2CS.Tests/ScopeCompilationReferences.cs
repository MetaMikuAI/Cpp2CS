using Microsoft.CodeAnalysis;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests;

/// <summary>部分源码编译的引用副本：范围内类型转发至源码，范围外声明保持原可见性。</summary>
internal static class ScopeCompilationReferences
{
    internal static MetadataReference[] Create(string assemblies, string assembly, IReadOnlySet<string> roots, string sourceName, string output,
        MetadataReference[]? declarations = null)
    {
        var references = Path.Combine(output, "refs");
        Directory.CreateDirectory(references);
        var path = Path.Combine(references, assembly + ".dll");
        using var resolver = new SourceResolver(sourceName);
        resolver.AddSearchDirectory(assemblies);
        // 写入引用签名中的枚举常量时，Cecil 仍需原定义确认枚举底层类型。
        using var definitions = AssemblyDefinition.ReadAssembly(Path.Combine(assemblies, assembly + ".dll"), new ReaderParameters { AssemblyResolver = resolver });
        resolver.Source = definitions;
        using var module = ModuleDefinition.ReadModule(Path.Combine(assemblies, assembly + ".dll"), new ReaderParameters { AssemblyResolver = resolver });
        var selected = module.Types.Where(t => roots.Contains(t.FullName)).ToArray();
        if (selected.Length != roots.Count) throw new InvalidDataException("范围源码与引用程序集的顶层类型不一致");
        Rewrite(module, selected, sourceName);
        module.Write(path);
        File.WriteAllText(Path.Combine(output, "references.local.md"),
            "# 编译引用\n\n此引用副本仅用于编译检查，不能运行。范围内类型转发到当前源码程序集；范围外类型保留原声明与访问级别。\n\n"
            + "InternalsVisibleTo 仅恢复原同程序集的 internal 访问关系，private/protected 不放宽。方法体替换为引用占位体，不计入恢复、字节或执行指标。\n");
        declarations ??= Directory.GetFiles(assemblies, "*.dll").Select(p => (MetadataReference)MetadataReference.CreateFromFile(p)).ToArray();
        return declarations.Select(r => Path.GetFileName(r.Display) == assembly + ".dll" ? MetadataReference.CreateFromFile(path) : r).ToArray();
    }

    internal static void Rewrite(ModuleDefinition module, TypeDefinition[] selected, string sourceName)
    {
        var destination = new AssemblyNameReference(sourceName, new Version(0, 0, 0, 0));
        module.AssemblyReferences.Add(destination);
        var removed = selected.SelectMany(Descendants).ToDictionary(t => t.FullName);
        var mapped = new Dictionary<string, TypeReference>();

        TypeReference Type(TypeReference type)
        {
            if (type is GenericParameter) return type;
            if (type is GenericInstanceType generic)
            {
                var result = new GenericInstanceType(Type(generic.ElementType));
                foreach (var argument in generic.GenericArguments) result.GenericArguments.Add(Type(argument));
                return result;
            }
            if (type is ArrayType array)
            {
                var result = new ArrayType(Type(array.ElementType), array.Rank);
                for (var i = 0; i < array.Dimensions.Count; i++) result.Dimensions[i] = array.Dimensions[i];
                return result;
            }
            if (type is ByReferenceType byRef) return new ByReferenceType(Type(byRef.ElementType));
            if (type is PointerType pointer) return new PointerType(Type(pointer.ElementType));
            if (type is RequiredModifierType required) return new RequiredModifierType(Type(required.ModifierType), Type(required.ElementType));
            if (type is OptionalModifierType optional) return new OptionalModifierType(Type(optional.ModifierType), Type(optional.ElementType));
            if (type is PinnedType pinned) return new PinnedType(Type(pinned.ElementType));
            if (type is SentinelType sentinel) return new SentinelType(Type(sentinel.ElementType));
            if (type is TypeSpecification) throw new NotSupportedException($"编译引用类型 {type.GetType().Name}");
            if (type.Scope != module || !removed.TryGetValue(type.FullName, out var definition)) return type;
            if (mapped.TryGetValue(type.FullName, out var cached)) return cached;
            var reference = new TypeReference(type.Namespace, type.Name, module, destination, type.IsValueType);
            mapped.Add(type.FullName, reference);
            if (definition.DeclaringType is { } outer) reference.DeclaringType = Type(outer);
            foreach (var parameter in definition.GenericParameters) reference.GenericParameters.Add(new(parameter.Name, reference));
            return reference;
        }
        MethodReference Method(MethodReference method)
        {
            if (method is GenericInstanceMethod generic)
            {
                var result = new GenericInstanceMethod(Method(generic.ElementMethod));
                foreach (var argument in generic.GenericArguments) result.GenericArguments.Add(Type(argument));
                return result;
            }
            var reference = new MethodReference(method.Name, Type(method.ReturnType), Type(method.DeclaringType))
                { HasThis = method.HasThis, ExplicitThis = method.ExplicitThis, CallingConvention = method.CallingConvention };
            foreach (var parameter in method.GenericParameters) reference.GenericParameters.Add(new(parameter.Name, reference));
            foreach (var parameter in method.Parameters) reference.Parameters.Add(new(Type(parameter.ParameterType)));
            return reference;
        }
        CustomAttributeArgument Argument(CustomAttributeArgument argument) => new(Type(argument.Type), argument.Value switch
        {
            TypeReference type => Type(type),
            CustomAttributeArgument[] array => array.Select(Argument).ToArray(),
            _ => argument.Value,
        });
        void Attributes(ICustomAttributeProvider provider)
        {
            foreach (var attribute in provider.CustomAttributes)
            {
                attribute.Constructor = Method(attribute.Constructor);
                for (var i = 0; i < attribute.ConstructorArguments.Count; i++) attribute.ConstructorArguments[i] = Argument(attribute.ConstructorArguments[i]);
                for (var i = 0; i < attribute.Fields.Count; i++) attribute.Fields[i] = new(attribute.Fields[i].Name, Argument(attribute.Fields[i].Argument));
                for (var i = 0; i < attribute.Properties.Count; i++) attribute.Properties[i] = new(attribute.Properties[i].Name, Argument(attribute.Properties[i].Argument));
            }
        }
        void Parameters(IGenericParameterProvider provider)
        {
            foreach (var parameter in provider.GenericParameters)
            {
                Attributes(parameter);
                foreach (var constraint in parameter.Constraints) { constraint.ConstraintType = Type(constraint.ConstraintType); Attributes(constraint); }
            }
        }
        foreach (var type in module.GetTypes().Where(t => !removed.ContainsKey(t.FullName)).ToArray())
        {
            if (type.BaseType is { } basis) type.BaseType = Type(basis);
            foreach (var itf in type.Interfaces) { itf.InterfaceType = Type(itf.InterfaceType); Attributes(itf); }
            Parameters(type); Attributes(type);
            foreach (var field in type.Fields) { field.FieldType = Type(field.FieldType); Attributes(field); }
            foreach (var method in type.Methods)
            {
                method.ReturnType = Type(method.ReturnType);
                Attributes(method); Attributes(method.MethodReturnType); Parameters(method);
                foreach (var parameter in method.Parameters) { parameter.ParameterType = Type(parameter.ParameterType); Attributes(parameter); }
                for (var i = 0; i < method.Overrides.Count; i++) method.Overrides[i] = Method(method.Overrides[i]);
                if (method.HasBody)
                {
                    method.Body = new MethodBody(method);
                    method.Body.Instructions.Add(Instruction.Create(OpCodes.Ldnull));
                    method.Body.Instructions.Add(Instruction.Create(OpCodes.Throw));
                }
            }
            foreach (var property in type.Properties)
            {
                property.PropertyType = Type(property.PropertyType); Attributes(property);
                foreach (var parameter in property.Parameters) parameter.ParameterType = Type(parameter.ParameterType);
            }
            foreach (var e in type.Events) { e.EventType = Type(e.EventType); Attributes(e); }
        }
        Attributes(module); Attributes(module.Assembly);
        foreach (var type in selected)
        {
            module.Types.Remove(type);
            module.ExportedTypes.Add(new(type.Namespace, type.Name, module, destination) { Attributes = TypeAttributes.Forwarder });
        }
        var friend = new MethodReference(".ctor", module.TypeSystem.Void,
            new TypeReference("System.Runtime.CompilerServices", "InternalsVisibleToAttribute", module, module.TypeSystem.CoreLibrary)) { HasThis = true };
        friend.Parameters.Add(new(module.TypeSystem.String));
        var visibility = new CustomAttribute(friend);
        visibility.ConstructorArguments.Add(new(module.TypeSystem.String, sourceName));
        module.Assembly.CustomAttributes.Add(visibility);
        module.Assembly.CustomAttributes.Add(new(new MethodReference(".ctor", module.TypeSystem.Void,
            new TypeReference("System.Runtime.CompilerServices", "ReferenceAssemblyAttribute", module, module.TypeSystem.CoreLibrary)) { HasThis = true }));
    }

    private static IEnumerable<TypeDefinition> Descendants(TypeDefinition type) => type.NestedTypes.SelectMany(Descendants).Prepend(type);

    private sealed class SourceResolver(string sourceName) : DefaultAssemblyResolver
    {
        internal AssemblyDefinition? Source { get; set; }
        public override AssemblyDefinition Resolve(AssemblyNameReference name) => name.Name == sourceName ? Source! : base.Resolve(name);
        public override AssemblyDefinition Resolve(AssemblyNameReference name, ReaderParameters parameters) => name.Name == sourceName ? Source! : base.Resolve(name, parameters);
    }
}
