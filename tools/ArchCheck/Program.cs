using System.Collections.Immutable;
using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;

namespace Cpp2CS.Tools.ArchCheck;

/// <summary>
/// 架构检查：扫描构建出的程序集，核对设计“构造上的强制”一节里可以机检的条目。
/// 用法：ArchCheck 程序集或目录…
/// 规则写成数据。规则涉及的程序集或类型还不存在时，这条规则记为“尚无对象”，不算通过也不算违反。
/// 扫描的单位是每一份不同的产物（按程序集名与模块版本号区分）：同名的不同产物逐份检查，并在结果里列出。
/// </summary>
internal static class Program
{
    /// <summary>程序集的登记：可以直接引用的本项目程序集；是否可信；是否禁止反射。</summary>
    private sealed record Layer(string Name, string[] MayReference, bool Trusted, bool ForbidReflection);

    // 设计里“程序集”一表的依赖方向。可引用的范围按传递闭包计：能引用内核，就能引用内核公开的签名里出现的快照与规格。
    private static readonly Layer[] layers =
    [
        new("Cpp2CS.Model", [], Trusted: true, ForbidReflection: false),
        new("Cpp2CS.Input", ["Cpp2CS.Model"], Trusted: true, ForbidReflection: false),
        new("Cpp2CS.Snapshot", ["Cpp2CS.Model"], Trusted: true, ForbidReflection: false),
        new("Cpp2CS.Target", ["Cpp2CS.Snapshot", "Cpp2CS.Input"], Trusted: true, ForbidReflection: false),
        new("Cpp2CS.Spec", ["Cpp2CS.Snapshot"], Trusted: true, ForbidReflection: false),
        new("Cpp2CS.Kernel", ["Cpp2CS.Snapshot", "Cpp2CS.Spec"], Trusted: true, ForbidReflection: false),
        new("Cpp2CS.Facts", ["Cpp2CS.Kernel", "Cpp2CS.Model"], Trusted: true, ForbidReflection: false),
        new("Cpp2CS.Discovery", ["Cpp2CS.Kernel"], Trusted: false, ForbidReflection: true),
        new("Cpp2CS.Output", ["Cpp2CS.Kernel"], Trusted: true, ForbidReflection: false),
    ];

    // 只能由本程序集内部构造的类型：项只出自项池，图与快照只出自校验过的构造器，凭据、解释、方法体只出自引擎、选择、下降。
    private static readonly (string Assembly, string Type)[] sealedConstruction =
    [
        ("Cpp2CS.Snapshot", "Cpp2CS.Snapshot.Term"),
        ("Cpp2CS.Snapshot", "Cpp2CS.Snapshot.FlowGraph`1"),
        ("Cpp2CS.Snapshot", "Cpp2CS.Snapshot.FlowBlock`1"),
        ("Cpp2CS.Snapshot", "Cpp2CS.Snapshot.MethodSnapshot"),
        ("Cpp2CS.Kernel", "Cpp2CS.Kernel.Certificate"),
        ("Cpp2CS.Kernel", "Cpp2CS.Kernel.Explanation"),
        ("Cpp2CS.Kernel", "Cpp2CS.Kernel.ManagedBody"),
    ];

    // 内核之外拿不到入边，也拿不到来源关系（设计 7.3、第 11 节）：这些成员不得公开。
    private static readonly (string Assembly, string Type, string Member)[] kernelOnly =
    [
        ("Cpp2CS.Kernel", "Cpp2CS.Kernel.Sources.FlowShape", "InEdges"),
        ("Cpp2CS.Kernel", "Cpp2CS.Kernel.Sources.ValueSources", "Alternatives"),
    ];

    // 反射与绕过可见性、绕过构造的途径：这些命名空间与类型的引用，以及下列类型上的成员。
    // Unsafe、MemoryMarshal、ImmutableCollectionsMarshal 只列成员：编译器为集合表达式与 params 跨度生成的代码会用到它们的另一些成员
    // （Unsafe.As<TFrom, TTo>、Unsafe.Add、Unsafe.AsRef、MemoryMarshal.CreateSpan、CreateReadOnlySpan、ImmutableCollectionsMarshal.AsImmutableArray）。
    private static readonly string[] reflectionNamespaces = ["System.Reflection", "System.Reflection.Emit", "System.Linq.Expressions"];
    private static readonly string[] reflectionTypes =
    [
        "System.Activator",
        "System.Runtime.CompilerServices.UnsafeAccessorAttribute",
        "System.Runtime.InteropServices.Marshal",
        "System.Runtime.Serialization.FormatterServices",
    ];
    private static readonly (string Type, string[] Members)[] reflectionMembers =
    [
        ("System.Type", ["GetMethod", "GetMethods", "GetField", "GetFields", "GetProperty", "GetProperties", "GetMember", "GetMembers",
            "GetConstructor", "GetConstructors", "InvokeMember", "GetType", "GetNestedType", "GetNestedTypes", "GetEvent", "GetEvents",
            "GetInterface", "GetInterfaces", "GetDefaultMembers", "FindMembers", "MakeGenericType", "get_TypeInitializer",
            "GetMemberWithSameMetadataDefinitionAs"]),
        ("System.Delegate", ["DynamicInvoke", "get_Method", "CreateDelegate"]),
        // 不经构造函数得到对象。
        ("System.Runtime.CompilerServices.RuntimeHelpers", ["GetUninitializedObject"]),
        // 取得不可变集合、只读跨度背后可写的存储。
        ("System.Runtime.InteropServices.ImmutableCollectionsMarshal", ["AsArray"]),
        ("System.Runtime.InteropServices.MemoryMarshal", ["AsMemory", "GetReference", "TryGetArray", "GetArrayDataReference"]),
        ("System.Runtime.CompilerServices.Unsafe", ["AsPointer", "Write", "WriteUnaligned", "Copy", "CopyBlock", "CopyBlockUnaligned",
            "InitBlock", "InitBlockUnaligned"]),
    ];

    // 现在还没有检查对象的条目，列出来以免被当成已经检查过。
    private static readonly string[] pending =
    [
        "入边与来源图的遍历接口不在只读查询面上（只读查询面尚未建立；这些成员不公开另有一条检查）",
        "下降的代码不引用走查与独立关系（下降尚未建立）",
    ];

    /// <summary>一份产物。</summary>
    private sealed record Artifact(string Path, string Name, Guid Version, PEReader Pe, MetadataReader Md);

    private static int Main(string[] arguments)
    {
        var files = new List<string>();
        foreach (string argument in arguments)
        {
            if (Directory.Exists(argument)) files.AddRange(Directory.EnumerateFiles(argument, "Cpp2CS.*.dll", SearchOption.AllDirectories));
            else if (File.Exists(argument)) files.Add(argument);
            else { Console.Error.WriteLine($"找不到 {argument}"); return 2; }
        }
        if (files.Count == 0) { Console.Error.WriteLine("用法：ArchCheck 程序集或目录…"); return 2; }

        // 同一份产物的多个副本只查一次；同名而模块版本号不同的产物各查一次。
        var artifacts = new List<Artifact>();
        var versions = new HashSet<(string, Guid)>();
        foreach (string file in files.Order(StringComparer.Ordinal))
        {
            var pe = new PEReader(File.OpenRead(file));
            if (!pe.HasMetadata) { pe.Dispose(); continue; }
            var md = pe.GetMetadataReader();
            if (!md.IsAssembly) { pe.Dispose(); continue; }
            string name = md.GetString(md.GetAssemblyDefinition().Name);
            var version = md.GetGuid(md.GetModuleDefinition().Mvid);
            if (!name.StartsWith("Cpp2CS.", StringComparison.Ordinal) || !versions.Add((name, version))) { pe.Dispose(); continue; }
            artifacts.Add(new(file, name, version, pe, md));
        }

        var violations = new List<string>();
        var absent = new List<string>(pending);
        var foundTypes = new HashSet<(string, string)>();
        var foundMembers = new HashSet<(string, string, string)>();
        int checks = 0;
        foreach (var artifact in artifacts)
        {
            var (name, md) = (artifact.Name, artifact.Md);
            string label = artifacts.Count(a => a.Name == name) > 1 ? $"{name}（{artifact.Path}）" : name;

            // 一、依赖方向。
            var layer = Array.Find(layers, l => name == l.Name || name.StartsWith(l.Name + ".", StringComparison.Ordinal));
            checks++;
            if (layer is null) { violations.Add($"{label}：没有登记在程序集表里"); continue; }
            var allowed = Closure(layer);
            foreach (var handle in md.AssemblyReferences)
            {
                string reference = md.GetString(md.GetAssemblyReference(handle).Name);
                if (!reference.StartsWith("Cpp2CS.", StringComparison.Ordinal)) continue;
                checks++;
                if (!allowed.Any(a => reference == a || reference.StartsWith(a + ".", StringComparison.Ordinal)))
                    violations.Add($"{label} 引用了 {reference}，依赖方向不允许");
            }

            // 二、可信的程序集不向别的程序集开放内部成员。
            if (layer.Trusted)
            {
                checks++;
                foreach (var handle in md.GetAssemblyDefinition().GetCustomAttributes())
                    if (AttributeName(md, md.GetCustomAttribute(handle)) == "System.Runtime.CompilerServices.InternalsVisibleToAttribute")
                        violations.Add($"{label} 用 InternalsVisibleTo 开放了内部成员");
            }

            // 三、不可信的程序集不使用反射。
            if (layer.ForbidReflection)
            {
                checks++;
                Reflection(md, label, violations);
            }

            // 四、不可信的程序集对本项目程序集的引用只落在公开的类型与成员上。
            if (!layer.Trusted)
            {
                checks++;
                Visibility(md, label, artifacts, violations, absent);
            }

            // 五、只能在内部构造的类型没有对外的构造途径：构造函数不公开、不对派生类开放，类型自己不公开返回自身实例的方法。
            foreach (var handle in md.TypeDefinitions)
            {
                var type = md.GetTypeDefinition(handle);
                string full = FullName(md, type);
                if (!sealedConstruction.Contains((name, full))) continue;
                foundTypes.Add((name, full));
                checks++;
                foreach (var methodHandle in type.GetMethods())
                {
                    var method = md.GetMethodDefinition(methodHandle);
                    string member = md.GetString(method.Name);
                    if (!Exposed(method.Attributes)) continue;
                    if (member == ".ctor") violations.Add($"{full} 有对外的构造函数（{method.Attributes & MethodAttributes.MemberAccessMask}）");
                    else if (member != ".cctor" && ReturnTypeName(md, method) == full)
                        violations.Add($"{full} 的 {member} 对外返回自身的实例");
                }
            }

            // 六、内核之外拿不到入边与来源关系。
            foreach (var handle in md.TypeDefinitions)
            {
                var type = md.GetTypeDefinition(handle);
                string full = FullName(md, type);
                foreach (var methodHandle in type.GetMethods())
                {
                    var method = md.GetMethodDefinition(methodHandle);
                    string member = md.GetString(method.Name);
                    if (!kernelOnly.Contains((name, full, member))) continue;
                    if (foundMembers.Add((name, full, member))) checks++;
                    if (Exposed(method.Attributes)) violations.Add($"{full}.{member} 对内核之外可见");
                }
            }
        }

        var seen = artifacts.Select(a => a.Name).Distinct().Order(StringComparer.Ordinal).ToList();
        foreach (var layer in layers)
            if (!seen.Any(s => s == layer.Name || s.StartsWith(layer.Name + ".", StringComparison.Ordinal))) absent.Add($"程序集 {layer.Name} 的各条规则（程序集尚未建立）");
        foreach (var item in sealedConstruction)
            if (seen.Contains(item.Assembly) && !foundTypes.Contains(item)) absent.Add($"{item.Type} 没有对外的构造途径（类型尚未建立）");
        foreach (var item in kernelOnly)
            if (seen.Contains(item.Assembly) && !foundMembers.Contains(item)) absent.Add($"{item.Type}.{item.Member} 不对内核之外可见（成员尚未建立）");

        var duplicates = artifacts.GroupBy(a => a.Name).Where(g => g.Count() > 1).ToList();
        Console.WriteLine($"架构检查：程序集 {seen.Count} 个（{string.Join("、", seen)}），产物 {artifacts.Count} 份，检查 {checks} 项，违反 {violations.Count} 项，尚无对象 {absent.Count} 项");
        foreach (var group in duplicates)
            Console.WriteLine($"  同名的不同产物，逐份检查：{group.Key} {group.Count()} 份（{string.Join("、", group.Select(a => a.Path))}）");
        foreach (string violation in violations) Console.WriteLine($"  违反：{violation}");
        foreach (string item in absent) Console.WriteLine($"  尚无对象：{item}");
        foreach (var artifact in artifacts) artifact.Pe.Dispose();
        return violations.Count == 0 ? 0 : 1;
    }

    /// <summary>对别的程序集可见：公开、受保护，或受保护与程序集内二者之一。</summary>
    private static bool Exposed(MethodAttributes attributes) =>
        (attributes & MethodAttributes.MemberAccessMask) is MethodAttributes.Public or MethodAttributes.Family or MethodAttributes.FamORAssem;

    private static bool Exposed(FieldAttributes attributes) =>
        (attributes & FieldAttributes.FieldAccessMask) is FieldAttributes.Public or FieldAttributes.Family or FieldAttributes.FamORAssem;

    private static string FullName(MetadataReader md, TypeDefinition type)
    {
        var outer = type.GetDeclaringType();
        if (!outer.IsNil) return FullName(md, md.GetTypeDefinition(outer)) + "/" + md.GetString(type.Name);
        return md.GetString(type.Namespace) + "." + md.GetString(type.Name);
    }

    private static string FullName(MetadataReader md, TypeReference reference)
    {
        if (reference.ResolutionScope.Kind == HandleKind.TypeReference)
            return FullName(md, md.GetTypeReference((TypeReferenceHandle)reference.ResolutionScope)) + "/" + md.GetString(reference.Name);
        return md.GetString(reference.Namespace) + "." + md.GetString(reference.Name);
    }

    /// <summary>
    /// 反射的引用。命名空间规则有一个例外：只被当作特性构造的特性类型（例如 SDK 生成的 AssemblyCompanyAttribute），
    /// 它的成员引用只有构造函数；构造特性对象不是反射，读取特性要经过别的反射成员，那些仍在检查之内。
    /// </summary>
    private static void Reflection(MetadataReader md, string label, List<string> violations)
    {
        var members = new Dictionary<TypeReferenceHandle, List<string>>();
        foreach (var handle in md.MemberReferences)
        {
            var member = md.GetMemberReference(handle);
            if (member.Parent.Kind != HandleKind.TypeReference) continue;
            var parent = (TypeReferenceHandle)member.Parent;
            if (!members.TryGetValue(parent, out var names)) members[parent] = names = [];
            string name = md.GetString(member.Name);
            names.Add(name);
            // Unsafe.As<T>(object) 把对象当作任意引用类型：与编译器使用的 As<TFrom, TTo>(ref TFrom) 按泛型参数个数区分。
            if (name == "As" && FullName(md, md.GetTypeReference(parent)) == "System.Runtime.CompilerServices.Unsafe" && GenericArity(md, member) == 1)
                violations.Add($"{label} 调用了 System.Runtime.CompilerServices.Unsafe::As<T>(object)");
        }
        foreach (var handle in md.TypeReferences)
        {
            var reference = md.GetTypeReference(handle);
            string @namespace = md.GetString(reference.Namespace), name = md.GetString(reference.Name), full = FullName(md, reference);
            if (reflectionTypes.Contains(full)) { violations.Add($"{label} 引用了 {full}"); continue; }
            if (!reflectionNamespaces.Contains(@namespace)) continue;
            bool attributeOnly = name.EndsWith("Attribute", StringComparison.Ordinal)
                && members.GetValueOrDefault(handle, []).All(member => member == ".ctor");
            if (!attributeOnly) violations.Add($"{label} 引用了 {full}");
        }
        foreach (var (parent, names) in members)
        {
            string full = FullName(md, md.GetTypeReference(parent));
            foreach (var (type, forbidden) in reflectionMembers)
                if (type == full)
                    foreach (string name in names.Distinct())
                        if (forbidden.Contains(name)) violations.Add($"{label} 调用了 {full}::{name}");
        }
    }

    /// <summary>不可信程序集对本项目程序集里类型与成员的引用，须落在对它可见的定义上。引用的程序集不在扫描范围内时记为尚无对象。</summary>
    private static void Visibility(MetadataReader md, string label, List<Artifact> artifacts, List<string> violations, List<string> absent)
    {
        // 引用的类型 → 被引用程序集里的定义（逐份）。
        var resolved = new Dictionary<TypeReferenceHandle, List<(MetadataReader Md, TypeDefinition Type)>>();
        List<(MetadataReader, TypeDefinition)>? Resolve(TypeReferenceHandle handle)
        {
            if (resolved.TryGetValue(handle, out var known)) return known;
            var reference = md.GetTypeReference(handle);
            List<(MetadataReader, TypeDefinition)>? result = null;
            var scope = reference.ResolutionScope;
            if (scope.Kind == HandleKind.AssemblyReference)
            {
                string assembly = md.GetString(md.GetAssemblyReference((AssemblyReferenceHandle)scope).Name);
                if (!assembly.StartsWith("Cpp2CS.", StringComparison.Ordinal)) return resolved[handle] = null!;
                var targets = artifacts.Where(a => a.Name == assembly).ToList();
                if (targets.Count == 0) { absent.Add($"{label} 引用的 {assembly} 不在扫描范围内，可见性无从核对"); return resolved[handle] = null!; }
                string full = FullName(md, reference);
                result = [];
                foreach (var target in targets)
                {
                    var found = target.Md.TypeDefinitions.Select(target.Md.GetTypeDefinition)
                        .Where(t => t.GetDeclaringType().IsNil && FullName(target.Md, t) == full).ToList();
                    if (found.Count == 0) violations.Add($"{label} 引用的类型 {full} 在 {target.Path} 里不存在");
                    foreach (var type in found)
                    {
                        if ((type.Attributes & TypeAttributes.VisibilityMask) != TypeAttributes.Public)
                            violations.Add($"{label} 引用了 {assembly} 的非公开类型 {full}");
                        result.Add((target.Md, type));
                    }
                }
            }
            else if (scope.Kind == HandleKind.TypeReference && Resolve((TypeReferenceHandle)scope) is { } outers)
            {
                string name = md.GetString(reference.Name);
                result = [];
                foreach (var (targetMd, outer) in outers)
                    foreach (var nestedHandle in outer.GetNestedTypes())
                    {
                        var nested = targetMd.GetTypeDefinition(nestedHandle);
                        if (targetMd.GetString(nested.Name) != name) continue;
                        if ((nested.Attributes & TypeAttributes.VisibilityMask) is not (TypeAttributes.NestedPublic or TypeAttributes.NestedFamily or TypeAttributes.NestedFamORAssem))
                            violations.Add($"{label} 引用了非公开的嵌套类型 {FullName(md, reference)}");
                        result.Add((targetMd, nested));
                    }
            }
            return resolved[handle] = result!;
        }

        foreach (var handle in md.TypeReferences) Resolve(handle);
        foreach (var handle in md.MemberReferences)
        {
            var member = md.GetMemberReference(handle);
            TypeReferenceHandle? parent = member.Parent.Kind switch
            {
                HandleKind.TypeReference => (TypeReferenceHandle)member.Parent,
                HandleKind.TypeSpecification => GenericDefinition(md, (TypeSpecificationHandle)member.Parent),
                _ => null,
            };
            if (parent is not { } owner || Resolve(owner) is not { } definitions) continue;
            string name = md.GetString(member.Name);
            bool method = member.GetKind() == MemberReferenceKind.Method;
            foreach (var (targetMd, type) in definitions)
            {
                bool visible = method
                    ? type.GetMethods().Select(targetMd.GetMethodDefinition).Any(m => targetMd.GetString(m.Name) == name && Exposed(m.Attributes))
                    : type.GetFields().Select(targetMd.GetFieldDefinition).Any(f => targetMd.GetString(f.Name) == name && Exposed(f.Attributes));
                if (!visible) violations.Add($"{label} 引用了 {FullName(targetMd, type)} 上不可见的成员 {name}");
            }
        }
    }

    /// <summary>方法引用的泛型参数个数。</summary>
    private static int GenericArity(MetadataReader md, MemberReference member)
    {
        var blob = md.GetBlobReader(member.Signature);
        var header = blob.ReadSignatureHeader();
        return header.IsGeneric ? blob.ReadCompressedInteger() : 0;
    }

    /// <summary>泛型实例的定义（若它是一个类型引用）。</summary>
    private static TypeReferenceHandle? GenericDefinition(MetadataReader md, TypeSpecificationHandle handle)
    {
        var blob = md.GetBlobReader(md.GetTypeSpecification(handle).Signature);
        if (blob.ReadSignatureTypeCode() != SignatureTypeCode.GenericTypeInstance) return null;
        blob.ReadCompressedInteger();
        var definition = blob.ReadTypeHandle();
        return definition.Kind == HandleKind.TypeReference ? (TypeReferenceHandle)definition : null;
    }

    /// <summary>方法返回类型的全名；泛型实例取它的定义。</summary>
    private static string ReturnTypeName(MetadataReader md, MethodDefinition method) =>
        method.DecodeSignature(new Names(md), null).ReturnType;

    /// <summary>把签名里的类型写成全名，只用于比较返回类型。</summary>
    private sealed class Names(MetadataReader md) : ISignatureTypeProvider<string, object?>
    {
        public string GetPrimitiveType(PrimitiveTypeCode typeCode) => "System." + typeCode;
        public string GetTypeFromDefinition(MetadataReader reader, TypeDefinitionHandle handle, byte rawTypeKind) => FullName(md, md.GetTypeDefinition(handle));
        public string GetTypeFromReference(MetadataReader reader, TypeReferenceHandle handle, byte rawTypeKind) => FullName(md, md.GetTypeReference(handle));
        public string GetTypeFromSpecification(MetadataReader reader, object? context, TypeSpecificationHandle handle, byte rawTypeKind) =>
            md.GetTypeSpecification(handle).DecodeSignature(this, context);
        public string GetGenericInstantiation(string genericType, ImmutableArray<string> typeArguments) => genericType;
        public string GetSZArrayType(string elementType) => elementType + "[]";
        public string GetArrayType(string elementType, ArrayShape shape) => elementType + "[,]";
        public string GetByReferenceType(string elementType) => elementType + "&";
        public string GetPointerType(string elementType) => elementType + "*";
        public string GetFunctionPointerType(MethodSignature<string> signature) => "fnptr";
        public string GetGenericMethodParameter(object? context, int index) => "!!" + index;
        public string GetGenericTypeParameter(object? context, int index) => "!" + index;
        public string GetModifiedType(string modifier, string unmodifiedType, bool isRequired) => unmodifiedType;
        public string GetPinnedType(string elementType) => elementType;
    }

    private static HashSet<string> Closure(Layer layer)
    {
        var result = new HashSet<string>();
        var work = new Stack<string>(layer.MayReference);
        while (work.Count > 0)
        {
            string name = work.Pop();
            if (!result.Add(name)) continue;
            foreach (string next in Array.Find(layers, l => l.Name == name)?.MayReference ?? []) work.Push(next);
        }
        return result;
    }

    private static string AttributeName(MetadataReader md, CustomAttribute attribute)
    {
        EntityHandle type = attribute.Constructor.Kind switch
        {
            HandleKind.MemberReference => md.GetMemberReference((MemberReferenceHandle)attribute.Constructor).Parent,
            HandleKind.MethodDefinition => md.GetMethodDefinition((MethodDefinitionHandle)attribute.Constructor).GetDeclaringType(),
            _ => default,
        };
        if (type.Kind == HandleKind.TypeReference) return FullName(md, md.GetTypeReference((TypeReferenceHandle)type));
        if (type.Kind == HandleKind.TypeDefinition) return FullName(md, md.GetTypeDefinition((TypeDefinitionHandle)type));
        return "";
    }
}
