using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;

namespace Cpp2CS.Tools.ArchCheck;

/// <summary>
/// 架构检查：扫描构建出的程序集，核对设计“构造上的强制”一节里可以机检的条目。
/// 用法：ArchCheck 程序集或目录…
/// 规则写成数据。规则涉及的程序集或类型还不存在时，这条规则记为“尚无对象”，不算通过也不算违反。
/// </summary>
internal static class Program
{
    /// <summary>程序集的登记：可以直接引用的本项目程序集；是否可信；是否禁止反射。</summary>
    private sealed record Layer(string Name, string[] MayReference, bool Trusted, bool ForbidReflection);

    // 设计里“程序集”一表的依赖方向。可引用的范围按传递闭包计：能引用内核，就能引用内核公开的签名里出现的快照与规格。
    private static readonly Layer[] layers =
    [
        new("Cpp2CS.Model", [], Trusted: true, ForbidReflection: false),
        new("Cpp2CS.Snapshot", ["Cpp2CS.Model"], Trusted: true, ForbidReflection: false),
        new("Cpp2CS.Target", ["Cpp2CS.Snapshot"], Trusted: true, ForbidReflection: false),
        new("Cpp2CS.Spec", ["Cpp2CS.Snapshot"], Trusted: true, ForbidReflection: false),
        new("Cpp2CS.Kernel", ["Cpp2CS.Snapshot", "Cpp2CS.Spec"], Trusted: true, ForbidReflection: false),
        new("Cpp2CS.Facts", ["Cpp2CS.Kernel"], Trusted: true, ForbidReflection: false),
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

    private static readonly string[] reflectionNamespaces = ["System.Reflection", "System.Reflection.Emit", "System.Linq.Expressions"];
    private static readonly string[] reflectionTypes = ["System.Activator", "System.Runtime.CompilerServices.UnsafeAccessorAttribute"];
    private static readonly string[] reflectionMembers =
        ["GetMethod", "GetMethods", "GetField", "GetFields", "GetProperty", "GetProperties", "GetMember", "GetMembers", "GetConstructor", "GetConstructors", "InvokeMember"];

    // 现在还没有检查对象的条目，列出来以免被当成已经检查过。
    private static readonly string[] pending =
    [
        "入边与来源图的遍历接口不在只读查询面上（只读查询面尚未建立）",
        "下降的代码不引用走查与独立关系（下降尚未建立）",
    ];

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

        var seen = new HashSet<string>();
        var violations = new List<string>();
        var foundTypes = new HashSet<(string, string)>();
        int checks = 0;
        foreach (string file in files.Order(StringComparer.Ordinal))
        {
            using var pe = new PEReader(File.OpenRead(file));
            if (!pe.HasMetadata) continue;
            var md = pe.GetMetadataReader();
            string name = md.GetString(md.GetAssemblyDefinition().Name);
            if (!name.StartsWith("Cpp2CS.", StringComparison.Ordinal) || !seen.Add(name)) continue;

            // 一、依赖方向。
            var layer = Array.Find(layers, l => name == l.Name || name.StartsWith(l.Name + ".", StringComparison.Ordinal));
            checks++;
            if (layer is null) { violations.Add($"{name}：没有登记在程序集表里"); continue; }
            var allowed = Closure(layer);
            foreach (var handle in md.AssemblyReferences)
            {
                string reference = md.GetString(md.GetAssemblyReference(handle).Name);
                if (!reference.StartsWith("Cpp2CS.", StringComparison.Ordinal)) continue;
                checks++;
                if (!allowed.Any(a => reference == a || reference.StartsWith(a + ".", StringComparison.Ordinal)))
                    violations.Add($"{name} 引用了 {reference}，依赖方向不允许");
            }

            // 二、可信的程序集不向别的程序集开放内部成员。
            if (layer.Trusted)
            {
                checks++;
                foreach (var handle in md.GetAssemblyDefinition().GetCustomAttributes())
                    if (AttributeName(md, md.GetCustomAttribute(handle)) == "System.Runtime.CompilerServices.InternalsVisibleToAttribute")
                        violations.Add($"{name} 用 InternalsVisibleTo 开放了内部成员");
            }

            // 三、不可信的程序集不使用反射。
            if (layer.ForbidReflection)
            {
                checks++;
                foreach (var handle in md.TypeReferences)
                {
                    var reference = md.GetTypeReference(handle);
                    string @namespace = md.GetString(reference.Namespace), full = @namespace + "." + md.GetString(reference.Name);
                    if (reflectionNamespaces.Contains(@namespace) || reflectionTypes.Contains(full))
                        violations.Add($"{name} 引用了 {full}");
                }
                foreach (var handle in md.MemberReferences)
                {
                    var member = md.GetMemberReference(handle);
                    if (member.Parent.Kind != HandleKind.TypeReference) continue;
                    var parent = md.GetTypeReference((TypeReferenceHandle)member.Parent);
                    if (md.GetString(parent.Namespace) == "System" && md.GetString(parent.Name) == "Type" && reflectionMembers.Contains(md.GetString(member.Name)))
                        violations.Add($"{name} 调用了 System.Type::{md.GetString(member.Name)}");
                }
            }

            // 四、只能在内部构造的类型没有公开的构造函数。
            foreach (var handle in md.TypeDefinitions)
            {
                var type = md.GetTypeDefinition(handle);
                string full = md.GetString(type.Namespace) + "." + md.GetString(type.Name);
                if (!sealedConstruction.Contains((name, full))) continue;
                foundTypes.Add((name, full));
                checks++;
                foreach (var methodHandle in type.GetMethods())
                {
                    var method = md.GetMethodDefinition(methodHandle);
                    if (md.GetString(method.Name) == ".ctor" && (method.Attributes & MethodAttributes.MemberAccessMask) == MethodAttributes.Public)
                        violations.Add($"{full} 有公开的构造函数");
                }
            }
        }

        var absent = new List<string>(pending);
        foreach (var layer in layers)
            if (!seen.Any(s => s == layer.Name || s.StartsWith(layer.Name + ".", StringComparison.Ordinal))) absent.Add($"程序集 {layer.Name} 的各条规则（程序集尚未建立）");
        foreach (var item in sealedConstruction)
            if (seen.Contains(item.Assembly) && !foundTypes.Contains(item)) absent.Add($"{item.Type} 没有公开的构造函数（类型尚未建立）");

        Console.WriteLine($"架构检查：程序集 {seen.Count} 个（{string.Join("、", seen.Order(StringComparer.Ordinal))}），检查 {checks} 项，违反 {violations.Count} 项，尚无对象 {absent.Count} 项");
        foreach (string violation in violations) Console.WriteLine($"  违反：{violation}");
        foreach (string item in absent) Console.WriteLine($"  尚无对象：{item}");
        return violations.Count == 0 ? 0 : 1;
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
        if (type.Kind == HandleKind.TypeReference)
        {
            var reference = md.GetTypeReference((TypeReferenceHandle)type);
            return md.GetString(reference.Namespace) + "." + md.GetString(reference.Name);
        }
        if (type.Kind == HandleKind.TypeDefinition)
        {
            var definition = md.GetTypeDefinition((TypeDefinitionHandle)type);
            return md.GetString(definition.Namespace) + "." + md.GetString(definition.Name);
        }
        return "";
    }
}
