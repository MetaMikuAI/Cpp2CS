using System.Diagnostics;
using Cpp2CS.Output;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;

namespace Cpp2CS.Tests;

/// <summary>
/// 把 recover 写出的程序集整体反编译成 C#，以原程序集名对其余骨架程序集编译。
/// 只有含已写出方法体的类型（emitted.tsv）计入断言：这些类型的源码文件必须 0 错误；其余文件的错误只统计，
/// 它们全是骨架（裁剪后的核心库、特性实参等环境问题），与恢复无关。
/// </summary>
internal static class CompileCheck
{
    [Command("compile", "反编译并用 Roslyn 编译：含已恢复方法的类型 0 错误", Arguments = "<recover 输出目录>")]
    public static int Run(string directory) => Check(directory, "assemblies");

    [Command("compile-source", "检查经过 async/源码整理后的程序集，目标与 compile 相同", Arguments = "<recover 输出目录>")]
    public static int Source(string directory) => Check(directory, "assemblies-src");

    private static int Check(string directory, string assemblyDirectory)
    {
        var assemblies = Path.Combine(directory, assemblyDirectory);
        var emitted = File.ReadAllLines(Path.Combine(directory, "emitted.tsv")).Select(l => l.Split('\t')).ToArray();
        var a = new Assertions();
        foreach (var group in emitted.GroupBy(f => f[0]))
        {
            var targets = group.Select(f => (Namespace: f[1], Name: f[2])).ToHashSet();
            var errors = Compile(assemblies, Path.GetFileNameWithoutExtension(group.Key), targets, out var targetFiles);
            var inTargets = errors.Where(e => e.Target).Select(e => e.Diagnostic).ToArray();
            Console.WriteLine($"  {group.Key}: 目标类型文件 {targetFiles}（方法 {group.Count()}），目标内错误 {inTargets.Length}，其余文件错误 {errors.Count - inTargets.Length}");
            foreach (var code in inTargets.GroupBy(d => d.Id).OrderByDescending(g => g.Count()).Take(12))
            {
                var sample = code.First();
                Console.WriteLine($"    {code.Key,-8} {code.Count(),5}  {sample.Location.SourceTree?.FilePath}{sample.Location.GetLineSpan().StartLinePosition}: {sample.GetMessage()}");
            }
            a.Equal(0, inTargets.Length, $"{group.Key} 中含已恢复方法的类型的编译错误");
        }
        return a.Finish(assemblyDirectory == "assemblies" ? "compile" : "compile-source");
    }

    private static List<(Diagnostic Diagnostic, bool Target)> Compile(string directory, string assemblyName, HashSet<(string, string)> targets, out int targetFiles)
    {
        var watch = Stopwatch.StartNew();
        var main = Path.Combine(directory, assemblyName + ".dll");
        var sources = Decompilation.Decompile(main, directory, _ => true, assemblyAttributes: true, recoveringBodies: true);
        var decompiled = watch.Elapsed;
        var parseOptions = new CSharpParseOptions(LanguageVersion.Preview);
        var trees = new SyntaxTree[sources.Count];
        var isTarget = new HashSet<string>();
        for (var i = 0; i < sources.Count; i++)
        {
            var path = $"{i}:{sources[i].TypeName ?? "AssemblyInfo"}";
            if (sources[i].TypeName is { } name && targets.Contains((sources[i].Namespace, TopName(name, sources[i].Namespace)))) isTarget.Add(path);
        }
        Parallel.For(0, sources.Count, i => trees[i] = CSharpSyntaxTree.ParseText(sources[i].Source, parseOptions, path: $"{i}:{sources[i].TypeName ?? "AssemblyInfo"}"));
        targetFiles = isTarget.Count;
        var references = Directory.GetFiles(directory, "*.dll")
            .Where(p => Path.GetFileNameWithoutExtension(p) != assemblyName)
            .Select(p => MetadataReference.CreateFromFile(p))
            .ToArray();
        var compilation = CSharpCompilation.Create(assemblyName, trees, references, new CSharpCompilationOptions(
            OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true, nullableContextOptions: NullableContextOptions.Disable));
        var shims = Shims.Where(shim => compilation.GetTypeByMetadataName(shim.MetadataName) is null).ToArray();
        if (shims.Length > 0)
            compilation = compilation.AddSyntaxTrees(shims.Select(shim => CSharpSyntaxTree.ParseText(shim.Source, parseOptions, path: "<shim>" + shim.MetadataName)));
        var errors = compilation.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error)
            .Select(d => (d, d.Location.SourceTree?.FilePath is { } p && isTarget.Contains(p))).ToList();
        Console.WriteLine($"  {assemblyName}: 反编译 {decompiled.TotalSeconds:F0} s，编译 {(watch.Elapsed - decompiled).TotalSeconds:F0} s，文件 {sources.Count}");
        return errors;
    }

    /// <summary>反编译结果的 TypeName 是 ReflectionName（Namespace.Name`N）；取不带命名空间与泛型元数的顶层名。</summary>
    private static string TopName(string reflectionName, string ns)
    {
        var name = ns.Length > 0 && reflectionName.StartsWith(ns + ".", StringComparison.Ordinal) ? reflectionName[(ns.Length + 1)..] : reflectionName;
        return name.IndexOf('`') is var tick and >= 0 ? name[..tick] : name;
    }

    /// <summary>编译环境补丁（不属于输出）：骨架 mscorlib 来自裁剪后的元数据，缺少 ILSpy 会合成的伪特性类型等。只在骨架里没有时加入。</summary>
    private static readonly (string MetadataName, string Source)[] Shims =
    [
        ("System.Runtime.InteropServices.LayoutKind", """
            namespace System.Runtime.InteropServices { public enum LayoutKind { Sequential = 0, Explicit = 2, Auto = 3 } }
            """),
        ("System.Runtime.InteropServices.StructLayoutAttribute", """
            namespace System.Runtime.InteropServices
            {
                public sealed class StructLayoutAttribute : System.Attribute
                {
                    public StructLayoutAttribute(LayoutKind layoutKind) { }
                    public StructLayoutAttribute(short layoutKind) { }
                    public int Pack;
                    public int Size;
                    public CharSet CharSet;
                }
            }
            """),
        ("System.Runtime.CompilerServices.MethodImplOptions", """
            namespace System.Runtime.CompilerServices { [System.Flags] public enum MethodImplOptions { NoInlining = 8, ForwardRef = 16, Synchronized = 32, NoOptimization = 64, PreserveSig = 128, AggressiveInlining = 256, InternalCall = 4096 } }
            """),
        ("System.Runtime.CompilerServices.MethodImplAttribute", """
            namespace System.Runtime.CompilerServices
            {
                public sealed class MethodImplAttribute : System.Attribute
                {
                    public MethodImplAttribute() { }
                    public MethodImplAttribute(MethodImplOptions methodImplOptions) { }
                    public MethodImplAttribute(short value) { }
                }
            }
            """),
        ("System.Runtime.InteropServices.FieldOffsetAttribute", """
            namespace System.Runtime.InteropServices { public sealed class FieldOffsetAttribute : System.Attribute { public FieldOffsetAttribute(int offset) { } } }
            """),
    ];
}
