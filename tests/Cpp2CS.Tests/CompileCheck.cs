using System.Diagnostics;
using Cpp2CS.Output;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;

namespace Cpp2CS.Tests;

/// <summary>
/// 编译检查：骨架写出后，把 Assembly-CSharp 全部反编译成 C#，以 "Assembly-CSharp" 为名
/// 对其他骨架程序集（骨架 mscorlib 作为核心库）编译，统计错误。回归命名空间单列。
/// </summary>
internal static class CompileCheck
{
    public static int Run(string binary, string metadata, string directory, string? regressionNamespaces)
    {
        var watch = Stopwatch.StartNew();
        var model = ModelCheck.Load(binary, metadata);
        Console.WriteLine($"模型      {watch.ElapsedMilliseconds} ms");
        watch.Restart();
        var skeleton = new Skeleton(model);
        skeleton.Write(directory);
        Console.WriteLine($"骨架      {watch.ElapsedMilliseconds} ms  程序集 {skeleton.Assemblies.Count}");

        return Saved(directory, regressionNamespaces);
    }

    /// <summary>只验证已写出的程序集，不重新生成骨架覆盖恢复结果。</summary>
    public static int Saved(string directory, string? regressionNamespaces, string assemblyName = "Assembly-CSharp")
    {
        var watch = Stopwatch.StartNew();
        var main = Path.Combine(directory, assemblyName + ".dll");
        var sources = Decompilation.Decompile(main, directory, _ => true, assemblyAttributes: true, recoveringBodies: true);
        Console.WriteLine($"反编译    {watch.ElapsedMilliseconds} ms  文件 {sources.Count}  行 {sources.Sum(s => s.Source.Count(c => c == '\n'))}");
        WriteSources(Path.Combine(directory, "src-" + assemblyName), sources);

        watch.Restart();
        var regression = regressionNamespaces?.Split(',').ToHashSet() ?? [];
        var parseOptions = new CSharpParseOptions(LanguageVersion.Preview);
        var trees = new SyntaxTree[sources.Count];
        Parallel.For(0, sources.Count, i => trees[i] = CSharpSyntaxTree.ParseText(sources[i].Source, parseOptions, path: sources[i].TypeName ?? "AssemblyInfo"));
        var references = Directory.GetFiles(directory, "*.dll")
            .Where(p => Path.GetFileNameWithoutExtension(p) != assemblyName)
            .Select(p => MetadataReference.CreateFromFile(p))
            .ToArray();
        var compilation = CSharpCompilation.Create(assemblyName, trees, references, new CSharpCompilationOptions(
            OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true, nullableContextOptions: NullableContextOptions.Disable));
        var shims = Shims.Where(shim => compilation.GetTypeByMetadataName(shim.MetadataName) is null).ToArray();
        if (shims.Length > 0)
        {
            Console.WriteLine($"环境补丁  {string.Join(" ", shims.Select(s => s.MetadataName))}");
            compilation = compilation.AddSyntaxTrees(shims.Select(shim => CSharpSyntaxTree.ParseText(shim.Source, parseOptions, path: "<shim>" + shim.MetadataName)));
        }
        var errors = compilation.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error).ToArray();
        Console.WriteLine($"编译      {watch.ElapsedMilliseconds} ms");

        var namespaceOf = sources.Where(s => s.TypeName is not null).ToDictionary(s => s.TypeName!, s => s.Namespace);
        bool Included(string ns) => regression.Any(root => ns == root || ns.StartsWith(root + ".", StringComparison.Ordinal));
        bool InRegression(Diagnostic d) => d.Location.SourceTree?.FilePath is { } path && namespaceOf.TryGetValue(path, out var ns) && Included(ns);
        var regressionFiles = sources.Count(s => s.TypeName is not null && Included(s.Namespace));
        Console.WriteLine($"错误      {errors.Length}  涉及文件 {errors.Select(d => d.Location.SourceTree?.FilePath).Distinct().Count()}");
        Console.WriteLine($"回归错误  {errors.Count(InRegression)}  回归文件 {regressionFiles}  有错文件 {errors.Where(InRegression).Select(d => d.Location.SourceTree!.FilePath).Distinct().Count()}");
        foreach (var group in errors.GroupBy(d => d.Id).OrderByDescending(g => g.Count()).Take(25))
        {
            var sample = group.First();
            Console.WriteLine($"  {group.Key,-8} {group.Count(),6}  {sample.Location.SourceTree?.FilePath}{sample.Location.GetLineSpan().StartLinePosition}: {sample.GetMessage()}");
        }
        return errors.Length == 0 ? 0 : 1;
    }

    /// <summary>
    /// 编译环境补丁（不属于输出）：骨架 mscorlib 来自裁剪后的元数据，缺少 ILSpy 会合成的伪特性类型等。
    /// 只在骨架里没有时加入编译，使这类缺失不计为恢复错误。
    /// </summary>
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

    /// <summary>源码写到目录供查看；文件系统大小写不敏感，同名（如 Sekai.API 与 Sekai.Api 下的同名类型）加序号区分。</summary>
    private static void WriteSources(string directory, IReadOnlyList<SourceFile> sources)
    {
        if (Directory.Exists(directory)) Directory.Delete(directory, true);
        Directory.CreateDirectory(directory);
        var used = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        var invalid = Path.GetInvalidFileNameChars();
        foreach (var source in sources)
        {
            var stem = new string((source.TypeName ?? "AssemblyInfo").Select(c => invalid.Contains(c) ? '_' : c).ToArray());
            var name = stem;
            for (var k = 2; !used.Add(name); k++) name = $"{stem}~{k}";
            File.WriteAllText(Path.Combine(directory, name + ".cs"), source.Source);
        }
    }
}
