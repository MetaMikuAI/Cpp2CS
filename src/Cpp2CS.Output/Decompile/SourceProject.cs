using System.Xml.Linq;
using Mono.Cecil;

namespace Cpp2CS.Output;

/// <summary>按程序集、命名空间和类型导出源码，泛型同名类型合并到同一文件。</summary>
public static class SourceProject
{
    public static int Write(string assemblyPath, string searchDirectory, string output,
        Func<ICSharpCode.Decompiler.TypeSystem.ITypeDefinition, bool> include, IDecompileTransformProvider? transforms = null, Func<string>? stubs = null)
    {
        using var module = ModuleDefinition.ReadModule(assemblyPath);
        var directory = Path.Combine(output, FileName(Path.GetFileName(assemblyPath)));
        Directory.CreateDirectory(directory);
        var references = Path.Combine(directory, "references");
        SourceReferences.Prepare(assemblyPath, searchDirectory, references);
        var paths = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        var count = 0;
        foreach (var source in Decompilation.Decompile(Path.Combine(references, Path.GetFileName(assemblyPath)), references, include, true, groupByName: true, transforms: transforms, stubs: stubs))
        {
            var relative = source.TypeName is null ? Path.Combine("Properties", "AssemblyInfo.cs")
                : Path.Combine(source.Namespace.Length == 0 ? "" : FileName(source.Namespace),
                    FileName(source.Namespace.Length == 0 ? source.TypeName : source.TypeName[(source.Namespace.Length + 1)..]) + ".cs");
            if (!paths.Add(relative)) throw new InvalidDataException($"源码路径重复：{relative}");
            var path = Path.Combine(directory, relative);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, source.Source);
            if (source.TypeName is not null) count++;
        }
        if (StrippedAttributes(searchDirectory) is { Length: > 0 } stripped)
        {
            var path = Path.Combine(directory, "Properties", "StrippedAttributes.cs");
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, stripped);
        }
        File.WriteAllText(Path.Combine(directory, "Properties", "AwaiterExtensions.cs"), AwaiterExtensions);
        var project = new XElement("Project", new XAttribute("Sdk", "Microsoft.NET.Sdk"),
            new XElement("PropertyGroup",
                new XElement("AssemblyName", module.Assembly.Name.Name),
                new XElement("TargetFramework", "net40"),
                new XElement("GenerateAssemblyInfo", false),
                new XElement("GenerateTargetFrameworkAttribute", false),
                new XElement("LangVersion", Decompilation.TargetLanguageVersion),
                new XElement("AllowUnsafeBlocks", true),
                new XElement("CheckForOverflowUnderflow", false),
                // 工程可能放在别的工程目录下，不继承那里的编译设置。
                new XElement("Nullable", "disable"),
                new XElement("ImplicitUsings", "disable"),
                new XElement("TreatWarningsAsErrors", false),
                new XElement("WarningLevel", 0),
                // 引用的程序集可能标了更高的目标框架（第三方库），它们都是骨架，不用按框架筛选。
                new XElement("ResolveAssemblyReferenceIgnoreTargetFrameworkAttributeVersionMismatch", true)),
            // 引用目录里的全部程序集：C# 还要解析间接引用（基类、约束所在的程序集）。
            new XElement("ItemGroup", Directory.GetFiles(references, "*.dll").OrderBy(f => f, StringComparer.Ordinal)
                .Where(f => !string.Equals(Path.GetFileName(f), Path.GetFileName(assemblyPath), StringComparison.OrdinalIgnoreCase))
                .Select(file => new XElement("Reference", new XAttribute("Include", Path.GetFileNameWithoutExtension(file)),
                    new XElement("HintPath", Path.Combine("references", Path.GetFileName(file)))))));
        new XDocument(project).Save(Path.Combine(directory, FileName(module.Assembly.Name.Name) + ".csproj"));
        return count;
    }

    /// <summary>
    /// 内联的 GetAwaiter 把等待器直接交给 await，等待器自身没有 GetAwaiter。这个扩展把它原样返回，
    /// await 仍按原来的等待器读 IsCompleted、GetResult。
    /// </summary>
    private const string AwaiterExtensions = """
        internal static class AwaiterExtensions
        {
            public static TAwaiter GetAwaiter<TAwaiter>(this TAwaiter awaiter) where TAwaiter : struct, System.Runtime.CompilerServices.INotifyCompletion => awaiter;
        }

        """;

    private static readonly (string Namespace, string Name, string Declaration)[] PseudoAttributes =
    [
        ("System.Runtime.InteropServices", "LayoutKind", "internal enum LayoutKind { Sequential = 0, Explicit = 2, Auto = 3 }"),
        ("System.Runtime.InteropServices", "CharSet", "internal enum CharSet { None = 1, Ansi = 2, Unicode = 3, Auto = 4 }"),
        ("System.Runtime.InteropServices", "StructLayoutAttribute", "internal sealed class StructLayoutAttribute : global::System.Attribute { public StructLayoutAttribute(LayoutKind layoutKind) { } public int Pack; public int Size; public CharSet CharSet; }"),
        ("System.Runtime.InteropServices", "FieldOffsetAttribute", "internal sealed class FieldOffsetAttribute : global::System.Attribute { public FieldOffsetAttribute(int offset) { } }"),
        ("System.Runtime.CompilerServices", "MethodImplOptions", "internal enum MethodImplOptions { Unmanaged = 4, NoInlining = 8, ForwardRef = 16, Synchronized = 32, NoOptimization = 64, PreserveSig = 128, AggressiveInlining = 256, AggressiveOptimization = 512, InternalCall = 4096 }"),
        ("System.Runtime.CompilerServices", "MethodImplAttribute", "internal sealed class MethodImplAttribute : global::System.Attribute { public MethodImplAttribute() { } public MethodImplAttribute(short value) { } public MethodImplAttribute(MethodImplOptions methodImplOptions) { } }"),
    ];

    /// <summary>
    /// IL2CPP 裁掉了只对运行时有意义的伪特性类型（类型布局、字段偏移、方法实现标志），反编译器仍按元数据的标志写出它们。
    /// 核心库里没有时在工程内声明，只为源码能编译，不影响方法体。
    /// </summary>
    private static string StrippedAttributes(string searchDirectory)
    {
        var corlib = Path.Combine(searchDirectory, "mscorlib.dll");
        if (!File.Exists(corlib)) return "";
        using var module = ModuleDefinition.ReadModule(corlib);
        var missing = PseudoAttributes.Where(a => module.GetType(a.Namespace, a.Name) is null).GroupBy(a => a.Namespace);
        return string.Concat(missing.Select(g => $"namespace {g.Key}\n{{\n{string.Concat(g.Select(a => $"    {a.Declaration}\n"))}}}\n"));
    }

    private static string FileName(string name)
    {
        var invalid = Path.GetInvalidFileNameChars();
        var value = new string(name.Select(c => invalid.Contains(c) ? '_' : c).ToArray()).TrimEnd('.', ' ');
        if (value.Length == 0) return "_";
        var stem = value.Split('.')[0];
        return stem.Equals("CON", StringComparison.OrdinalIgnoreCase) || stem.Equals("PRN", StringComparison.OrdinalIgnoreCase)
            || stem.Equals("AUX", StringComparison.OrdinalIgnoreCase) || stem.Equals("NUL", StringComparison.OrdinalIgnoreCase)
            || stem.Length == 4 && (stem.StartsWith("COM", StringComparison.OrdinalIgnoreCase) || stem.StartsWith("LPT", StringComparison.OrdinalIgnoreCase))
                && stem[3] is >= '1' and <= '9' ? "_" + value : value;
    }
}
