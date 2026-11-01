using System.Xml.Linq;
using Mono.Cecil;

namespace Cpp2CS.Output;

/// <summary>按程序集、命名空间和类型导出源码，泛型同名类型合并到同一文件。</summary>
public static class SourceProject
{
    public static int Write(string assemblyPath, string searchDirectory, string output,
        Func<ICSharpCode.Decompiler.TypeSystem.ITypeDefinition, bool> include, IDecompileTransformProvider? transforms = null)
    {
        using var module = ModuleDefinition.ReadModule(assemblyPath);
        var directory = Path.Combine(output, FileName(Path.GetFileName(assemblyPath)));
        Directory.CreateDirectory(directory);
        var paths = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        var count = 0;
        foreach (var source in Decompilation.Decompile(assemblyPath, searchDirectory, include, true, recoveringBodies: true, groupByName: true, transforms: transforms))
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
        var project = new XElement("Project", new XAttribute("Sdk", "Microsoft.NET.Sdk"),
            new XElement("PropertyGroup",
                new XElement("AssemblyName", module.Assembly.Name.Name),
                new XElement("TargetFramework", "net40"),
                new XElement("GenerateAssemblyInfo", false),
                new XElement("GenerateTargetFrameworkAttribute", false),
                new XElement("LangVersion", "latest"),
                new XElement("AllowUnsafeBlocks", true),
                new XElement("CheckForOverflowUnderflow", false)),
            new XElement("ItemGroup", module.AssemblyReferences.Select(reference =>
                new XElement("Reference", new XAttribute("Include", reference.Name),
                    new XElement("HintPath", Path.GetRelativePath(directory, Path.GetFullPath(Path.Combine(searchDirectory, reference.Name + ".dll"))))))));
        new XDocument(project).Save(Path.Combine(directory, FileName(module.Assembly.Name.Name) + ".csproj"));
        return count;
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
