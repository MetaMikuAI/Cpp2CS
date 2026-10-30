using Cpp2CS.Facts;
using static Cpp2CS.Pipeline.RecoveryReport;

namespace Cpp2CS.Pipeline;

internal static class DecompileStage
{
    internal static int Write(RecoveryRequest request, ProgramFacts facts, string sourceAssemblies,
        IEnumerable<MethodRecoveryResult> emitted, IEnumerable<MethodRecoveryResult> partialEmitted,
        MethodRecoveryResult[] results, MethodDef[] methods, Action<string> Log)
    {
        var output = request.Output;
        var noSource = request.NoSource;
        var sourceLayout = request.SourceLayout;
        var list = request.Methods;
        var namespaces = request.Namespaces;
        var assembliesFilter = request.Assemblies;
        var all = request.All || assembliesFilter is not null;
        IDecompileTransformProvider? transforms = request.Profile == "full" ? ReadabilityTransforms.Instance : null;
        var sources = Path.Combine(output, "src");
        if (Directory.Exists(sources)) Directory.Delete(sources, true);
        Directory.CreateDirectory(sources);
        var invalid = Path.GetInvalidFileNameChars();
        var files = 0;
        var sourceTypes = sourceLayout == "project"
            ? facts.Model.Types.Where(t => t.DeclaringType is null && (list is not null ? methods.Any(m => Top(m.Owner) == t)
                : (all || InNamespaces(t, namespaces)) && (assembliesFilter is null || assembliesFilter.Contains(t.Assembly, StringComparer.Ordinal))))
            : emitted.Concat(partialEmitted).Concat(results.Where(r => r.Declaration is not null)).Select(r => Top(r.Method.Method.Owner)).Distinct();
        var sourceGroups = sourceTypes.GroupBy(t => t.Assembly).ToDictionary(g => g.Key, g => g.Select(t => (t.Namespace, t.SimpleName)).ToHashSet());
        var sourceAssemblyNames = sourceLayout == "project" && all
            ? facts.Model.Assemblies.Select(a => a.Name).Where(a => assembliesFilter is null || assembliesFilter.Contains(a, StringComparer.Ordinal))
            : sourceGroups.Keys.AsEnumerable();
        foreach (var assemblyName in sourceAssemblyNames.Where(_ => !noSource))
        {
            var wanted = sourceGroups.GetValueOrDefault(assemblyName) ?? [];
            if (sourceLayout == "project")
            {
                var count = SourceProject.Write(Path.Combine(sourceAssemblies, assemblyName), sourceAssemblies, sources,
                    t => all || wanted.Contains((t.Namespace, t.Name)), transforms);
                files += count;
                Log($"C# {assemblyName}：{count} 个类型文件，累计 {files}");
                continue;
            }
            foreach (var source in Decompilation.Decompile(Path.Combine(sourceAssemblies, assemblyName), sourceAssemblies,
                t => wanted.Contains((t.Namespace, t.Name)) || t.FullName == "Cpp2CS.NativeImports", false, recoveringBodies: true, transforms: transforms))
            {
                File.WriteAllText(Path.Combine(sources, new string((assemblyName + "_" + source.TypeName).Select(c => invalid.Contains(c) ? '_' : c).ToArray()) + ".cs"), source.Source);
                files++;
            }
        }
        return files;
    }
}
