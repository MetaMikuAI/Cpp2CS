using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Extensions.Decompile;

public static class FullDecompilation
{
    public static IReadOnlyList<SourceFile> Decompile(string assemblyPath, string searchDirectory,
        Func<ITypeDefinition, bool> include, bool assemblyAttributes, bool recoveringBodies = false, bool groupByName = false) =>
        Decompilation.Decompile(assemblyPath, searchDirectory, include, assemblyAttributes, recoveringBodies, groupByName,
            ReadabilityTransforms.Instance);
}
