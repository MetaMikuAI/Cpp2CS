using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Mono.Cecil;
namespace Cpp2CS.Tests.Execution;

/// <summary>检查用的真实 C# 编译产物；不经恢复路径或输出器。</summary>
internal sealed class CompiledSource : IDisposable
{
    private readonly MemoryStream image = new();
    private readonly DefaultAssemblyResolver resolver = new();
    public ModuleDefinition Module { get; }
    public CompiledSource(string source)
    {
        var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator).Select(p => MetadataReference.CreateFromFile(p));
        var compilation = CSharpCompilation.Create("ExecutionFixture", [CSharpSyntaxTree.ParseText(source)], references,
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, optimizationLevel: OptimizationLevel.Release, allowUnsafe: true));
        var result = compilation.Emit(image);
        if (!result.Success) throw new InvalidDataException(string.Join(Environment.NewLine, result.Diagnostics));
        image.Position = 0;
        resolver.AddSearchDirectory(Path.GetDirectoryName(typeof(object).Assembly.Location)!);
        Module = ModuleDefinition.ReadModule(image, new ReaderParameters { AssemblyResolver = resolver });
    }
    public MethodDefinition Method(string type, string name) => Module.GetType(type).Methods.Single(m => m.Name == name);
    public void Dispose() { Module.Dispose(); resolver.Dispose(); image.Dispose(); }
}
