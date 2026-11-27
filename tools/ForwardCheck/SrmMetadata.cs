using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Facts;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>一个已打开的程序集。</summary>
internal sealed class Module : IDisposable
{
    public string Image => Md.GetString(Md.GetModuleDefinition().Name);
    public PEReader Pe { get; }
    public MetadataReader Md { get; }
    private Dictionary<(string Namespace, string Name), TypeDefinitionHandle>? topLevel;

    public Module(string path)
    {
        Pe = new PEReader(File.OpenRead(path));
        Md = Pe.GetMetadataReader();
    }

    public TypeDefinitionHandle? FindTopLevel(string @namespace, string name)
    {
        if (topLevel is null)
        {
            topLevel = [];
            foreach (var handle in Md.TypeDefinitions)
            {
                var definition = Md.GetTypeDefinition(handle);
                if (definition.GetDeclaringType().IsNil)
                    topLevel[(Md.GetString(definition.Namespace), Md.GetString(definition.Name))] = handle;
            }
        }
        return topLevel.TryGetValue((@namespace, name), out var found) ? found : null;
    }

    public void Dispose() => Pe.Dispose();
}

internal sealed partial class SrmMetadata : IDisposable
{
    private readonly string directory;
    public ModelMetadata Facts { get; }
    private readonly Dictionary<string, Module?> modules = new(StringComparer.OrdinalIgnoreCase);
    private readonly Dictionary<(Module, TypeReferenceHandle), (Module, TypeDefinitionHandle)> resolvedReferences = [];
    private readonly Dictionary<(string Image, int Token), int> types = [], methods = [], fields = [];
    private Dictionary<int, (Module Module, TypeDefinitionHandle Handle)>? generatedDefinitions;

    public SrmMetadata(string directory, ModelMetadata facts, Cpp2CS.Model.AssemblyMetadata? generated = null)
    {
        this.directory = directory;
        Facts = facts;
        if (generated != null)
        {
            IndexGenerated(generated);
            return;
        }
        foreach (var img in facts.Model.Images)
        {
            string image = img.Name;
            for (int i = img.FirstType; i < img.FirstType + img.TypeCount; i++)
            {
                var d = facts.Model.Types[i];
                types.Add((image, (int)d.Token), i);
                for (int k = d.FirstField; k < d.FirstField + d.FieldCount; k++) fields.Add((image, (int)facts.Model.Fields[k].Token), k);
                for (int k = d.FirstMethod; k < d.FirstMethod + d.MethodCount; k++) methods.Add((image, (int)facts.Model.Methods[k].Token), k);
            }
        }
    }

    public void Dispose()
    {
        foreach (var module in modules.Values) module?.Dispose();
    }

    public Module? Load(string assembly)
    {
        var definition = Facts.Model.Assemblies.FirstOrDefault(a => string.Equals(a.Name, assembly, StringComparison.OrdinalIgnoreCase));
        return LoadImage(definition == null ? assembly + ".dll" : Facts.Model.Images[definition.Image].Name);
    }

    internal Module? LoadImage(string image)
    {
        if (Path.GetFileName(image) != image) throw Unresolved($"模块名不是文件名 {image}");
        if (modules.TryGetValue(image, out var known)) return known;
        string path = Path.Combine(directory, image);
        var module = File.Exists(path) ? new Module(path) : null;
        modules[image] = module;
        return module;
    }

    private static ExpansionException Unresolved(string what) => new("元数据解析不了", what);

    // II.6.2：AssemblyRef 的版本、区域性与公钥标记也属于解析范围。
    private Module? AssemblyScope(Module from, AssemblyReferenceHandle handle)
    {
        var reference = from.Md.GetAssemblyReference(handle);
        var expected = reference.GetAssemblyName();
        var target = Load(expected.Name!);
        if (target == null) return null;
        var actual = target.Md.GetAssemblyDefinition().GetAssemblyName();
        if (!string.Equals(expected.Name, actual.Name, StringComparison.OrdinalIgnoreCase) ||
            expected.Version != actual.Version || !string.Equals(expected.CultureName, actual.CultureName, StringComparison.OrdinalIgnoreCase) ||
            !(expected.GetPublicKeyToken() ?? []).SequenceEqual(actual.GetPublicKeyToken() ?? []))
            throw Unresolved($"程序集引用 {expected.FullName} 与 {actual.FullName} 不匹配");
        return target;
    }

    private (Module Module, TypeDefinitionHandle Handle) Resolve(Module module, TypeReferenceHandle handle)
    {
        if (resolvedReferences.TryGetValue((module, handle), out var result)) return result;
        return resolvedReferences[(module, handle)] = ResolveReference(module, handle);
    }

    private (Module Module, TypeDefinitionHandle Handle) ResolveReference(Module module, TypeReferenceHandle handle)
    {
        var reference = module.Md.GetTypeReference(handle);
        string @namespace = module.Md.GetString(reference.Namespace), name = module.Md.GetString(reference.Name);
        var scope = reference.ResolutionScope;
        if (scope.Kind == HandleKind.TypeReference)
        {
            var (outerModule, outer) = Resolve(module, (TypeReferenceHandle)scope);
            foreach (var nested in outerModule.Md.GetTypeDefinition(outer).GetNestedTypes())
                if (outerModule.Md.GetString(outerModule.Md.GetTypeDefinition(nested).Name) == name) return (outerModule, nested);
            throw Unresolved($"嵌套类型 {name}");
        }
        Module? target = scope.Kind switch
        {
            HandleKind.AssemblyReference => AssemblyScope(module, (AssemblyReferenceHandle)scope),
            HandleKind.ModuleDefinition => module,
            HandleKind.ModuleReference => LoadImage(module.Md.GetString(module.Md.GetModuleReference((ModuleReferenceHandle)scope).Name)),
            _ => null,
        };
        var visited = new HashSet<Module>();
        while (target != null && visited.Add(target))
        {
            if (target.FindTopLevel(@namespace, name) is { } found) return (target, found);
            // 类型转发。
            Module? next = null;
            foreach (var exportedHandle in target.Md.ExportedTypes)
            {
                var exported = target.Md.GetExportedType(exportedHandle);
                if (target.Md.GetString(exported.Name) != name || target.Md.GetString(exported.Namespace) != @namespace) continue;
                if (exported.IsForwarder && exported.Implementation.Kind == HandleKind.AssemblyReference)
                    next = AssemblyScope(target, (AssemblyReferenceHandle)exported.Implementation);
                else if (exported.Implementation.Kind == HandleKind.AssemblyFile)
                {
                    var file = target.Md.GetAssemblyFile((AssemblyFileHandle)exported.Implementation);
                    if (file.ContainsMetadata) next = LoadImage(target.Md.GetString(file.Name));
                }
                if (next != null) break;
            }
            target = next;
        }
        throw Unresolved($"类型 {@namespace}.{name}");
    }

}
