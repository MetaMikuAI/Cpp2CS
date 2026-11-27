using System.Buffers.Binary;
using System.Reflection.Metadata.Ecma335;
using Cpp2CS.Facts;
using Cpp2CS.Input;

namespace Cpp2CS.Tools.ForwardCheck;

internal static class ModelInput
{
    public static SrmMetadata Load(string assemblies, Dictionary<string, string> options)
    {
        string directory = Path.Combine(Path.GetFullPath(assemblies), "..", "il2cppOutput", "build", "arm64-v8a");
        string binary = options.GetValueOrDefault("--binary", Path.Combine(directory, "libil2cpp.so"));
        string metadata = options.GetValueOrDefault("--metadata", Path.Combine(directory, "Data", "Metadata", "global-metadata.dat"));
        var input = Il2CppInput.Load(binary, metadata);
        return Open(assemblies, input, File.ReadAllBytes(binary));
    }

    public static SrmMetadata Open(string assemblies, Il2CppInput input, byte[] file)
        => new(assemblies, Facts(input, file, assemblies));

    public static ModelMetadata Facts(Il2CppInput input, byte[] file, string? assemblies = null)
    {
        // vm/GlobalMetadata.cpp::FromTypeDefinition：登记表中每个定义有一个含对象头的 instance_size。
        var model = input.Model;
        var elf = input.Elf;
        ulong table = elf.Pointer(checked(elf.ImageBase + input.Code.MetadataRegistration + 104));
        var layouts = new LayoutDefinition[model.Types.Count];
        foreach (var image in model.Images)
        {
            string? path = assemblies == null ? null : Path.Combine(assemblies, image.Name);
            using var module = File.Exists(path) ? new Module(path) : null;
            if (module != null && module.Image != image.Name) throw new InvalidDataException($"程序集映像名称不符 {image.Name}");
            for (int i = image.FirstType; i < image.FirstType + image.TypeCount; i++)
            {
                var type = model.Types[i];
                ulong sizeRecord = elf.Pointer(checked(table + (ulong)i * 8));
                int offset = elf.FileOffset(sizeRecord, 4) ?? throw new InvalidDataException($"类型 {i} 的大小登记不可读");
                int size = checked((int)BinaryPrimitives.ReadUInt32LittleEndian(file.AsSpan(offset, 4)));
                if (module != null)
                {
                    var h = (System.Reflection.Metadata.TypeDefinitionHandle)MetadataTokens.EntityHandle((int)type.Token);
                    var definition = module.Md.GetTypeDefinition(h);
                    if (module.Md.GetString(definition.Name) != type.Name || module.Md.GetString(definition.Namespace) != type.Namespace)
                        throw new InvalidDataException($"映像 {image.Name} 类型记号 0x{type.Token:x8} 与模型不匹配");
                }
                var layout = input.RuntimeLayout(i);
                layouts[i] = new(size, layout.Packing, layout.DefaultSize);
            }
        }
        var raw = Enumerable.Range(0, model.Fields.Count).Select(i => input.FieldOffsetSource(i)?.Value).ToArray();
        return new ModelMetadata(new EntityKeys(model), new(layouts, raw));
    }
}
