using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json;
using Il2CppDumper;

namespace Il2CppDumper
{
    internal static class Resource1
    {
        internal static byte[] Il2CppDummyDll
        {
            get
            {
                using var source = typeof(Resource1).Assembly.GetManifestResourceStream("Il2CppDummyDll");
                using var output = new MemoryStream();
                source.CopyTo(output);
                return output.ToArray();
            }
        }
    }
}

namespace Cpp2CS.Input
{
    public static class RawImport
    {
        // 缓存版本标识导入格式及对应的 Dumper 版本。
        public const string Version = "2-4741d46";

        public static int Run(string binary, string metadataPath, string output)
        {
            var metadata = new Metadata(new MemoryStream(File.ReadAllBytes(metadataPath)));
            var image = new Elf64(new MemoryStream(File.ReadAllBytes(binary)));
            image.SetProperties(metadata.Version, metadata.metadataUsagesCount);
            if (!image.PlusSearch(metadata.methodDefs.Count(m => m.methodIndex >= 0), metadata.typeDefs.Length, metadata.imageDefs.Length)
                && !image.Search() && !image.SymbolSearch())
            {
                Console.Error.WriteLine("无法自动定位 IL2CPP 注册表；不支持此输入。");
                return 2;
            }
            if (image.IsDumped)
            {
                Console.Error.WriteLine("当前入口只支持磁盘 ELF，不支持内存转储。");
                return 2;
            }
            var executor = new Il2CppExecutor(metadata, image);
            new StructGenerator(executor).WriteScript(output + Path.DirectorySeparatorChar);
            var dllDirectory = Path.Combine(output, "DummyDll");
            Directory.CreateDirectory(dllDirectory);
            var owners = new Dictionary<ulong, HashSet<string>>();
            var typeOwners = new string[metadata.typeDefs.Length];
            foreach (var definition in metadata.imageDefs)
            {
                var name = metadata.GetStringFromIndex(definition.nameIndex);
                for (var index = definition.typeStart; index < definition.typeStart + definition.typeCount; index++)
                    typeOwners[index] = name;
            }
            void AddOwner(ulong pointer, int declaringType)
            {
                if (pointer == 0) return;
                var address = image.GetRVA(pointer);
                if (!owners.TryGetValue(address, out var names)) owners.Add(address, names = new());
                names.Add(typeOwners[declaringType]);
            }
            foreach (var method in metadata.methodDefs)
                AddOwner(image.GetMethodPointer(typeOwners[method.declaringType], method), method.declaringType);
            foreach (var instance in image.methodSpecGenericMethodPointers)
                AddOwner(instance.Value, metadata.methodDefs[instance.Key.methodDefinitionIndex].declaringType);
            foreach (var assembly in new DummyAssemblyGenerator(executor, true).Assemblies)
            {
                var name = assembly.MainModule.Name;
                if (name != Path.GetFileName(name) || name.Contains('\\') || name.Contains('/') || name.Contains(':'))
                    throw new InvalidDataException("程序集名称包含目录分隔符");
                assembly.Write(Path.Combine(dllDirectory, name));
            }
            // 最后写完成标记；中断或失败的目录不会被当作有效缓存。
            File.WriteAllText(Path.Combine(output, "assemblies.json"), JsonSerializer.Serialize(owners.ToDictionary(p => p.Key, p => p.Value.OrderBy(n => n).ToArray())));
            return 0;
        }
    }
}
