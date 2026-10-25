using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using ILVerify;

namespace Cpp2CS.Tests;

/// <summary>
/// ILVerify 检查：emitted.tsv 中的方法（按写出后的元数据标记找到，并核对名称）都要通过 ILVerify。
/// 以骨架 mscorlib 为系统模块，引用按简单名在同一目录中解析。
/// </summary>
internal static class IlVerifyCheck
{
    [Command("ilverify", "已写出的方法体全部通过 ILVerify", Arguments = "<recover 输出目录>")]
    public static int Run(string directory)
    {
        var assemblies = Path.Combine(directory, "assemblies");
        var emitted = File.ReadAllLines(Path.Combine(directory, "emitted.tsv")).Select(l => l.Split('\t')).ToArray();
        var a = new Assertions();
        using var table = File.CreateText(Path.Combine(directory, "ilverify.tsv"));
        using var resolver = new Resolver(assemblies);
        var verifier = new Verifier(resolver, new VerifierOptions { SanityChecks = true });
        verifier.SetSystemModuleName(new AssemblyNameInfo("mscorlib"));
        foreach (var group in emitted.GroupBy(f => f[0]).OrderBy(g => g.Key, StringComparer.Ordinal))
        {
            var pe = resolver.Resolve(Path.GetFileNameWithoutExtension(group.Key)) ?? throw new FileNotFoundException(group.Key);
            var reader = pe.GetMetadataReader();
            var errors = new List<(string Method, VerificationResult Result)>();
            var misnamed = 0;
            foreach (var fields in group)
            {
                var handle = (MethodDefinitionHandle)MetadataTokens.EntityHandle(Convert.ToInt32(fields[5], 16));
                var name = Name(reader, reader.GetMethodDefinition(handle));
                // emitted.tsv 的方法名是 L3 的写法（嵌套类型以 . 连接），只核对末尾的方法名
                if (!fields[4].EndsWith("." + name.Split('.')[^1], StringComparison.Ordinal)) misnamed++;
                var methodErrors = verifier.Verify(pe, handle).ToArray();
                foreach (var result in methodErrors) errors.Add((name, result));
                table.WriteLine($"{fields[3]}\t{fields[4]}\t{methodErrors.Length}\t{string.Join(',', methodErrors.Select(e => e.Code).Distinct())}\t{(fields.Length > 6 ? fields[6] : "target")}");
            }
            Console.WriteLine($"  {group.Key}: 校验方法 {group.Count()}，错误 {errors.Count}（涉及 {errors.Select(e => e.Method).Distinct().Count()} 个方法）");
            foreach (var code in errors.GroupBy(e => e.Result.Code).OrderByDescending(g => g.Count()).Take(12))
                Console.WriteLine($"    {code.Key,-28} {code.Count(),5}  例：{code.First().Method}: {code.First().Result.Message}");
            if (Environment.GetEnvironmentVariable("ILVERIFY_VERBOSE") == "1")
                foreach (var error in errors)
                    Console.WriteLine($"    {error.Method}: {error.Result.Code}: {error.Result.Message}; {string.Join(", ", error.Result.Args ?? [])}; {System.Text.Json.JsonSerializer.Serialize(error.Result.ErrorArguments, new System.Text.Json.JsonSerializerOptions { IncludeFields = true })}");
            a.Equal(0, misnamed, $"{group.Key} 中元数据标记与方法名对不上的方法");
            a.Equal(0, errors.Count, $"{group.Key} 的 ILVerify 错误");
        }
        return a.Finish("ilverify");
    }

    private static string Name(MetadataReader reader, MethodDefinition method)
    {
        var type = reader.GetTypeDefinition(method.GetDeclaringType());
        var ns = reader.GetString(type.Namespace);
        return $"{(ns.Length > 0 ? ns + "." : "")}{reader.GetString(type.Name)}.{reader.GetString(method.Name)}";
    }

    private sealed class Resolver(string directory) : IResolver, IDisposable
    {
        private readonly Dictionary<string, PEReader?> readers = new(StringComparer.OrdinalIgnoreCase);

        public PEReader? Resolve(string name)
        {
            if (!readers.TryGetValue(name, out var reader))
            {
                var path = Path.Combine(directory, name + ".dll");
                readers.Add(name, reader = File.Exists(path) ? new PEReader(File.OpenRead(path)) : null);
            }
            return reader;
        }

        PEReader? IResolver.ResolveAssembly(AssemblyNameInfo assemblyName) => Resolve(assemblyName.Name);
        PEReader? IResolver.ResolveModule(AssemblyNameInfo referencingAssembly, string fileName) => Resolve(Path.GetFileNameWithoutExtension(fileName));

        public void Dispose()
        {
            foreach (var reader in readers.Values) reader?.Dispose();
        }
    }
}
