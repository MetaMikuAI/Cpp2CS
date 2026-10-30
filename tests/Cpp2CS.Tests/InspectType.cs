using ICSharpCode.Decompiler;
using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Tests;

internal static class InspectType
{
    [Command("inspect-source", "用源码输出管线查看本地程序集中的指定类型", Arguments = "<assembly> <type> <output>")]
    public static int Source(string assembly, string type, string output)
    {
        var sources = Cpp2CS.Extensions.Decompile.FullDecompilation.Decompile(assembly, Path.GetDirectoryName(Path.GetFullPath(assembly))!,
            t => t.ReflectionName == type, assemblyAttributes: false, recoveringBodies: true);
        File.WriteAllText(output, sources.Single().Source);
        return 0;
    }

    [Command("inspect-cil", "查看本地程序集中的方法 CIL", Arguments = "<assembly> <method substring> <output>")]
    public static int Cil(string assembly, string method, string output)
    {
        using var module = Mono.Cecil.ModuleDefinition.ReadModule(assembly);
        using var writer = File.CreateText(output);
        foreach (var item in module.GetTypes().SelectMany(t => t.Methods).Where(m => m.FullName.Contains(method, StringComparison.Ordinal)))
        {
            writer.WriteLine(item.FullName);
            if (item.HasBody) foreach (var instruction in item.Body.Instructions) writer.WriteLine(instruction);
        }
        return 0;
    }
    [Command("inspect-type", "查看本地程序集中的指定类型", Arguments = "<assembly> <type> <output>")]
    public static int Run(string assembly, string type, string output)
    {
        var decompiler = new CSharpDecompiler(assembly, new DecompilerSettings { ThrowOnAssemblyResolveErrors = false });
        File.WriteAllText(output, decompiler.DecompileTypeAsString(new FullTypeName(type)));
        return 0;
    }
}
