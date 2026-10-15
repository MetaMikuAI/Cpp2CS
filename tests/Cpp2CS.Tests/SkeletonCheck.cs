using System.Diagnostics;
using Cpp2CS.Output;
using ICSharpCode.Decompiler;
using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.Metadata;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Tests;

/// <summary>由模型生成骨架程序集写到目录，再用 ICSharpCode.Decompiler 反编译指定类型，检查骨架能被读回。</summary>
internal static class SkeletonCheck
{
    public static int Run(string binary, string metadata, string directory, string? typeNames)
    {
        var watch = Stopwatch.StartNew();
        var model = ModelCheck.Load(binary, metadata);
        Console.WriteLine($"模型      {watch.ElapsedMilliseconds} ms");
        watch.Restart();
        var skeleton = new Skeleton(model);
        Console.WriteLine($"骨架      {watch.ElapsedMilliseconds} ms  程序集 {skeleton.Assemblies.Count}");
        watch.Restart();
        skeleton.Write(directory);
        Console.WriteLine($"写出      {watch.ElapsedMilliseconds} ms");
        if (typeNames is null) return 0;

        var main = Path.Combine(directory, "Assembly-CSharp.dll");
        var file = new PEFile(main);
        var resolver = new UniversalAssemblyResolver(main, true, file.DetectTargetFrameworkId());
        resolver.AddSearchDirectory(directory);
        var decompiler = new CSharpDecompiler(file, resolver, new DecompilerSettings());
        // 以 .* 结尾的项表示该命名空间下的全部顶层类型
        var names = typeNames.Split(',').SelectMany(n => n.EndsWith(".*")
            ? decompiler.TypeSystem.MainModule.TopLevelTypeDefinitions.Where(t => t.Namespace == n[..^2]).Select(t => t.FullTypeName)
            : [new FullTypeName(n)]);
        foreach (var name in names)
            Console.WriteLine(decompiler.DecompileTypeAsString(name));
        return 0;
    }
}
