using Cpp2CS.Facts;
using Cpp2CS.Images;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Cpp2CS.Tests.Execution;

/// <summary>编译实际生成的 Wrap 源码，用 CLR 执行，与完整原生函数对照，不经过 CIL 解释器。</summary>
internal static class SourceArithmeticCheck
{
    [Command("source-arithmetic", "真实 Wrap 的生成源码编译与 CLR/ARM64 对照", Arguments = "<binary> <recover 输出目录>")]
    public static int Run(string binary, string directory)
    {
        var source = CSharpSyntaxTree.ParseText(File.ReadAllText(Path.Combine(directory, "src", "CP.Common.Math.dll_CP.MathUtility.cs")));
        var method = source.GetRoot().DescendantNodes().OfType<MethodDeclarationSyntax>()
            .Single(m => m.Identifier.ValueText == "Wrap" && m.ReturnType.ToString() == "int");
        var unit = SyntaxFactory.CompilationUnit().AddMembers(SyntaxFactory.ClassDeclaration("SourceWrap")
            .AddModifiers(SyntaxFactory.Token(SyntaxKind.PublicKeyword), SyntaxFactory.Token(SyntaxKind.StaticKeyword)).AddMembers(method));
        var compilation = CSharpCompilation.Create("SourceWrap", [CSharpSyntaxTree.Create(unit)],
            [MetadataReference.CreateFromFile(typeof(object).Assembly.Location)], new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));
        using var stream = new MemoryStream();
        var compiled = compilation.Emit(stream);
        if (!compiled.Success) throw new InvalidOperationException(string.Join("\n", compiled.Diagnostics));
        var invoke = System.Reflection.Assembly.Load(stream.ToArray()).GetType("SourceWrap")!.GetMethod("Wrap")!
            .CreateDelegate<Func<int, int, int, int>>();
        var row = File.ReadLines(Path.Combine(directory, "emitted.tsv")).Select(l => l.Split('\t'))
            .Single(f => f[0] == "CP.Common.Math.dll" && f[4] == "CP.MathUtility.Wrap");
        var entry = Convert.ToUInt64(row[3][2..], 16);
        var image = ImageDocument.Load(binary);
        var function = CodeMap.Build(image).At(entry)!;
        using var arm = new Unicorn();
        var page = entry & ~0xfffUL;
        arm.Map(page, (function.End + 0xfff & ~0xfffUL) - page);
        arm.Write(entry, image.Read(entry, (int)function.Size));
        arm.Map(0x1000, 0x1000);
        bool returned = false;
        arm.OnCode((_, address, _, _) =>
        {
            if (address == 0x1000) { returned = true; arm.Stop(); }
            else if (address < entry || address >= function.End) arm.Stop();
        });
        int[] edges = [int.MinValue, int.MinValue + 1, -100, -7, -1, 0, 1, 7, 100, int.MaxValue - 1, int.MaxValue];
        var random = new Random(20261024);
        var cases = edges.SelectMany(x => edges.SelectMany(min => edges.Select(max => (x, min, max))))
            .Concat(Enumerable.Range(0, 1024).Select(_ => ((int)random.NextInt64(int.MinValue, (long)int.MaxValue + 1),
                (int)random.NextInt64(int.MinValue, (long)int.MaxValue + 1), (int)random.NextInt64(int.MinValue, (long)int.MaxValue + 1))));
        var assertions = new Assertions();
        var count = 0;
        foreach (var (x, min, max) in cases)
        {
            returned = false;
            arm.SetReg(Unicorn.X(0), (uint)x); arm.SetReg(Unicorn.X(1), (uint)min); arm.SetReg(Unicorn.X(2), (uint)max);
            arm.SetReg(Unicorn.X(3), 0); arm.SetReg(Unicorn.X(30), 0x1000);
            var error = arm.Start(entry, 128);
            if (error != 0 || !returned) throw new InvalidOperationException($"Wrap 原生执行未正常返回：{Unicorn.Error(error)}");
            assertions.Equal(unchecked((int)arm.Reg(Unicorn.X(0))), invoke(x, min, max), $"Wrap({x}, {min}, {max})");
            count++;
        }
        Console.WriteLine($"实际生成的 Wrap 源码：{count} 组整数边界/随机输入，CLR 对照原生函数 0x{entry:x}");
        return assertions.Finish("source-arithmetic");
    }
}
