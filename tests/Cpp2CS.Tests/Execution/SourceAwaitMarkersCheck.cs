using Cpp2CS.Output;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;

namespace Cpp2CS.Tests.Execution;

internal static class SourceAwaitMarkersCheck
{
    [Command("source-await-markers", "嵌套 await 标记经过内联后仍保留挂起和异常传播", Gate = Gate.Unit)]
    public static int Run()
    {
        var directory = Path.GetFullPath("artifacts/source-await-markers");
        Directory.CreateDirectory(directory);
        var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator)
            .Select(p => MetadataReference.CreateFromFile(p)).ToArray();
        byte[] Compile(string source, string name)
        {
            var compilation = CSharpCompilation.Create(name, [CSharpSyntaxTree.ParseText(source)], references,
                new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, optimizationLevel: OptimizationLevel.Release));
            using var stream = new MemoryStream();
            var result = compilation.Emit(stream);
            if (!result.Success) throw new InvalidOperationException(string.Join('\n', result.Diagnostics));
            return stream.ToArray();
        }
        var input = Path.Combine(directory, "AwaitMarkers.Input.dll");
        File.WriteAllBytes(input, Compile("""
            using System.Threading.Tasks;
            namespace Cpp2CS
            {
                public static class Await
                {
                    public static T Of<T>(Task<T> task) => task.GetAwaiter().GetResult();
                    public static Task<T> Result<T>(T result) => Task.FromResult(result);
                }
            }
            public class Probe
            {
                public int Value { get; set; }
                public static Task<int> Read(Task<int> task) => Cpp2CS.Await.Result(Cpp2CS.Await.Of(task) + 1);
            }
            """, "AwaitMarkers.Input"));
        var source = FullDecompilation.Decompile(input, directory, t => t.ReflectionName == "Probe", false, true).Single().Source;
        File.WriteAllText(Path.Combine(directory, "Probe.cs"), source);
        var rebuilt = Compile(source, "AwaitMarkers.Rebuilt");
        var read = System.Reflection.Assembly.Load(rebuilt).GetType("Probe")!.GetMethod("Read")!.CreateDelegate<Func<Task<int>, Task<int>>>();
        var a = new Assertions();
        a.True(!source.Contains("Await.", StringComparison.Ordinal) && source.Contains("await", StringComparison.Ordinal), "内外标记均消除");
        a.True(!source.Contains("BackingField", StringComparison.Ordinal) && source.Contains("get; set;", StringComparison.Ordinal), "自动属性保留访问器");
        var pending = new TaskCompletionSource<int>();
        var result = read(pending.Task);
        a.True(!result.IsCompleted, "输入尚未完成时保留挂起");
        pending.SetResult(41);
        a.Equal(42, result.GetAwaiter().GetResult(), "恢复后返回真实 await 结果");
        var failure = new InvalidOperationException("probe");
        var faulted = read(Task.FromException<int>(failure));
        a.True(faulted.IsFaulted && ReferenceEquals(failure, faulted.Exception!.InnerException), "异步结果保留原异常对象");
        return a.Finish("source-await-markers");
    }
}
