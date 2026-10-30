using Cpp2CS.Output;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

internal static class SourceInjectedCallsCheck
{
    [Command("source-injected-calls", "IL 注入的私有泛型参数经源码编译后保持类型和原异常", Gate = Gate.Unit)]
    public static int Run()
    {
        var directory = Path.GetFullPath("artifacts/source-injected-calls");
        Directory.CreateDirectory(directory);
        var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator)
            .Select(p => MetadataReference.CreateFromFile(p)).ToArray();
        byte[] Compile(string source, string name, bool dependency = false)
        {
            var compilation = CSharpCompilation.Create(name, [CSharpSyntaxTree.ParseText(source)],
                dependency ? references.Append(MetadataReference.CreateFromFile(Path.Combine(directory, "Injected.Input.dll"))) : references,
                new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, optimizationLevel: OptimizationLevel.Release));
            using var stream = new MemoryStream();
            var result = compilation.Emit(stream);
            if (!result.Success) throw new InvalidOperationException(string.Join('\n', result.Diagnostics));
            return stream.ToArray();
        }
        var bytes = Compile("""
            using System;
            namespace Unity.Jobs { public class DOTSCompilerGeneratedAttribute : Attribute { } }
            public class Container
            {
                private struct Hidden { }
                public static Type HiddenType => typeof(Hidden);
                public static void Reference()
                {
                    try { Target.Run<Hidden>(); }
                    catch (Exception error) { Generated.Caught = error; Generated.Reported = typeof(Hidden); }
                }
            }
            public static class Target
            {
                public static Type Seen;
                public static Exception Failure;
                public static int Calls;
                public static void Run<T>() { Calls++; Seen = typeof(T); if (Failure != null) throw Failure; }
            }
            [Unity.Jobs.DOTSCompilerGenerated]
            public class Generated
            {
                public static Exception Caught;
                public static Type Reported;
                public static void Run()
                {
                    try { Target.Run<int>(); }
                    catch (Exception error) { Caught = error; Reported = typeof(int); }
                }
            }
            """, "Injected.Input");
        var input = Path.Combine(directory, "Injected.Input.dll");
        using (var module = ModuleDefinition.ReadModule(new MemoryStream(bytes)))
        {
            var hidden = module.Types.Single(t => t.Name == "Container").NestedTypes.Single();
            foreach (var instruction in module.Types.Single(t => t.Name == "Generated").Methods.Single(m => m.Name == "Run").Body.Instructions)
            {
                if (instruction.Operand is GenericInstanceMethod method) method.GenericArguments[0] = hidden;
                if (instruction.OpCode.Code == Code.Ldtoken && instruction.Operand is TypeReference { FullName: "System.Int32" }) instruction.Operand = hidden;
            }
            module.Write(input);
        }
        var source = FullDecompilation.Decompile(input, directory, t => t.ReflectionName == "Generated", false, true).Single().Source;
        File.WriteAllText(Path.Combine(directory, "Generated.cs"), source);
        var rebuilt = Compile(source, "Injected.Rebuilt", dependency: true);
        var original = System.Runtime.Loader.AssemblyLoadContext.Default.LoadFromAssemblyPath(input);
        var restored = System.Runtime.Loader.AssemblyLoadContext.Default.LoadFromStream(new MemoryStream(rebuilt));
        var target = original.GetType("Target")!;
        var hiddenType = (Type)original.GetType("Container")!.GetProperty("HiddenType")!.GetValue(null)!;
        var a = new Assertions();
        a.True(hiddenType.IsNestedPrivate, "依赖类型保持私有，不修改编译引用的访问权限");
        a.True(source.Contains("CreateDelegate") && !source.Contains(".Invoke("), "使用直接委托调用，避免反射调用的异常包装");
        foreach (var assembly in new[] { original, restored })
        foreach (var failure in new Exception?[] { null, new InvalidOperationException("probe") })
        {
            target.GetField("Failure")!.SetValue(null, failure);
            target.GetField("Calls")!.SetValue(null, 0);
            var generated = assembly.GetType("Generated")!;
            generated.GetField("Caught")!.SetValue(null, null);
            var invoke = assembly == original ? original.GetType("Container")!.GetMethod("Reference")! : generated.GetMethod("Run")!;
            invoke.CreateDelegate<Action>()();
            a.Equal(1, (int)target.GetField("Calls")!.GetValue(null)!, "合法参照与重编译形式均只调用一次");
            a.True(ReferenceEquals(hiddenType, target.GetField("Seen")!.GetValue(null)), "泛型参数保留私有类型身份");
            a.True(ReferenceEquals(failure, generated.GetField("Caught")!.GetValue(null)), "catch 获得同一个异常对象");
            if (failure is not null) a.True(ReferenceEquals(hiddenType, generated.GetField("Reported")!.GetValue(null)), "异常记录的 typeof 保留同一个私有类型");
        }
        return a.Finish("source-injected-calls");
    }
}
