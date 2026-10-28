using Cpp2CS.Output;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

internal static class SourceDelegateCacheCheck
{
    [Command("source-delegate-cache", "已展开 lambda 的无用缓存读取与静态初始化边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var directory = Path.GetFullPath("artifacts/source-delegate-cache");
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
        var bytes = Compile("""
            using System;
            using System.Linq;
            public static class Probe
            {
                public static int Visits;
                public static void Touch() => Visits++;
                public static Func<int, int> Transform() => value => value + 1;
                public static Func<T, T> Identity<T>() => value => value;
                public static int[] Project(int[] values) => values.Select(value => value * 3).ToArray();
                public static int[] Groups(int[] values) => values.GroupBy(value => value % 3).Select(group => group.Sum()).ToArray();
                public static int[] Filter(int[] values) => values.Where(value => value > 0).Select(value => value + 4).ToArray();
            }
            """, "DelegateCache.Input");
        var a = new Assertions();
        foreach (var sideEffect in new[] { false, true })
        {
            using var module = ModuleDefinition.ReadModule(new MemoryStream(bytes));
            var owner = module.GetType("Probe");
            var cache = owner.NestedTypes.Single(t => t.Name == "<>c");
            foreach (var method in owner.Methods.Where(m => m.Name is "Transform" or "Project" or "Identity" or "Groups" or "Filter"))
            {
                var field = (FieldReference)method.Body.Instructions.First(i => i.OpCode == OpCodes.Ldsfld
                    && ((FieldReference)i.Operand).Name.StartsWith("<>9__", StringComparison.Ordinal)).Operand;
                var il = method.Body.GetILProcessor();
                var start = method.Body.Instructions[0];
                il.InsertBefore(start, il.Create(OpCodes.Ldsfld, field));
                il.InsertBefore(start, il.Create(OpCodes.Pop));
            }
            if (sideEffect)
            {
                var initializer = cache.Methods.Single(m => m.IsConstructor && m.IsStatic);
                initializer.Body.GetILProcessor().InsertBefore(initializer.Body.Instructions[0],
                    Instruction.Create(OpCodes.Call, owner.Methods.Single(m => m.Name == "Touch")));
            }
            var input = Path.Combine(directory, sideEffect ? "Effect.dll" : "Pure.dll");
            module.Write(input);
            var source = Decompilation.Decompile(input, directory, t => t.ReflectionName == "Probe", false, true).Single().Source;
            File.WriteAllText(Path.ChangeExtension(input, ".cs"), source);
            a.Equal(sideEffect, source.Contains("_003C_003Ec", StringComparison.Ordinal), "只清除初始化无副作用且全部展开的缓存类");
            a.Equal(sideEffect, source.Contains("_ = _003C_003Ec", StringComparison.Ordinal), "有静态初始化副作用的读取必须保留");
            a.True(source.Contains("group value by", StringComparison.Ordinal) && source.Contains("where value > 0", StringComparison.Ordinal),
                "分组和筛选确实转换为查询语法");
            var rebuilt = Compile(source, sideEffect ? "DelegateCache.Effect.Rebuilt" : "DelegateCache.Pure.Rebuilt");
            foreach (var assembly in new[] { File.ReadAllBytes(input), rebuilt })
            {
                var type = System.Reflection.Assembly.Load(assembly).GetType("Probe")!;
                var factory = type.GetMethod("Transform")!.CreateDelegate<Func<Func<int, int>>>();
                var project = type.GetMethod("Project")!.CreateDelegate<Func<int[], int[]>>();
                var identity = type.GetMethod("Identity")!.MakeGenericMethod(typeof(object)).CreateDelegate<Func<Func<object, object>>>();
                var groups = type.GetMethod("Groups")!.CreateDelegate<Func<int[], int[]>>();
                var filter = type.GetMethod("Filter")!.CreateDelegate<Func<int[], int[]>>();
                var instance = new object();
                a.True(ReferenceEquals(instance, identity()(instance)) && identity()(null!) is null, "泛型方法缓存保持实例身份和 null");
                a.True(factory()(7) == 8 && factory()(-2) == -1, "委托主体与重复调用结果保持");
                a.True(project([1, -2, 0]).SequenceEqual([3, -6, 0]) && project([]).Length == 0, "枚举与空集合结果保持");
                a.True(groups([1, 4, 2, 3]).SequenceEqual([5, 2, 3]) && groups([]).Length == 0, "分组顺序与分组内聚合保持");
                a.True(filter([-2, 0, 3, 1]).SequenceEqual([7, 5]), "筛选与投影的查询方法保持");
                a.Equal(sideEffect ? 1 : 0, (int)type.GetField("Visits")!.GetValue(null)!, "静态初始化次数保持");
            }
        }
        return a.Finish("source-delegate-cache");
    }
}
