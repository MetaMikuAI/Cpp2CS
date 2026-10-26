using Cpp2CS.Output;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Mono.Cecil;
using Mono.Cecil.Cil;
using Mono.Cecil.Rocks;

namespace Cpp2CS.Tests.Execution;

internal static class SourceIteratorCopiesCheck
{
    [Command("source-iterator-copies", "闭包引用副本跨 yield 后仍共享捕获值", Gate = Gate.Unit)]
    public static int Run()
    {
        var directory = Path.GetFullPath("artifacts/source-iterator-copies");
        Directory.CreateDirectory(directory);
        var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator)
            .Select(p => MetadataReference.CreateFromFile(p)).ToArray();
        byte[] Compile(string source, string name)
        {
            var compilation = CSharpCompilation.Create(name, [CSharpSyntaxTree.ParseText(source)], references,
                new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, optimizationLevel: OptimizationLevel.Release));
            using var stream = new MemoryStream();
            var emitted = compilation.Emit(stream);
            if (!emitted.Success) throw new InvalidOperationException(string.Join('\n', emitted.Diagnostics));
            return stream.ToArray();
        }
        var input = Path.Combine(directory, "IteratorCopies.Input.dll");
        var bytes = Compile("""
            using System;
            using System.Collections.Generic;
            public class Probe
            {
                public int Value;
                public IEnumerable<int> InstanceValues()
                {
                    var owner = this;
                    Action advance = () => owner.Value++;
                    yield return owner.Value;
                    advance();
                    yield return owner.Value;
                }
                public static IEnumerable<int> Values(int seed)
                {
                    int current = seed;
                    Action advance = () => current++;
                    yield return current;
                    advance();
                    yield return current;
                    current += 10;
                    advance();
                    yield return current;
                }
            }
            """, "IteratorCopies.Input");
        using var module = ModuleDefinition.ReadModule(new MemoryStream(bytes));
        var move = module.GetTypes().SelectMany(t => t.Methods).Single(m => m.Name == "MoveNext" && m.DeclaringType.Name.StartsWith("<Values>", StringComparison.Ordinal));
        move.Body.SimplifyMacros();
        var il = move.Body.GetILProcessor();
        var reads = move.Body.Instructions.Where(i => i.OpCode == OpCodes.Ldfld
            && i.Operand is FieldReference f && f.FieldType.Name.Contains("DisplayClass", StringComparison.Ordinal)).ToArray();
        // 仅插入等价的两次引用复制，保留原编译器的构造、状态、回调与清理路径。
        foreach (var read in reads)
        {
            var type = ((FieldReference)read.Operand).FieldType;
            var first = new VariableDefinition(type);
            var second = new VariableDefinition(type);
            move.Body.Variables.Add(first); move.Body.Variables.Add(second);
            var cursor = read;
            foreach (var instruction in new[] { il.Create(OpCodes.Stloc, first), il.Create(OpCodes.Ldloc, first), il.Create(OpCodes.Stloc, second), il.Create(OpCodes.Ldloc, second) })
            {
                il.InsertAfter(cursor, instruction);
                cursor = instruction;
            }
        }
        module.Write(input);
        var source = Decompilation.Decompile(input, directory, t => t.ReflectionName == "Probe", false, true).Single().Source;
        File.WriteAllText(Path.Combine(directory, "Probe.cs"), source);
        var rebuilt = Compile(source, "IteratorCopies.Rebuilt");
        File.WriteAllBytes(Path.Combine(directory, "IteratorCopies.Rebuilt.dll"), rebuilt);
        var original = System.Reflection.Assembly.Load(File.ReadAllBytes(input)).GetType("Probe")!.GetMethod("Values")!.CreateDelegate<Func<int, IEnumerable<int>>>();
        var restored = System.Reflection.Assembly.Load(rebuilt).GetType("Probe")!.GetMethod("Values")!.CreateDelegate<Func<int, IEnumerable<int>>>();
        var a = new Assertions();
        a.True(reads.Length > 1 && source.Contains("yield return", StringComparison.Ordinal), "多个闭包读取副本仍成功折叠");
        foreach (var seed in new[] { -4, 0, 7 })
        {
            var expected = new[] { seed, seed + 1, seed + 12 };
            a.True(original(seed).SequenceEqual(expected) && restored(seed).SequenceEqual(expected), $"seed={seed} 多次挂起与回调共享捕获值");
            var iterator = restored(seed).GetEnumerator();
            iterator.MoveNext();
            iterator.Dispose();
            a.True(!iterator.MoveNext(), $"seed={seed} 保留当前编译器的提前释放行为");
        }
        foreach (var assembly in new[] { File.ReadAllBytes(input), rebuilt })
        {
            var type = System.Reflection.Assembly.Load(assembly).GetType("Probe")!;
            var instance = Activator.CreateInstance(type)!;
            type.GetField("Value")!.SetValue(instance, 7);
            var iterator = ((IEnumerable<int>)type.GetMethod("InstanceValues")!.Invoke(instance, null)!).GetEnumerator();
            a.True(iterator.MoveNext() && iterator.Current == 7, "this 副本首次挂起读取实例");
            type.GetField("Value")!.SetValue(instance, 123);
            a.True(iterator.MoveNext() && iterator.Current == 124 && !iterator.MoveNext(), "跨挂起后的 lambda 仍修改同一个实例");
        }
        return a.Finish("source-iterator-copies");
    }
}
