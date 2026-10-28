using Cpp2CS.Output;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Cpp2CS.Tests.Execution;

internal static class SourceForeachResultsCheck
{
    [Command("source-foreach-results", "枚举结束复制与释放异常、捕获局部的观察顺序", Gate = Gate.Unit)]
    public static int Run()
    {
        var directory = Path.GetFullPath("artifacts/source-foreach-results");
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
        string[] modes = ["Valid", "OuterLocal", "CapturedSource", "CapturedTarget", "FactoryCopy", "Reused", "ObservedFactory", "PrefixCallback"];
        var methods = string.Join('\n', modes.Select(mode => $$"""
            public static int {{mode}}(Sequence sequence)
            {
                int result = -7;
                {{(mode == "OuterLocal" ? "try {" : "")}}
                int sum = 0;
                {{(mode == "CapturedSource" ? "sequence.OnDispose = () => sum = 99;" : "")}}
                {{(mode == "CapturedTarget" ? "sequence.OnDispose = () => Trace.Add(\"O\" + result);" : "")}}
                Sequence.Enumerator iterator = default;
                {{(mode == "Reused" ? "iterator = sequence.GetEnumerator(); try { while (iterator.MoveNext()) { int first = iterator.Current; sum += first; if (first < 0) break; } } catch (Exception) { iterator.Dispose(); throw; } iterator.Dispose();" : "")}}
                {{(mode == "PrefixCallback" ? "int counter = 0; sequence.OnGetEnumerator = () => counter++;" : "")}}
                {{(mode is "FactoryCopy" or "ObservedFactory" or "PrefixCallback" ? "Sequence.Enumerator factory = sequence.GetEnumerator();" : "")}}
                {{(mode == "FactoryCopy" ? "int offset = 1;" : mode == "PrefixCallback" ? "int offset = counter;" : "")}}
                iterator = {{(mode is "FactoryCopy" or "ObservedFactory" or "PrefixCallback" ? "factory" : "sequence.GetEnumerator()")}};
                try
                {
                    while (iterator.MoveNext())
                    {
                        int current = iterator.Current;
                        sum += current{{(mode is "FactoryCopy" or "PrefixCallback" ? " + offset" : "")}};
                        if (current < 0) break;
                    }
                    result = sum;
                }
                catch (Exception) { iterator.Dispose(); throw; }
                iterator.Dispose();
                {{(mode == "ObservedFactory" ? "factory.MoveNext();" : "")}}
                {{(mode == "OuterLocal" ? "} catch (InvalidOperationException) { Trace.Add(\"O\" + result); }" : "")}}
                return result;
            }
            """));
        var inputSource = """
            using System;
            using System.Collections;
            using System.Collections.Generic;
            public class Probe
            {
                public static List<string> Trace;
                public static int Failure;
                public class Sequence
                {
                    public int Count;
                    public Action OnDispose;
                    public Action OnGetEnumerator;
                    public Enumerator GetEnumerator() { OnGetEnumerator?.Invoke(); return new Enumerator { Owner = this, Index = 0 }; }
                    public struct Enumerator : IEnumerator<int>
                    {
                        public Sequence Owner;
                        public int Index;
                        public int Current { get { Trace.Add("C" + Index); if (Failure == 1) throw new InvalidOperationException(); return Index; } }
                        object IEnumerator.Current => Current;
                        public bool MoveNext() { Trace.Add("M"); if (Failure == 2) throw new InvalidOperationException(); return ++Index <= Owner.Count; }
                        public void Dispose() { Trace.Add("D"); Owner.OnDispose?.Invoke(); if (Failure == 3) throw new InvalidOperationException(); }
                        public void Reset() => throw new NotSupportedException();
                    }
                }
                public static string Observe(string mode, int count, int failure)
                {
                    Trace = new List<string>(); Failure = failure;
                    var sequence = new Sequence { Count = count };
                    try
                    {
                        int result = mode switch
                        {
                            "Valid" => Valid(sequence), "OuterLocal" => OuterLocal(sequence),
                            "CapturedSource" => CapturedSource(sequence), "CapturedTarget" => CapturedTarget(sequence),
                            "FactoryCopy" => FactoryCopy(sequence), "Reused" => Reused(sequence),
                            "ObservedFactory" => ObservedFactory(sequence), "PrefixCallback" => PrefixCallback(sequence),
                            _ => throw new ArgumentException()
                        };
                        Trace.Add("R" + result);
                    }
                    catch (InvalidOperationException) { Trace.Add("X"); }
                    return string.Join(",", Trace);
                }
                METHODS
            }
            """.Replace("METHODS", methods, StringComparison.Ordinal);
        var original = Compile(inputSource, "ForeachResults.Input");
        var input = Path.Combine(directory, "Input.dll");
        File.WriteAllBytes(input, original);
        var source = Decompilation.Decompile(input, directory, t => t.Name == "Probe", false, true).Single().Source;
        File.WriteAllText(Path.Combine(directory, "Probe.cs"), source);
        var tree = CSharpSyntaxTree.ParseText(source).GetRoot();
        var a = new Assertions();
        foreach (var mode in modes)
            a.Equal(mode is "Valid" or "FactoryCopy" ? 1 : mode == "Reused" ? 2 : 0, tree.DescendantNodes().OfType<MethodDeclarationSyntax>().Single(m => m.Identifier.ValueText == mode)
                .DescendantNodes().OfType<ForEachStatementSyntax>().Count(), "仅局部且异常后不可观察的复制可延后：" + mode);
        var rebuilt = Compile(source, "ForeachResults.Rebuilt");
        Func<string, int, int, string> Observe(byte[] bytes) => System.Reflection.Assembly.Load(bytes).GetType("Probe")!.GetMethod("Observe")!
            .CreateDelegate<Func<string, int, int, string>>();
        var before = Observe(original); var after = Observe(rebuilt);
        foreach (var mode in modes)
        foreach (var count in new[] { 0, 1, 3 })
        foreach (var failure in Enumerable.Range(0, 4))
            a.Equal(before(mode, count, failure), after(mode, count, failure), "正常、空集合、Current/MoveNext/Dispose 异常与回调保持顺序");
        a.Equal("M,C1,M,C2,M,C3,M,D,O6,R6", after("OuterLocal", 3, 3), "释放失败时外部捕获仍读到复制结果");
        a.Equal("M,C1,M,C2,M,C3,M,D,R6", after("CapturedSource", 3, 0), "释放回调修改源局部不改变已保存结果");
        a.Equal("M,C1,M,C2,M,C3,M,D,O6,R6", after("CapturedTarget", 3, 0), "释放回调仍观察复制后的目标");
        a.Equal("M,C1,M,C2,M,C3,M,D,R9", after("PrefixCallback", 3, 0), "工厂回调仍先于局部快照求值");
        return a.Finish("source-foreach-results");
    }
}
