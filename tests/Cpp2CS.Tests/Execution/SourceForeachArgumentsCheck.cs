using Cpp2CS.Output;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Cpp2CS.Tests.Execution;

internal static class SourceForeachArgumentsCheck
{
    [Command("source-foreach-arguments", "Current 参数提升保留接收者、异常和释放的求值顺序", Gate = Gate.Unit)]
    public static int Run()
    {
        var directory = Path.GetFullPath("artifacts/source-foreach-arguments");
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
        var samples = new (string Name, string Statement)[]
        {
            ("Direct", "sink.Add(iterator.Current);"),
            ("EffectReceiver", "Receiver(sink).Add(iterator.Current);"),
            ("Conditional", "sink?.Add(iterator.Current);"),
            ("LateArgument", "sink.AddPair(Effect(), iterator.Current);"),
            ("RefReceiver", "sink.Add(iterator.Current);"),
            ("Captured", "sink.Add(iterator.Current);"),
        };
        var methods = string.Join('\n', samples.Select(s => $$"""
            public static void {{s.Name}}(Sequence sequence, {{(s.Name == "RefReceiver" ? "ref " : "")}}Sink sink)
            {
                {{(s.Name == "Captured" ? "sequence.OnCurrent = () => sink = null;" : "")}}
                Sequence.Enumerator iterator = default;
                iterator = sequence.GetEnumerator();
                try { while (iterator.MoveNext()) { {{s.Statement}} } }
                catch (Exception) { iterator.Dispose(); throw; }
                iterator.Dispose();
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
                public class Sink
                {
                    public void Add(int value) { Trace.Add("A" + value); if (Failure == 2) throw new InvalidOperationException(); }
                    public void AddPair(int first, int value) { Trace.Add("P" + first + ":" + value); Add(value); }
                }
                public class Sequence
                {
                    public int Count;
                    public Action OnCurrent;
                    public Enumerator GetEnumerator() => new Enumerator { Owner = this, Count = Count, Index = -1 };
                    public struct Enumerator : IEnumerator<int>
                    {
                        public int Count, Index;
                        public Sequence Owner;
                        public int Current { get { Trace.Add("C"); if (Failure == 1) throw new InvalidOperationException(); Owner.OnCurrent?.Invoke(); return Index; } }
                        object IEnumerator.Current => Current;
                        public bool MoveNext() { Trace.Add("M"); return ++Index < Count; }
                        public void Dispose() { Trace.Add("D"); if (Failure == 3) throw new InvalidOperationException(); }
                        public void Reset() => throw new NotSupportedException();
                    }
                }
                public static Sink Receiver(Sink sink) { Trace.Add("R"); return sink; }
                public static int Effect() { Trace.Add("E"); return 9; }
                public static string Observe(string mode, int failure)
                {
                    Trace = new List<string>(); Failure = failure;
                    var sequence = new Sequence { Count = failure == 4 ? 0 : 3 };
                    var sink = failure == 5 ? null : new Sink();
                    try
                    {
                        switch (mode)
                        {
                            case "Direct": Direct(sequence, sink); break;
                            case "EffectReceiver": EffectReceiver(sequence, sink); break;
                            case "Conditional": Conditional(sequence, sink); break;
                            case "LateArgument": LateArgument(sequence, sink); break;
                            case "RefReceiver": RefReceiver(sequence, ref sink); break;
                            case "Captured": Captured(sequence, sink); break;
                        }
                    }
                    catch (InvalidOperationException) { Trace.Add("X"); }
                    catch (NullReferenceException) { Trace.Add("N"); }
                    return string.Join(",", Trace);
                }
                METHODS
            }
            """.Replace("METHODS", methods, StringComparison.Ordinal);
        var original = Compile(inputSource, "ForeachArguments.Input");
        var input = Path.Combine(directory, "Input.dll");
        File.WriteAllBytes(input, original);
        var source = Decompilation.Decompile(input, directory, t => t.Name == "Probe", false, true).Single().Source;
        File.WriteAllText(Path.Combine(directory, "Probe.cs"), source);
        var tree = CSharpSyntaxTree.ParseText(source).GetRoot();
        var a = new Assertions();
        foreach (var sample in samples)
            a.Equal(sample.Name == "Direct" ? 1 : 0, tree.DescendantNodes().OfType<MethodDeclarationSyntax>().Single(m => m.Identifier.ValueText == sample.Name)
                .DescendantNodes().OfType<ForEachStatementSyntax>().Count(), "只提升稳定引用局部的第一个参数，保留调用、条件执行、前置参数与 ref 接收者");
        var rebuilt = Compile(source, "ForeachArguments.Rebuilt");
        Func<string, int, string> Observe(byte[] bytes) => System.Reflection.Assembly.Load(bytes).GetType("Probe")!.GetMethod("Observe")!
            .CreateDelegate<Func<string, int, string>>();
        var before = Observe(original);
        var after = Observe(rebuilt);
        foreach (var sample in samples)
            foreach (var failure in Enumerable.Range(0, 6))
                a.Equal(before(sample.Name, failure), after(sample.Name, failure), "正常、空集合、Current/主体/Dispose 异常及 null 接收者事件顺序一致");
        a.Equal("M,C,D,N", after("Direct", 5), "null 接收者仍先读取 Current 再抛错并释放");
        a.Equal("M,M,M,M,D", after("Conditional", 5), "空条件接收者不读取 Current");
        a.Equal("M,C,D,X", after("Direct", 1), "Current 抛错时释放一次");
        a.Equal("M,C,A0,D,X", after("Direct", 2), "主体抛错时释放一次");
        a.Equal("M,C,A0,M,C,D,N", after("Captured", 0), "Current 改写捕获接收者时仍使用调用前读取的引用");
        return a.Finish("source-foreach-arguments");
    }
}
