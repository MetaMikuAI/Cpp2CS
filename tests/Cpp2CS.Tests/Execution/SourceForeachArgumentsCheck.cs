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
            ("Arithmetic", "sink.Add((int)(double)(iterator.Current + Effect()));"),
            ("LateArithmetic", "sink.Add((int)(double)(Effect() + iterator.Current));"),
            ("StableArgument", "sink.AddPair(sink, iterator.Current);"),
            ("CapturedArgument", "sink.AddPair(sink, iterator.Current);"),
            ("FinallyDirect", "sink.Add(iterator.Current);"),
            ("FinallyPrefix", "Sink saved = sink; int current = iterator.Current; saved.Add(current);"),
            ("FinallyExtra", "sink.Add(iterator.Current);"),
            ("FinallyYield", "yield return iterator.Current;"),
        };
        var methods = string.Join('\n', samples.Select(s => $$"""
            public static {{(s.Name == "FinallyYield" ? "IEnumerable<int>" : "void")}} {{s.Name}}(Sequence sequence, {{(s.Name == "RefReceiver" ? "ref " : "")}}Sink sink)
            {
                {{(s.Name is "Captured" or "CapturedArgument" ? "sequence.OnCurrent = () => sink = null;" : "")}}
                Sequence.Enumerator iterator = default;
                iterator = sequence.GetEnumerator();
                try { while (iterator.MoveNext()) { {{s.Statement}} } }
                {{(s.Name.StartsWith("Finally", StringComparison.Ordinal) ? "finally { iterator.Dispose(); " + (s.Name == "FinallyExtra" ? "Trace.Add(\"F\");" : "") + " }" : "catch (Exception) { iterator.Dispose(); throw; } iterator.Dispose();")}}
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
                    public void AddPair(Sink first, int value) { Trace.Add(first == null ? "PN" : "PS"); Add(value); }
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
                            case "Arithmetic": Arithmetic(sequence, sink); break;
                            case "LateArithmetic": LateArithmetic(sequence, sink); break;
                            case "StableArgument": StableArgument(sequence, sink); break;
                            case "CapturedArgument": CapturedArgument(sequence, sink); break;
                            case "FinallyDirect": FinallyDirect(sequence, sink); break;
                            case "FinallyPrefix": FinallyPrefix(sequence, sink); break;
                            case "FinallyExtra": FinallyExtra(sequence, sink); break;
                            case "FinallyYield": foreach (var value in FinallyYield(sequence, sink)) { Trace.Add("Y" + value); if (failure == 6) break; } break;
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
            a.Equal(sample.Name is "Direct" or "Arithmetic" or "StableArgument" or "FinallyDirect" or "FinallyPrefix" or "FinallyYield" ? 1 : 0,
                tree.DescendantNodes().OfType<MethodDeclarationSyntax>().Single(m => m.Identifier.ValueText == sample.Name)
                .DescendantNodes().OfType<ForEachStatementSyntax>().Count(), "保留参数求值与 finally 清理边界：" + sample.Name);
        var rebuilt = Compile(source, "ForeachArguments.Rebuilt");
        Func<string, int, string> Observe(byte[] bytes) => System.Reflection.Assembly.Load(bytes).GetType("Probe")!.GetMethod("Observe")!
            .CreateDelegate<Func<string, int, string>>();
        var before = Observe(original);
        var after = Observe(rebuilt);
        foreach (var sample in samples)
            foreach (var failure in Enumerable.Range(0, 7))
                a.Equal(before(sample.Name, failure), after(sample.Name, failure), "正常、空集合、Current/主体/Dispose 异常及 null 接收者事件顺序一致");
        a.Equal("M,C,D,N", after("Direct", 5), "null 接收者仍先读取 Current 再抛错并释放");
        a.Equal("M,M,M,M,D", after("Conditional", 5), "空条件接收者不读取 Current");
        a.Equal("M,C,D,X", after("Direct", 1), "Current 抛错时释放一次");
        a.Equal("M,C,A0,D,X", after("Direct", 2), "主体抛错时释放一次");
        a.Equal("M,C,A0,M,C,D,N", after("Captured", 0), "Current 改写捕获接收者时仍使用调用前读取的引用");
        a.Equal("M,C,D,X", after("Arithmetic", 1), "左侧 Current 抛错时不执行右侧调用");
        a.Equal("M,E,C,D,X", after("LateArithmetic", 1), "右侧 Current 不能越过左侧调用");
        a.Equal("M,C,Y0,D", after("FinallyYield", 6), "暂停后提前释放仍清理枚举器一次");
        return a.Finish("source-foreach-arguments");
    }
}
