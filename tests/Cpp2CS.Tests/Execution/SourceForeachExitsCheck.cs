using Cpp2CS.Output;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Cpp2CS.Tests.Execution;

internal static class SourceForeachExitsCheck
{
    [Command("source-foreach-exits", "外跳枚举的释放路径、公共结果与捕获局部", Gate = Gate.Unit)]
    public static int Run()
    {
        var directory = Path.GetFullPath("artifacts/source-foreach-exits");
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
        string[] modes = ["Valid", "Captured", "Typed", "LeadingMember", "AssignedMember", "AssignmentTarget", "NestedIf", "OuterFinally", "MissingCleanup", "SharedEntry", "Fallthrough", "Split", "SplitRejected", "NestedCallback"];
        var methods = string.Join('\n', modes.Where(mode => !mode.StartsWith("Split", StringComparison.Ordinal)).Select(mode => $$"""
            public static Entry {{mode}}({{(mode == "Typed" ? "ObjectSequence" : "Sequence")}} sequence, int key, bool bypass)
            {
                {{(mode == "Typed" ? "ObjectSequence" : "Sequence")}}.Enumerator iterator = default;
                Entry current = null;
                {{(mode == "Captured" ? "Action observe = () => Trace.Add(\"O\" + (current?.Id.ToString() ?? \"null\"));" : "")}}
                {{(mode == "NestedIf" ? "if (!bypass) { if (sequence != null) {" : mode == "OuterFinally" ? "try { if (!bypass) {" : "")}}
                iterator = sequence.GetEnumerator();
                try
                {
                    while (iterator.MoveNext())
                    {
                        {{(mode == "LeadingMember" ? "int[] numbers = iterator.Current.Numbers; if (numbers.Length == 0) continue; current = new Entry(numbers[0]);" : mode == "AssignmentTarget" ? "Receiver().Value = iterator.Current.Self; current = Storage.Value;" : "current = " + (mode == "Typed" ? "(Entry)" : "") + "iterator.Current" + (mode == "AssignedMember" ? ".Self" : "") + ";")}}
                        {{(mode == "NestedCallback" ? "Func<int> read = () => { Trace.Add(\"L\"); return current.Id; }; if (read() != key) continue;" : "if (current.Id != key) continue;")}}
                        goto found;
                    }
                }
                catch (Exception) { iterator.Dispose(); throw; }
                iterator.Dispose();
                {{(mode == "NestedIf" ? "} }" : mode == "OuterFinally" ? "} } finally { Trace.Add(\"F\"); }" : "")}}
                Entry created = new Entry(99);
                Entry result = created;
                {{(mode == "SharedEntry" ? "if (bypass) { current = created; goto found; }" : "")}}
                {{(mode == "Fallthrough" ? "" : "goto finished;")}}
                found:
                {{(mode == "MissingCleanup" ? "" : "iterator.Dispose();")}}
                result = current;
                goto finished;
                finished:
                {{(mode == "Captured" ? "observe();" : "")}}
                result.Initialize();
                return result;
            }
            """));
        methods += string.Join('\n', new[] { "Split", "SplitRejected" }.Select(mode => $$"""
            public static Entry {{mode}}(Sequence sequence, int key, bool bypass)
            {
                Sequence.Enumerator iterator = default;
                Entry current = null;
                if (bypass)
                {
                    iterator = sequence.GetEnumerator();
                    try
                    {
                        while (iterator.MoveNext())
                        {
                            current = iterator.Current;
                            if (current.Id != key) continue;
                            goto found;
                        }
                    }
                    catch (Exception) { iterator.Dispose(); throw; }
                }
                else
                {
                    iterator = sequence.Other().GetEnumerator();
                    try
                    {
                        while (iterator.MoveNext())
                        {
                            {{(mode == "SplitRejected" ? "Trace.Add(\"B\");" : "")}}
                            current = iterator.Current;
                            if (current.Id < key) continue;
                            if (current.Id != key) continue;
                            goto found;
                        }
                    }
                    catch (Exception) { iterator.Dispose(); throw; }
                }
                iterator.Dispose();
                return new Entry(99);
                found:
                iterator.Dispose();
                current.Initialize();
                return current;
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
                public class Holder { public Entry Value; }
                public static Holder Storage = new Holder();
                public static Holder Receiver() { Trace.Add("R"); return Storage; }
                public class Entry
                {
                    public int Id;
                    public int[] Numbers { get { Trace.Add("P"); if (Failure == 4) throw new InvalidOperationException(); return new[] { Id }; } }
                    public Entry Self { get { Trace.Add("S"); return this; } }
                    public Entry(int id) { Id = id; Trace?.Add("N" + id); }
                    public void Initialize() { Trace.Add("I" + Id); if (Failure == 3) throw new InvalidOperationException(); }
                }
                public class Sequence
                {
                    public Entry[] Values;
                    public Sequence Other() { Trace.Add("O"); return this; }
                    public Enumerator GetEnumerator() { Trace.Add("G"); return new Enumerator { Values = Values, Index = -1 }; }
                    public struct Enumerator : IEnumerator<Entry>
                    {
                        public Entry[] Values;
                        public int Index;
                        public Entry Current { get { Trace.Add("C"); if (Failure == 1) throw new InvalidOperationException(); return Values[Index]; } }
                        object IEnumerator.Current => Current;
                        public bool MoveNext() { Trace.Add("M"); return ++Index < Values.Length; }
                        public void Dispose() { Trace.Add("D"); if (Failure == 2) throw new InvalidOperationException(); }
                        public void Reset() => throw new NotSupportedException();
                    }
                }
                public static string Observe(string mode, int[] values, int key, int failure, bool bypass)
                {
                    var input = Array.ConvertAll(values, value => value == -1 ? null : new Entry(value));
                    Trace = new List<string>(); Failure = failure;
                    var sequence = new Sequence { Values = input };
                    try
                    {
                        var result = mode switch
                        {
                            "Valid" => Valid(sequence, key, bypass),
                            "Captured" => Captured(sequence, key, bypass),
                            "Typed" => Typed(new ObjectSequence { Values = input }, key, bypass),
                            "LeadingMember" => LeadingMember(sequence, key, bypass),
                            "AssignedMember" => AssignedMember(sequence, key, bypass),
                            "AssignmentTarget" => AssignmentTarget(sequence, key, bypass),
                            "NestedIf" => NestedIf(sequence, key, bypass),
                            "OuterFinally" => OuterFinally(sequence, key, bypass),
                            "MissingCleanup" => MissingCleanup(sequence, key, bypass),
                            "SharedEntry" => SharedEntry(sequence, key, bypass),
                            "Fallthrough" => Fallthrough(sequence, key, bypass),
                            "Split" => Split(sequence, key, bypass),
                            "SplitRejected" => SplitRejected(sequence, key, bypass),
                            "NestedCallback" => NestedCallback(sequence, key, bypass),
                            _ => throw new NotSupportedException()
                        };
                        Trace.Add(Array.IndexOf(input, result) >= 0 ? "original" : "created");
                    }
                    catch (InvalidOperationException) { Trace.Add("X"); }
                    catch (NullReferenceException) { Trace.Add("NRE"); }
                    return string.Join(",", Trace);
                }
                METHODS
                public class ObjectSequence
                {
                    public Entry[] Values;
                    public Enumerator GetEnumerator() { Trace.Add("G"); return new Enumerator { Values = Values, Index = -1 }; }
                    public struct Enumerator : IEnumerator<object>
                    {
                        public Entry[] Values;
                        public int Index;
                        public object Current { get { Trace.Add("C"); if (Failure == 1) throw new InvalidOperationException(); return Values[Index]; } }
                        public bool MoveNext() { Trace.Add("M"); return ++Index < Values.Length; }
                        public void Dispose() { Trace.Add("D"); if (Failure == 2) throw new InvalidOperationException(); }
                        public void Reset() => throw new NotSupportedException();
                    }
                }
            }
            """.Replace("METHODS", methods, StringComparison.Ordinal);
        var original = Compile(inputSource, "ForeachExits.Input");
        var input = Path.Combine(directory, "Input.dll");
        File.WriteAllBytes(input, original);
        var source = Decompilation.Decompile(input, directory, t => t.Name == "Probe", false, true).Single().Source;
        File.WriteAllText(Path.Combine(directory, "Probe.cs"), source);
        var tree = CSharpSyntaxTree.ParseText(source).GetRoot();
        var a = new Assertions();
        foreach (var mode in modes)
            a.Equal(mode == "Split" ? 2 : mode is "Valid" or "Captured" or "Typed" or "LeadingMember" or "AssignedMember" or "NestedIf" or "NestedCallback" ? 1 : 0, tree.DescendantNodes().OfType<MethodDeclarationSyntax>().Single(m => m.Identifier.ValueText == mode)
                .DescendantNodes().OfType<ForEachStatementSyntax>().Count(), "只在外跳清理完整且独占时恢复 foreach");
        var rebuilt = Compile(source, "ForeachExits.Rebuilt");
        Func<string, int[], int, int, bool, string> Observe(byte[] bytes) => System.Reflection.Assembly.Load(bytes).GetType("Probe")!.GetMethod("Observe")!
            .CreateDelegate<Func<string, int[], int, int, bool, string>>();
        var before = Observe(original); var after = Observe(rebuilt);
        int[][] inputs = [[], [2], [1, 2, 3], [1, 3], [-1, 2]];
        foreach (var mode in modes)
            foreach (var values in inputs)
                foreach (var failure in Enumerable.Range(0, 4))
                    foreach (var bypass in new[] { false, true })
                        a.Equal(before(mode, values, 2, failure, bypass), after(mode, values, 2, failure, bypass), "匹配、耗尽、空/异常、创建和捕获读取顺序一致");
        a.Equal("G,M,C,D,I2,original", after("Valid", [2], 2, 0, false), "匹配分支先释放再初始化原对象");
        a.Equal("G,M,D,N99,I99,created", after("Valid", [], 2, 0, false), "耗尽分支先释放再创建对象");
        a.Equal("G,M,C,D,O2,I2,original", after("Captured", [2], 2, 0, false), "捕获局部仍收到实际元素");
        a.Equal("G,M,C,D,I2,original", after("NestedIf", [2], 2, 0, false), "跨普通分支仍先释放再使用结果");
        a.Equal("G,M,C,F,D,I2,original", after("OuterFinally", [2], 2, 0, false), "跨外层 finally 的释放顺序保持不变");
        a.Equal(before("LeadingMember", [2], 2, 4, false), after("LeadingMember", [2], 2, 4, false), "成员 getter 抛错仍正确释放");
        a.Equal("G,M,C,P,D,X", after("LeadingMember", [2], 2, 4, false), "Current 之后读取成员，异常后释放一次");
        a.Equal("G,M,R,C,S,D,I2,original", after("AssignmentTarget", [2], 2, 0, false), "有副作用的赋值目标仍先于 Current 求值");
        return a.Finish("source-foreach-exits");
    }
}
