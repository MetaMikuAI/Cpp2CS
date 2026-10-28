using Cpp2CS.Output;
using ICSharpCode.Decompiler.Metadata;
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
                public static int BranchVisits;
                public static void Touch(int value) => BranchVisits += value;
                public static bool NullAfterReset(bool reset)
                {
                    object value = new object();
                    if (reset) value = null;
                    return value == null;
                }
                public static Func<int> BranchCapture(int seed)
                {
                    int current = seed;
                    return () => ++current;
                }
                public static Func<int>[] NestedCapture(int seed, bool branch)
                {
                    int current = seed;
                    Func<int> outer = () => ++current;
                    if (seed < 0) return new[] { outer, outer };
                    {
                        int step = 2;
                        return new[] { outer, () => current += step };
                    }
                }
                public IEnumerable<int> InstanceValues()
                {
                    var owner = this;
                    Action advance = () => owner.Value++;
                    yield return owner.Value;
                    advance();
                    yield return owner.Value;
                }
                public IEnumerable<int> RepeatedInstanceValues(int count)
                {
                    Probe owner;
                    for (int i = 0; i < count; i++)
                    {
                        owner = this;
                        Action advance = () => owner.Value++;
                        yield return owner.Value;
                        advance();
                    }
                }
                public IEnumerable<int> ReassignedInstanceValues(Probe other)
                {
                    var owner = this;
                    yield return owner.Value;
                    owner = other;
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
        var branchCapture = module.GetType("Probe").Methods.Single(m => m.Name == "BranchCapture");
        var originalInstructions = branchCapture.Body.Instructions.ToArray();
        var constructors = originalInstructions.Where(i => i.OpCode == OpCodes.Newobj).Select(i => (MethodReference)i.Operand).ToArray();
        var callback = (MethodReference)originalInstructions.Single(i => i.OpCode == OpCodes.Ldftn).Operand;
        var captured = (FieldReference)originalInstructions.Single(i => i.OpCode == OpCodes.Stfld).Operand;
        var touch = module.GetType("Probe").Methods.Single(m => m.Name == "Touch");
        var root = new VariableDefinition(constructors[0].DeclaringType);
        var alias = new VariableDefinition(root.VariableType);
        branchCapture.Body.Instructions.Clear(); branchCapture.Body.Variables.Clear();
        branchCapture.Body.Variables.Add(root); branchCapture.Body.Variables.Add(alias);
        var branchIl = branchCapture.Body.GetILProcessor();
        var right = branchIl.Create(OpCodes.Ldc_I4_2);
        var joined = branchIl.Create(OpCodes.Ldloc, alias);
        var initialize = branchIl.Create(OpCodes.Ldloc, root);
        // 两个分支把同一个入口闭包赋给副本，回调必须继续共享该对象。
        foreach (var instruction in new[] {
            branchIl.Create(OpCodes.Newobj, constructors[0]), branchIl.Create(OpCodes.Stloc, root),
            branchIl.Create(OpCodes.Ldloc, root), branchIl.Create(OpCodes.Brtrue, initialize),
            branchIl.Create(OpCodes.Newobj, module.ImportReference(typeof(NullReferenceException).GetConstructor(Type.EmptyTypes)!)), branchIl.Create(OpCodes.Throw),
            initialize, branchIl.Create(OpCodes.Ldarg_0), branchIl.Create(OpCodes.Stfld, captured),
            branchIl.Create(OpCodes.Ldarg_0), branchIl.Create(OpCodes.Ldc_I4_0), branchIl.Create(OpCodes.Bge, right),
            branchIl.Create(OpCodes.Ldc_I4_1), branchIl.Create(OpCodes.Call, touch),
            branchIl.Create(OpCodes.Ldloc, root), branchIl.Create(OpCodes.Stloc, alias), branchIl.Create(OpCodes.Br, joined),
            right, branchIl.Create(OpCodes.Call, touch), branchIl.Create(OpCodes.Ldloc, root), branchIl.Create(OpCodes.Stloc, alias), joined, branchIl.Create(OpCodes.Ldftn, callback),
            branchIl.Create(OpCodes.Newobj, constructors[1]), branchIl.Create(OpCodes.Ret) }) branchIl.Append(instruction);
        var nested = module.GetType("Probe").Methods.Single(m => m.Name == "NestedCapture");
        nested.Body.SimplifyMacros();
        var linkStore = nested.Body.Instructions.Single(i => i.OpCode == OpCodes.Stfld && i.Operand is FieldReference field
            && field.Name.Contains("locals", StringComparison.Ordinal));
        var link = (FieldReference)linkStore.Operand;
        var holder = nested.Body.Variables.Single(v => v.VariableType.FullName == link.DeclaringType.FullName);
        var linked = new VariableDefinition(link.FieldType);
        nested.Body.Variables.Add(linked);
        var nestedIl = nested.Body.GetILProcessor();
        var alternate = nestedIl.Create(OpCodes.Ldc_I4_2);
        var join = nestedIl.Create(OpCodes.Ldloc, linked);
        var cursorLink = linkStore;
        // 两条路径从内层闭包读取同一外层引用，合流后仍共享可变捕获。
        foreach (var instruction in new[] {
            nestedIl.Create(OpCodes.Ldarg_1), nestedIl.Create(OpCodes.Brtrue, alternate),
            nestedIl.Create(OpCodes.Ldc_I4_1), nestedIl.Create(OpCodes.Call, touch),
            nestedIl.Create(OpCodes.Ldloc, holder), nestedIl.Create(OpCodes.Ldfld, link), nestedIl.Create(OpCodes.Stloc, linked), nestedIl.Create(OpCodes.Br, join),
            alternate, nestedIl.Create(OpCodes.Call, touch), nestedIl.Create(OpCodes.Ldloc, holder), nestedIl.Create(OpCodes.Ldfld, link),
            nestedIl.Create(OpCodes.Stloc, linked), join,
            nestedIl.Create(OpCodes.Ldfld, link.FieldType.Resolve().Fields.Single(f => f.Name == "current")), nestedIl.Create(OpCodes.Call, touch) })
        {
            nestedIl.InsertAfter(cursorLink, instruction);
            cursorLink = instruction;
        }
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
        bool EmptyClosureConstructor(string path)
        {
            using var file = new ICSharpCode.Decompiler.Metadata.PEFile(path);
            var resolver = new ICSharpCode.Decompiler.Metadata.UniversalAssemblyResolver(path, true, file.DetectTargetFrameworkId());
            var system = new ICSharpCode.Decompiler.TypeSystem.DecompilerTypeSystem(file, resolver, Decompilation.Settings(true));
            var constructor = system.MainModule.TopLevelTypeDefinitions.Single(t => t.Name == "Probe").NestedTypes
                .Single(t => t.Name == link.DeclaringType.Name).Methods.Single(m => m.IsConstructor && !m.IsStatic);
            return (bool)typeof(Decompilation).GetNestedType("ClosureLinks", System.Reflection.BindingFlags.NonPublic)!
                .GetMethod("EmptyConstructor", System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Static)!.Invoke(null, [constructor])!;
        }
        a.True(EmptyClosureConstructor(input), "普通闭包构造只调用 object 构造");
        var publishingConstructor = link.DeclaringType.Resolve().Methods.Single(m => m.IsConstructor && !m.IsStatic);
        var constructorIl = publishingConstructor.Body.GetILProcessor();
        constructorIl.InsertBefore(publishingConstructor.Body.Instructions[0], constructorIl.Create(OpCodes.Call, touch));
        constructorIl.InsertBefore(publishingConstructor.Body.Instructions[0], constructorIl.Create(OpCodes.Ldc_I4_1));
        var altered = Path.Combine(directory, "ConstructorEffect.dll");
        module.Write(altered);
        a.True(!EmptyClosureConstructor(altered), "附加构造调用可能发布 this，不能据此消除字段读取");
        a.True(!source.Contains("DisplayClass", StringComparison.Ordinal), "分支副本和挂起副本均展开为共享捕获变量");
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
            var checkNull = type.GetMethod("NullAfterReset")!.CreateDelegate<Func<bool, bool>>();
            a.True(!checkNull(false) && checkNull(true), "允许重新赋值为 null 的变量不能按新对象消除判空");
            var factory = type.GetMethod("BranchCapture")!.CreateDelegate<Func<int, Func<int>>>();
            foreach (var seed in new[] { -4, 7 })
            {
                type.GetField("BranchVisits")!.SetValue(null, 0);
                var callbackProbe = factory(seed);
                a.True(callbackProbe() == seed + 1 && callbackProbe() == seed + 2 && (int)type.GetField("BranchVisits")!.GetValue(null)! == (seed < 0 ? 1 : 2),
                    $"seed={seed} 分支合流后的回调共享可变捕获并保留分支调用");
            }
            var nestedFactory = type.GetMethod("NestedCapture")!.CreateDelegate<Func<int, bool, Func<int>[]>>();
            foreach (var seed in new[] { -4, 0, 7 })
                foreach (var branch in new[] { false, true })
                {
                    type.GetField("BranchVisits")!.SetValue(null, 0);
                    var callbacks = nestedFactory(seed, branch);
                    a.True(callbacks[0]() == seed + 1 && callbacks[1]() == seed + (seed < 0 ? 2 : 3)
                        && callbacks[0]() == seed + (seed < 0 ? 3 : 4), "嵌套闭包与分支合流仍共享同一捕获对象");
                    a.Equal(seed < 0 ? 0 : seed + (branch ? 2 : 1), (int)type.GetField("BranchVisits")!.GetValue(null)!, "保留分支调用和读取顺序");
                }
            var instance = Activator.CreateInstance(type)!;
            type.GetField("Value")!.SetValue(instance, 7);
            var iterator = ((IEnumerable<int>)type.GetMethod("InstanceValues")!.Invoke(instance, null)!).GetEnumerator();
            a.True(iterator.MoveNext() && iterator.Current == 7, "this 副本首次挂起读取实例");
            type.GetField("Value")!.SetValue(instance, 123);
            a.True(iterator.MoveNext() && iterator.Current == 124 && !iterator.MoveNext(), "跨挂起后的 lambda 仍修改同一个实例");
            type.GetField("Value")!.SetValue(instance, 4);
            var repeated = (IEnumerable<int>)type.GetMethod("RepeatedInstanceValues")!.Invoke(instance, [3])!;
            a.True(repeated.SequenceEqual([4, 5, 6]) && (int)type.GetField("Value")!.GetValue(instance)! == 7,
                "循环内赋值的 this 副本保留挂起与捕获修改");
            var other = Activator.CreateInstance(type)!;
            type.GetField("Value")!.SetValue(other, 99);
            var reassigned = (IEnumerable<int>)type.GetMethod("ReassignedInstanceValues")!.Invoke(instance, [other])!;
            a.True(reassigned.SequenceEqual([7, 99]), "可改为其他实例的局部变量不能替换为 this");
        }
        return a.Finish("source-iterator-copies");
    }
}
