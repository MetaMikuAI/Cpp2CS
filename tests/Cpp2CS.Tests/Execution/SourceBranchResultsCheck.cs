using Cpp2CS.Output;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

internal static class SourceBranchResultsCheck
{
    [Command("source-branch-results", "共享布尔分支恢复字符串 switch 并保留碰撞默认路径", Gate = Gate.Unit)]
    public static int Run()
    {
        var directory = Path.GetFullPath("artifacts/source-branch-results");
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
            using System.Runtime.CompilerServices;
            [CompilerGenerated] public static class Hash
            {
                public static uint ComputeStringHash(string value)
                {
                    if (value == null) return 0;
                    uint hash = 2166136261;
                    foreach (char c in value) hash = unchecked((hash ^ c) * 16777619);
                    return hash;
                }
            }
            public static class Probe
            {
                public static int Calls;
                public static int Hit() { Calls++; return 42; }
                public static int Select(string key, int fallback) => fallback;
                public static int SelectCopied(string key, int fallback) => fallback;
                public static int CopyOrder(int mode, int left, int right) => 0;
            }
            """, "BranchResults.Input");
        using var module = ModuleDefinition.ReadModule(new MemoryStream(bytes));
        var owner = module.GetType("Probe");
        var method = owner.Methods.Single(m => m.Name == "Select");
        method.Body.Instructions.Clear();
        var hash = new VariableDefinition(module.TypeSystem.UInt32);
        var matched = new VariableDefinition(module.TypeSystem.Boolean);
        method.Body.Variables.Add(hash); method.Body.Variables.Add(matched); method.Body.InitLocals = true;
        var il = method.Body.GetILProcessor();
        var fallback = il.Create(OpCodes.Ldarg_1);
        var decision = il.Create(OpCodes.Ldloc, matched);
        var hashing = module.GetType("Hash").Methods.Single(m => m.Name == "ComputeStringHash");
        var equals = module.ImportReference(typeof(string).GetMethod("op_Equality", [typeof(string), typeof(string)])!);
        var hashValue = System.Reflection.Assembly.Load(bytes).GetType("Hash")!.GetMethod("ComputeStringHash")!.CreateDelegate<Func<string?, uint>>();
        string[] keys = ["alpha", "beta", "costarring", "delta", "epsilon", "zeta", "omega", "中文"];
        il.Append(il.Create(OpCodes.Ldarg_0)); il.Append(il.Create(OpCodes.Call, hashing)); il.Append(il.Create(OpCodes.Stloc, hash));
        foreach (var key in keys)
        {
            var next = il.Create(OpCodes.Nop);
            foreach (var instruction in new[] { il.Create(OpCodes.Ldloc, hash), il.Create(OpCodes.Ldc_I4, unchecked((int)hashValue(key))),
                il.Create(OpCodes.Bne_Un, next), il.Create(OpCodes.Ldarg_0), il.Create(OpCodes.Ldstr, key), il.Create(OpCodes.Call, equals),
                il.Create(OpCodes.Stloc, matched), il.Create(OpCodes.Br, decision), next }) il.Append(instruction);
        }
        il.Append(il.Create(OpCodes.Br, fallback));
        il.Append(decision); il.Append(il.Create(OpCodes.Brfalse, fallback));
        il.Append(il.Create(OpCodes.Call, owner.Methods.Single(m => m.Name == "Hit"))); il.Append(il.Create(OpCodes.Ret));
        il.Append(fallback); il.Append(il.Create(OpCodes.Ret));
        var copied = owner.Methods.Single(m => m.Name == "SelectCopied");
        copied.Body.Instructions.Clear(); copied.Body.InitLocals = true;
        var copiedIl = copied.Body.GetILProcessor();
        var copiedHash = new VariableDefinition(module.TypeSystem.UInt32);
        var carried = new VariableDefinition(module.TypeSystem.Int32);
        var result = new VariableDefinition(module.TypeSystem.Int32);
        copied.Body.Variables.Add(copiedHash); copied.Body.Variables.Add(carried); copied.Body.Variables.Add(result);
        var copiedReturn = copiedIl.Create(OpCodes.Ldloc, result);
        var hit = copiedIl.Create(OpCodes.Call, owner.Methods.Single(m => m.Name == "Hit"));
        Instruction DefaultCopy()
        {
            var temporary = new VariableDefinition(module.TypeSystem.Int32);
            copied.Body.Variables.Add(temporary);
            var start = copiedIl.Create(OpCodes.Ldloc, carried);
            foreach (var instruction in new[] { start, copiedIl.Create(OpCodes.Stloc, temporary), copiedIl.Create(OpCodes.Ldarg_1),
                copiedIl.Create(OpCodes.Stloc, result), copiedIl.Create(OpCodes.Ldloc, temporary), copiedIl.Create(OpCodes.Stloc, carried),
                copiedIl.Create(OpCodes.Br, copiedReturn) }) copiedIl.Append(instruction);
            return start;
        }
        void Tree(string[] labels)
        {
            if (labels.Length == 1)
            {
                var equal = copiedIl.Create(OpCodes.Ldarg_0);
                copiedIl.Append(copiedIl.Create(OpCodes.Ldloc, copiedHash));
                copiedIl.Append(copiedIl.Create(OpCodes.Ldc_I4, unchecked((int)hashValue(labels[0]))));
                copiedIl.Append(copiedIl.Create(OpCodes.Beq, equal));
                var missed = DefaultCopy();
                copiedIl.Append(equal); copiedIl.Append(copiedIl.Create(OpCodes.Ldstr, labels[0]));
                copiedIl.Append(copiedIl.Create(OpCodes.Call, equals)); copiedIl.Append(copiedIl.Create(OpCodes.Brfalse, missed));
                copiedIl.Append(copiedIl.Create(OpCodes.Br, hit));
                return;
            }
            var middle = labels.Length / 2;
            var upper = copiedIl.Create(OpCodes.Nop);
            copiedIl.Append(copiedIl.Create(OpCodes.Ldloc, copiedHash));
            copiedIl.Append(copiedIl.Create(OpCodes.Ldc_I4, unchecked((int)hashValue(labels[middle - 1]))));
            copiedIl.Append(copiedIl.Create(OpCodes.Bgt_Un, upper));
            Tree(labels[..middle]); copiedIl.Append(upper); Tree(labels[middle..]);
        }
        copiedIl.Append(copiedIl.Create(OpCodes.Ldc_I4_3)); copiedIl.Append(copiedIl.Create(OpCodes.Stloc, carried));
        copiedIl.Append(copiedIl.Create(OpCodes.Ldarg_0)); copiedIl.Append(copiedIl.Create(OpCodes.Call, hashing));
        copiedIl.Append(copiedIl.Create(OpCodes.Stloc, copiedHash));
        Tree(keys.OrderBy(hashValue).ToArray());
        copiedIl.Append(hit); copiedIl.Append(copiedIl.Create(OpCodes.Ret));
        copiedIl.Append(copiedReturn); copiedIl.Append(copiedIl.Create(OpCodes.Ldloc, carried));
        copiedIl.Append(copiedIl.Create(OpCodes.Add)); copiedIl.Append(copiedIl.Create(OpCodes.Ret));

        var order = owner.Methods.Single(m => m.Name == "CopyOrder");
        order.Body.Instructions.Clear(); order.Body.InitLocals = true;
        var orderIl = order.Body.GetILProcessor();
        var left = new VariableDefinition(module.TypeSystem.Int32);
        var right = new VariableDefinition(module.TypeSystem.Int32);
        order.Body.Variables.Add(left); order.Body.Variables.Add(right);
        var done = orderIl.Create(OpCodes.Ldloc, left);
        var starts = Enumerable.Range(0, 4).Select(_ => orderIl.Create(OpCodes.Nop)).ToArray();
        orderIl.Append(orderIl.Create(OpCodes.Ldarg_1)); orderIl.Append(orderIl.Create(OpCodes.Stloc, left));
        orderIl.Append(orderIl.Create(OpCodes.Ldarg_2)); orderIl.Append(orderIl.Create(OpCodes.Stloc, right));
        orderIl.Append(orderIl.Create(OpCodes.Ldarg_0)); orderIl.Append(orderIl.Create(OpCodes.Switch, starts));
        orderIl.Append(orderIl.Create(OpCodes.Br, done));
        for (var mode = 0; mode < starts.Length; mode++)
        {
            orderIl.Append(starts[mode]);
            var snapshot = new VariableDefinition(module.TypeSystem.Int32);
            order.Body.Variables.Add(snapshot);
            orderIl.Append(orderIl.Create(OpCodes.Ldloc, left)); orderIl.Append(orderIl.Create(OpCodes.Stloc, snapshot));
            orderIl.Append(orderIl.Create(OpCodes.Ldloc, right)); orderIl.Append(orderIl.Create(OpCodes.Stloc, left));
            if (mode == 3) { orderIl.Append(orderIl.Create(OpCodes.Call, owner.Methods.Single(m => m.Name == "Hit"))); orderIl.Append(orderIl.Create(OpCodes.Pop)); }
            orderIl.Append(orderIl.Create(OpCodes.Ldloc, mode == 2 ? left : snapshot)); orderIl.Append(orderIl.Create(OpCodes.Stloc, right));
            orderIl.Append(orderIl.Create(OpCodes.Br, done));
        }
        orderIl.Append(done); orderIl.Append(orderIl.Create(OpCodes.Ldc_I4, 1000)); orderIl.Append(orderIl.Create(OpCodes.Mul));
        orderIl.Append(orderIl.Create(OpCodes.Ldloc, right)); orderIl.Append(orderIl.Create(OpCodes.Add)); orderIl.Append(orderIl.Create(OpCodes.Ret));
        var input = Path.Combine(directory, "Input.dll");
        module.Write(input);
        var source = Decompilation.Decompile(input, directory, t => t.Name == "Probe", false, true).Single().Source;
        File.WriteAllText(Path.Combine(directory, "Probe.cs"), source);
        var rebuilt = Compile(source, "BranchResults.Rebuilt");
        var a = new Assertions();
        a.True(source.Contains("switch (key)", StringComparison.Ordinal) && !source.Contains("ComputeStringHash", StringComparison.Ordinal), "恢复字符串 switch");
        a.Equal(hashValue("costarring"), hashValue("liquid"), "独立碰撞输入确实落在同一哈希桶");
        foreach (var assembly in new[] { File.ReadAllBytes(input), rebuilt })
        {
            var type = System.Reflection.Assembly.Load(assembly).GetType("Probe")!;
            foreach (var methodName in new[] { "Select", "SelectCopied" })
            {
                var select = type.GetMethod(methodName)!.CreateDelegate<Func<string?, int, int>>();
                foreach (var key in keys.Cast<string?>().Concat([null, "", "ALPHA", "liquid", "unknown"]))
                {
                    type.GetField("Calls")!.SetValue(null, 0);
                    var accepted = keys.Contains(key);
                    a.Equal(accepted ? 42 : methodName == "SelectCopied" ? -4 : -7, select(key, -7), "标签、未知值、null 和哈希碰撞保留分支结果");
                    a.Equal(accepted ? 1 : 0, (int)type.GetField("Calls")!.GetValue(null)!, "选中主体只执行一次");
                }
            }
            var copy = type.GetMethod("CopyOrder")!.CreateDelegate<Func<int, int, int, int>>();
            foreach (var mode in Enumerable.Range(-1, 6))
            {
                type.GetField("Calls")!.SetValue(null, 0);
                a.Equal(mode is 0 or 1 or 3 ? 7002 : mode == 2 ? 7007 : 2007, copy(mode, 2, 7), "交换快照、顺序覆盖与未匹配出口保持区别");
                a.Equal(mode == 3 ? 1 : 0, (int)type.GetField("Calls")!.GetValue(null)!, "含调用的复制路径保留副作用");
            }
        }
        return a.Finish("source-branch-results");
    }
}
