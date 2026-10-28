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
            var select = type.GetMethod("Select")!.CreateDelegate<Func<string?, int, int>>();
            foreach (var key in keys.Cast<string?>().Concat([null, "", "ALPHA", "liquid", "unknown"]))
            {
                type.GetField("Calls")!.SetValue(null, 0);
                var accepted = keys.Contains(key);
                a.Equal(accepted ? 42 : -7, select(key, -7), "标签、未知值、null 和哈希碰撞保留分支结果");
                a.Equal(accepted ? 1 : 0, (int)type.GetField("Calls")!.GetValue(null)!, "选中主体只执行一次");
            }
        }
        return a.Finish("source-branch-results");
    }
}
