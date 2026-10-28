using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Mono.Cecil.Cil;
using SR = System.Reflection;

namespace Cpp2CS.Tests.Execution;

internal static class SourceIntegerComparisonCheck
{
    [Command("source-integer-comparisons", "32 位关系比较的原始 CIL、源码 CIL 与重编译 C# 边界", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var original = facts.Model;
        var types = new ManagedTypes(original, facts.Layouts);
        var moduleType = new TypeDef { Index = original.Types.Count, Assembly = "IntegerComparison.dll", Namespace = "", Name = "<Module>",
            Token = 0, Attributes = SR.TypeAttributes.NotPublic, IsValueType = false, IsEnum = false };
        var owner = new TypeDef { Index = original.Types.Count + 1, Assembly = moduleType.Assembly, Namespace = "Tests", Name = "Comparison",
            Token = 0, Attributes = SR.TypeAttributes.Public | SR.TypeAttributes.Abstract | SR.TypeAttributes.Sealed, IsValueType = false,
            IsEnum = false, BaseType = types.Object };
        var methods = new List<(MethodDef Method, Cond Condition, bool Signed)>();
        var bodies = new List<ManagedBody>();
        foreach (var signed in new[] { false, true })
            foreach (var condition in new[] { Cond.Slt, Cond.Sle, Cond.Sgt, Cond.Sge, Cond.Ult, Cond.Ule, Cond.Ugt, Cond.Uge })
            {
                var type = signed ? types.Int32 : types.UInt32;
                var method = new MethodDef { Index = original.Methods.Count + methods.Count, Owner = owner, Name = $"{condition}_{signed}", Token = 0,
                    Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static, ImplAttributes = SR.MethodImplAttributes.IL, Slot = -1,
                    ReturnType = types.Boolean, Parameters = [new("left", type, 0, null, false), new("right", type, 0, null, false)] };
                methods.Add((method, condition, signed));
                bodies.Add(new(new(method, [], []), [new(0, [new ManagedReturn(0,
                    new ComparisonValue(condition, new ArgumentValue(0, type, 32), new ArgumentValue(1, type, 32), types.Boolean))])]));
            }
        owner.Methods = methods.Select(m => m.Method).ToArray();
        var assembly = new AssemblyDef { Name = owner.Assembly, AssemblyName = "IntegerComparison", Version = new(1, 0), Culture = "", PublicKey = [], Types = [moduleType, owner] };
        var model = new ProgramModel { Image = original.Image, MetadataVersion = original.MetadataVersion,
            Assemblies = [.. original.Assemblies, assembly], Types = [.. original.Types, moduleType, owner], Methods = [.. original.Methods, .. owner.Methods],
            Fields = original.Fields, RuntimeTypes = original.RuntimeTypes, MethodSpecs = original.MethodSpecs, FieldRefs = original.FieldRefs,
            StringLiterals = original.StringLiterals, Code = original.Code };
        var directory = Path.GetFullPath("artifacts/source-integer-comparisons");
        Directory.CreateDirectory(directory);
        var loaded = new List<SR.Assembly>();
        var a = new Assertions();
        foreach (var policy in new[] { EmissionPolicy.Recovered, EmissionPolicy.Source })
        {
            var skeleton = new Skeleton(model);
            a.Equal(0, new BodyEmitter(skeleton, types) { Policy = policy }.Emit(bodies).Count, "有无符号参数的比较均可写出");
            if (policy == EmissionPolicy.Source)
                a.True(methods.All(m => skeleton.Method(m.Method).Body.Instructions.All(i => i.OpCode.Code is not (Code.Conv_I4 or Code.Conv_U4))),
                    "源码比较不依赖重复 int32 转换");
            var path = Path.Combine(directory, policy + ".dll");
            skeleton.Assembly(owner.Assembly).Write(path);
            loaded.Add(SR.Assembly.Load(File.ReadAllBytes(path)));
        }
        var source = Decompilation.Decompile(Path.Combine(directory, "Source.dll"), directory, t => t.FullName == "Tests.Comparison", false, true).Single().Source;
        File.WriteAllText(Path.Combine(directory, "Comparison.cs"), source);
        var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator).Select(p => MetadataReference.CreateFromFile(p));
        var compilation = CSharpCompilation.Create("IntegerComparison.Rebuilt", [CSharpSyntaxTree.ParseText(source)], references,
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, optimizationLevel: OptimizationLevel.Release));
        using var stream = new MemoryStream();
        var emitted = compilation.Emit(stream);
        if (!emitted.Success) throw new InvalidOperationException(string.Join('\n', emitted.Diagnostics));
        loaded.Add(SR.Assembly.Load(stream.ToArray()));
        uint[] samples = [0, 1, 7, int.MaxValue, 0x80000000, uint.MaxValue - 1, uint.MaxValue];
        foreach (var target in loaded)
            foreach (var (method, condition, signed) in methods)
                foreach (var left in samples)
                    foreach (var right in samples)
                    {
                        var expected = condition switch
                        {
                            Cond.Slt => unchecked((int)left) < unchecked((int)right), Cond.Sle => unchecked((int)left) <= unchecked((int)right),
                            Cond.Sgt => unchecked((int)left) > unchecked((int)right), Cond.Sge => unchecked((int)left) >= unchecked((int)right),
                            Cond.Ult => left < right, Cond.Ule => left <= right, Cond.Ugt => left > right, Cond.Uge => left >= right,
                            _ => throw new NotSupportedException(),
                        };
                        var actual = (bool)target.GetType("Tests.Comparison")!.GetMethod(method.Name)!.Invoke(null,
                            [signed ? (object)unchecked((int)left) : left, signed ? (object)unchecked((int)right) : right])!;
                        a.Equal(expected, actual, "零、负数和符号边界的关系结果一致");
                    }
        return a.Finish("source-integer-comparisons");
    }
}
