using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using SR = System.Reflection;

namespace Cpp2CS.Tests.Execution;

internal static class FloatOrderCheck
{
    [Command("float-order", "浮点有序、无序和有序不等比较的 CIL 与重编译源码", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var original = facts.Model;
        var types = new ManagedTypes(original, facts.Layouts);
        var module = new TypeDef { Index = original.Types.Count, Assembly = "FloatOrder.dll", Namespace = "", Name = "<Module>",
            Token = 0, Attributes = SR.TypeAttributes.NotPublic, IsValueType = false, IsEnum = false };
        var owner = new TypeDef { Index = original.Types.Count + 1, Assembly = module.Assembly, Namespace = "Tests", Name = "Comparison",
            Token = 0, Attributes = SR.TypeAttributes.Public | SR.TypeAttributes.Abstract | SR.TypeAttributes.Sealed,
            IsValueType = false, IsEnum = false, BaseType = types.Object };
        var cases = (from width in new[] { 32, 64 } from condition in new[] { Cond.FOrdered, Cond.FUnordered, Cond.FNe }
            select (Width: width, Condition: condition)).ToArray();
        owner.Methods = cases.Select((sample, index) => new MethodDef { Index = original.Methods.Count + index, Owner = owner,
            Name = $"{sample.Condition}_{sample.Width}", Token = 0, Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static,
            ImplAttributes = SR.MethodImplAttributes.IL, Slot = -1, ReturnType = types.Boolean,
            Parameters = new[] { "left", "right" }.Select(name => new ParameterDef(name, sample.Width == 32 ? types.Single : types.Double, 0, null, false)).ToArray() }).ToArray();
        var bodies = owner.Methods.Select((method, index) => new ManagedBody(new(method, [], []), [new(0, [new ManagedReturn(0,
            new ComparisonValue(cases[index].Condition, new ArgumentValue(0, method.Parameters[0].Type, cases[index].Width),
                new ArgumentValue(1, method.Parameters[1].Type, cases[index].Width), types.Boolean))])])).ToArray();
        var assembly = new AssemblyDef { Name = owner.Assembly, AssemblyName = "FloatOrder", Version = new(1, 0), Culture = "", PublicKey = [], Types = [module, owner] };
        var model = new ProgramModel { Image = original.Image, MetadataVersion = original.MetadataVersion,
            Assemblies = [.. original.Assemblies, assembly], Types = [.. original.Types, module, owner], Methods = [.. original.Methods, .. owner.Methods],
            Fields = original.Fields, RuntimeTypes = original.RuntimeTypes, MethodSpecs = original.MethodSpecs, FieldRefs = original.FieldRefs,
            StringLiterals = original.StringLiterals, Code = original.Code };
        var directory = Path.GetFullPath("artifacts/float-order.local");
        Directory.CreateDirectory(directory);
        var loaded = new List<SR.Assembly>();
        var a = new Assertions();
        foreach (var policy in new[] { EmissionPolicy.Recovered, EmissionPolicy.Source })
        {
            var skeleton = new Skeleton(model);
            a.Equal(0, new FullBodyEmitter(skeleton, types).Emit(bodies, policy).Count, "浮点比较可写出");
            var path = Path.Combine(directory, policy + ".dll");
            skeleton.Assembly(owner.Assembly).Write(path);
            loaded.Add(SR.Assembly.Load(File.ReadAllBytes(path)));
        }
        var source = FullDecompilation.Decompile(Path.Combine(directory, "Source.dll"), directory, t => t.FullName == "Tests.Comparison", false, true).Single().Source;
        File.WriteAllText(Path.Combine(directory, "Comparison.cs"), source);
        var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator).Select(p => MetadataReference.CreateFromFile(p));
        var compilation = CSharpCompilation.Create("FloatOrder.Rebuilt", [CSharpSyntaxTree.ParseText(source)], references,
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, optimizationLevel: OptimizationLevel.Release));
        using var stream = new MemoryStream();
        var emitted = compilation.Emit(stream);
        if (!emitted.Success) throw new InvalidOperationException(string.Join('\n', emitted.Diagnostics));
        loaded.Add(SR.Assembly.Load(stream.ToArray()));
        double[] values = [double.NaN, double.NegativeInfinity, -1, -0.0, 0, 1, double.PositiveInfinity];
        foreach (var target in loaded)
            foreach (var sample in cases)
                foreach (var left in values)
                    foreach (var right in values)
                    {
                        var unordered = double.IsNaN(left) || double.IsNaN(right);
                        var expected = sample.Condition == Cond.FUnordered ? unordered
                            : sample.Condition == Cond.FOrdered ? !unordered : !unordered && left != right;
                        var actual = (bool)target.GetType("Tests.Comparison")!.GetMethod($"{sample.Condition}_{sample.Width}")!.Invoke(null,
                            [sample.Width == 32 ? (object)(float)left : left, sample.Width == 32 ? (object)(float)right : right])!;
                        a.Equal(expected, actual, "NaN、无穷、正负零与有限值比较一致");
                    }
        return a.Finish("float-order");
    }
}
