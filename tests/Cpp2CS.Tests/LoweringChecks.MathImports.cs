using System.Collections.Immutable;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Output;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Tests.Execution;

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    private static void MathImportChecks(Assertions checks)
    {
        using var source = new CompiledSource("""
            public static class MathImports {
                public static float fmodf(float x, float y) => x % y;
                public static double fmod(double x, double y) => x % y;
                public static double modf(double x) => System.Math.Truncate(x);
                public static float atan2f(float x, float y) => (float)System.Math.Atan2(x, y);
                public static float powf(float x, float y) => (float)System.Math.Pow(2.0, 3.0);
                public static float exp2f(float x) => (float)System.Math.Pow(2.0, x);
                public static float sincosf(float x) => (float)System.Math.Sin(x) + (float)System.Math.Cos(x);
            }
            """);
        var model = new CecilModel(source.Module);
        var program = FloatFixture(model, "Math");
        var spec = InputCorpusChecks.Spec("arm64-v8a"); var layouts = new FieldLayouts(spec, 8, 8);
        var types = new ManagedTypes(program, layouts, 8); var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(), catalog);
        var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        foreach (var symbol in new[] { "fmodf", "fmod", "modf", "atan2f", "powf", "exp2f", "sincosf" })
        foreach (var mode in symbol is "modf" or "sincosf" ? new[] { "Valid", "Fraction", "Write", "Escape", "Partial", "Before", "Overlap" } : symbol == "powf" ? new[] { "Valid", "Undefined", "Dynamic", "Special" } : new[] { "Valid", "Undefined" })
        {
            if (symbol == "sincosf" && mode == "Fraction" || symbol == "modf" && mode == "Overlap") continue;
            int width = symbol is "modf" or "fmod" ? 64 : 32;
            var method = program.Methods.Single(m => m.Owner.Name == "MathImports" && m.Name == symbol);
            var t = new TermTable(); var block = new BlockIdentity(); var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64);
            var f = new FunctionBuilder(t, block, 64, new(frame)); var arguments = new List<SlotValue>();
            for (int i = 0; i < method.Parameters.Count; i++)
            {
                var slot = new AbstractSlot(SlotKind.Floating, i); var input = t.Atom(new EntryAtom(slot), 128); f.Inputs.Add(new(slot, input));
                var value = mode == "Undefined" ? t.Undefined(128) : symbol == "powf" && mode != "Dynamic"
                    ? t.Concat(t.Constant(BitConverter.SingleToUInt32Bits(mode == "Special" ? i == 0 ? float.NaN : 0 : i == 0 ? 2 : 3), 32), t.Constant(0, 96)) : input;
                arguments.Add(new(slot, value));
            }
            Term Add(int offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, frame, t.Constant(unchecked((ulong)(long)offset), 64));
            var first = Add(-32); var second = mode == "Overlap" ? first : Add(-16); var statements = new List<Statement>();
            Term Read(Term address, int bits)
            {
                var read = new ReadIdentity(); var value = t.Atom(new ResultAtom(read), bits); statements.Add(new MemoryRead(read, address, bits, value)); return value;
            }
            Term? before = mode == "Before" ? Read(first, width) : null;
            if (symbol is "modf" or "sincosf") arguments.Add(new(new(SlotKind.Integer), first));
            if (symbol == "sincosf") arguments.Add(new(new(SlotKind.Integer, 1), second));
            var id = new CallIdentity(); var returned = t.Atom(new ResultAtom(id), 128);
            statements.Add(new Call(id, new ImportedTarget(new(symbol)), [.. arguments], symbol == "sincosf" ? [] : [new(new(SlotKind.Floating), returned)]));
            if (mode == "Write") statements.Add(new MemoryWrite(new(), first, width, t.Constant(0, width)));
            if (mode == "Escape") statements.Add(new MemoryWrite(new(), Add(-64), 64, first));
            Term result = t.Slice(returned, 0, width);
            if (symbol is "modf" or "sincosf")
            {
                var output = Read(first, mode == "Partial" ? width / 2 : width);
                if (mode == "Partial") output = t.Apply(new CoreOperator(CoreOperation.ZeroExtend), width, output);
                result = mode == "Fraction" ? result : before ?? output;
                if (symbol == "sincosf") result = t.Apply(new CoreOperator(CoreOperation.FloatAdd), 32, output, Read(second, 32));
            }
            f.Blocks.Add(new(block, [], [.. statements], new Return([new(new(SlotKind.Floating), t.Concat(result, t.Constant(0, 128 - width)))])));
            var lowered = new IntegerLowering(f.Freeze(), MethodRef.Open(method), binder, types, calls: calls, effects: new ManagedCallEffects(calls), spec: spec).Run();
            checks.True((lowered.Body is not null) == (mode == "Valid"), symbol + " " + mode + "：" + lowered.Failure);
            if (mode == "Fraction") checks.True(lowered.Failure?.Reason.Code == "lowering.Math.FractionUsed", "modf 小数返回值单独归因");
            if (lowered.Body is not { } body) continue;
            var problems = emitter.Emit([body]); checks.True(problems.Count == 0, symbol + " 写出校验：" + string.Join(';', problems.Values));
            if (problems.Count != 0) continue;
            var expected = source.Method("MathImports", symbol);
            var tested = new Mono.Cecil.MethodDefinition(symbol + "Recovered", expected.Attributes, expected.ReturnType);
            foreach (var p in expected.Parameters) tested.Parameters.Add(new(p.Name, p.Attributes, p.ParameterType));
            expected.DeclaringType.Methods.Add(tested); tested.Body = skeleton.Method(method).Body;
            RebindStructBody(source.Module, tested);
            var comparison = CilComparison.Compare(expected, tested);
            checks.True(comparison.Status == CilComparisonStatus.Match, symbol + " 执行对照：" + comparison.Reason);
            using var image = new MemoryStream(); source.Module.Write(image);
            var executable = System.Reflection.Assembly.Load(image.ToArray());
            var executableType = executable.GetType("MathImports")!;
            var recoveredMethod = executableType.GetMethod(tested.Name)!;
            var referenceMethod = executableType.GetMethod(expected.Name)!;
            foreach (var pair in new[] { (-5.5, 2.0), (5.5, -2.0), (1.0, 0.0), (0.0, 0.0), (-0.0, 3.0) })
            {
                var input = method.Parameters.Select((_, i) => width == 32 ? (object)(float)(i == 0 ? pair.Item1 : pair.Item2) : i == 0 ? pair.Item1 : pair.Item2).ToArray();
                var actual = recoveredMethod.Invoke(null, input);
                var wanted = referenceMethod.Invoke(null, input);
                checks.True(Equals(actual, wanted), symbol + " 确定输入 " + pair + "：" + actual + " / " + wanted);

            }
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
}
