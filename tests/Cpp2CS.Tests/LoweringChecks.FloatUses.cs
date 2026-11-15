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
    private static void FloatUseChecks(Assertions checks, ProgramModel primitives)
    {
        using var source = new CompiledSource("""
            public struct FloatLeaf { public float X; }
            public static class FloatUses {
                public static float Take(float x) => x;
                public static double TakeDouble(double x) => x;
                public static void Observe(int x) { }
                public static void Touch(ref FloatLeaf x) { }
                public static float Select(int c, float a) => Take(c != 0 ? 1f : 0f);
                public static float Merge(int c, float a) { float x; if (c != 0) x = 1f; else x = 0f; return Take(x); }
                public static float Mixed(int c, float a) { float x; if (c != 0) x = 1f; else x = a; return Take(x); }
                public static float Minimum(int c, float a) => Take(a > 2.5f ? 2.5f : a);
                public static float RoundTrip(int c, float a) => Take(System.BitConverter.Int32BitsToSingle(System.BitConverter.SingleToInt32Bits(a)));
                public static float FrameLeaf(int c, float a) { var x = new FloatLeaf { X = c != 0 ? 1f : a }; Touch(ref x); return Take(x.X); }
                public static float CachedSelect(int c, float a) { float x = c != 0 ? 1f : 0f; Observe(System.BitConverter.SingleToInt32Bits(x)); return Take(x); }
                public static float CachedMerge(int c, float a) { float x; if (c != 0) x = 1f; else x = a; Observe(System.BitConverter.SingleToInt32Bits(x)); return Take(x); }
                public static float Store(int c, ref float field, float a) { field = c != 0 ? 1f : a; return Take(field); }
                public static double DoubleStore(int c, ref double field, double a) { field = c != 0 ? 1.0 : a; return TakeDouble(field); }
                public static float Return(int c, float a) => c != 0 ? 1f : 0f;
                public static double DoubleReturn(int c, double a) => c != 0 ? 1.0 : 0.0;
                public static double DoubleSelect(int c, double a) => TakeDouble(c != 0 ? 1.0 : 0.0);
                public static double DoubleMerge(int c, double a) { double x; if (c != 0) x = 1.0; else x = a; return TakeDouble(x); }
            }
            """);
        var model = new CecilModel(source.Module);
        var program = FloatFixture(model, "BitConverter");
        var spec = InputCorpusChecks.Spec("arm64-v8a"); var layouts = new FieldLayouts(spec, 8, 8);
        var types = new ManagedTypes(program, layouts, 8); var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var methods = program.Methods.Where(m => m.Owner.Name == "FloatUses").ToDictionary(m => m.Name);
        var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        string[] modes = ["Select", "Merge", "Mixed", "Minimum", "RoundTrip", "FrameLeaf", "CachedSelect", "CachedMerge", "DoubleSelect", "DoubleMerge", "Store", "DoubleStore", "Return", "DoubleReturn"];
        foreach (var mode in modes)
        foreach (bool invalid in new[] { false, true })
        {
            bool wide = mode.StartsWith("Double", StringComparison.Ordinal); int width = wide ? 64 : 32;
            var t = new TermTable(); var entry = new BlockIdentity(); var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64);
            var f = new FunctionBuilder(t, entry, 64, new(frame));
            Term Input(SlotKind kind, int index = 0) { var slot = new AbstractSlot(kind, index); var value = t.Atom(new EntryAtom(slot), kind == SlotKind.Floating ? 128 : 64); f.Inputs.Add(new(slot, value)); return value; }
            Term Op(CoreOperation op, int bits, params Term[] operands) => t.Apply(new CoreOperator(op), bits, operands);
            var condition = Op(CoreOperation.NotEqual, 1, t.Slice(Input(SlotKind.Integer), 0, 32), t.Constant(0, 32));
            var a = t.Slice(Input(SlotKind.Floating), 0, width);
            var one = t.Constant(wide ? BitConverter.DoubleToUInt64Bits(1) : BitConverter.SingleToUInt32Bits(1), width);
            Term other = mode is "Mixed" or "CachedMerge" or "DoubleMerge" or "Store" or "DoubleStore" ? a : t.Constant(0, width);
            if (invalid) other = t.Undefined(width);
            Term value = mode == "RoundTrip" ? invalid ? t.Undefined(width) : a
                : mode == "FrameLeaf" ? invalid ? t.Undefined(width) : Op(CoreOperation.Select, width, condition, one, a)
                : mode == "Minimum" ? Op(CoreOperation.FloatMinimum, width, a, invalid ? Op(CoreOperation.FloatNegate, width, a) : t.Constant(BitConverter.SingleToUInt32Bits(2.5f), width))
                : Op(CoreOperation.Select, width, condition, one, other);
            var block = entry;
            if (mode is "Merge" or "Mixed" or "CachedMerge" or "DoubleMerge")
            {
                var yes = new BlockIdentity(); var no = new BlockIdentity(); block = new BlockIdentity(); var merge = new MergeIdentity();
                f.Blocks.Add(new(entry, [], [], new Branch(condition, yes, no)));
                f.Blocks.Add(new(yes, [], [], new Jump(block))); f.Blocks.Add(new(no, [], [], new Jump(block)));
                value = t.Atom(new ResultAtom(merge), width);
                f.Blocks.Add(new(block, [new(merge, value, [new(yes, one), new(no, other)])], [], new Return([])));
            }
            var statements = new List<Statement>();
            var map = new Dictionary<ulong, BindingEntry>();
            Term Invoke(string name, ImmutableArray<SlotValue> arguments, bool result = true)
            {
                ulong address = (ulong)map.Count + 10; map.Add(address, new(MethodRef.Open(methods[name]), BindingEntryKind.Ordinary));
                var id = new CallIdentity(); var output = t.Atom(new ResultAtom(id), 128);
                statements.Add(new Call(id, new ImageFunction(address), arguments, result ? [new(new(SlotKind.Floating), output)] : []));
                return t.Slice(output, 0, width);
            }
            if (mode.StartsWith("Cached", StringComparison.Ordinal))
                Invoke("Observe", [new(new(SlotKind.Integer), t.Concat(value, t.Constant(0, 32))), new(new(SlotKind.Integer, 1), t.Constant(0, 64))], false);
            if (mode == "FrameLeaf")
            {
                var address = Op(CoreOperation.Add, 64, frame, t.Constant(unchecked((ulong)-16L), 64));
                statements.Add(new MemoryWrite(new(), address, 32, value));
                Invoke("Touch", [new(new(SlotKind.Integer), address), new(new(SlotKind.Integer, 1), t.Constant(0, 64))], false);
                var id = new ReadIdentity(); value = t.Atom(new ResultAtom(id), 32); statements.Add(new MemoryRead(id, address, 32, value));
            }
            if (mode is "Store" or "DoubleStore")
            {
                var address = Input(SlotKind.Integer, 1);
                statements.Add(new MemoryWrite(new(), address, width, value));
                var read = new ReadIdentity(); var loaded = t.Atom(new ResultAtom(read), width); statements.Add(new MemoryRead(read, address, width, loaded)); value = loaded;
            }
            if (mode is not ("Return" or "DoubleReturn")) value = Invoke(wide ? "TakeDouble" : "Take", [new(new(SlotKind.Floating), t.Concat(value, t.Constant(0, 128 - width))), new(new(SlotKind.Integer), t.Constant(0, 64))]);
            var last = new Block(block, [], [.. statements], new Return([new(new(SlotKind.Floating), t.Concat(value, t.Constant(0, 128 - width)))]));
            int existing = f.Blocks.FindIndex(b => b.Identity == block);
            if (existing >= 0) f.Blocks[existing] = last with { Merges = f.Blocks[existing].Merges }; else f.Blocks.Add(last);
            var calls = new CallNamingQuery(binder, new FloatUseCodeMap(map), new NamingChecks.RuntimeMap(), catalog);
            var lowered = new IntegerLowering(f.Freeze(), MethodRef.Open(methods[mode]), binder, types, calls: calls,
                effects: new ManagedCallEffects(calls), spec: spec).Run();
            checks.True((lowered.Body is not null) == !invalid, mode + (invalid ? " 证据不足保持洞：" : " 浮点实参下降：") + lowered.Failure);
            if (lowered.Body is not { } body) continue;
            var problems = emitter.Emit([body]); checks.True(problems.Count == 0, mode + " 不交出 int32 浮点实参：" + string.Join(';', problems.Values));
            if (problems.Count != 0) continue;
            var expected = source.Method("FloatUses", mode);
            var tested = new Mono.Cecil.MethodDefinition(mode + "Recovered", expected.Attributes, expected.ReturnType);
            foreach (var p in expected.Parameters) tested.Parameters.Add(new(p.Name, p.Attributes, p.ParameterType));
            expected.DeclaringType.Methods.Add(tested); tested.Body = skeleton.Method(methods[mode]).Body;
            RebindStructBody(source.Module, tested);
            var comparison = CilComparison.Compare(expected, tested);
            checks.True(comparison.Status == CilComparisonStatus.Match, mode + " 执行对照：" + comparison.Reason);
        }
        var reference = MethodRef.Open(methods["Select"]);
        var integer = new ConstantValue(0x3f800000, types.Int32, 32);
        var number = new ConstantValue(0x3f800000, types.Single, 32);
        var floatLocal = new LocalValue(new(100), types.Single, 32);
        var target = new StaticFieldValue(new FieldRef(new FieldDef { Index = 0, Owner = methods["Select"].Owner,
            Name = "Number", Type = types.Single, Offset = 0, Attributes = System.Reflection.FieldAttributes.Public | System.Reflection.FieldAttributes.Static }, reference.DeclaringType), types.Single, 32);
        ManagedStatement[] malformed = [new ManagedReturn(0, integer), new ManagedStore(0, target, integer),
            new ManagedAssignment(0, floatLocal, integer), new ManagedCall(0, new(MethodRef.Open(methods["Take"]), null, [integer], false), null),
            new ManagedReturn(0, new ChoiceValue(new ConstantValue(1, types.Boolean, 1), integer, number, types.Single, 32)),
            new ManagedJump(0, new(1, [new(floatLocal, integer)])),
            new ManagedReturn(0, new ConversionValue(ConversionKind.Bitcast, integer, types.Double, 64)),
            new ManagedReturn(0, new ArgumentValue(0, types.Single, 32)),
            new ManagedReturn(0, new ConversionValue(ConversionKind.Bitcast, target with { Type = types.Int32 }, types.Single, 32)),
            // 整数扩展的结果声明成浮点类型：类型字段相符，栈上却是整数。
            new ManagedCall(0, new(MethodRef.Open(methods["Take"]), null, [new ConversionValue(ConversionKind.ZeroExtend, integer, types.Single, 32)], false), null),
            new ManagedBranch(0, new ConstantValue(1, types.Boolean, 1), new(1, [new(floatLocal, number)]),
                new(1, [new(floatLocal with { Type = types.Int32 }, integer)]))];
        foreach (var statement in malformed)
            checks.True(FloatingTypeContract.Check(new(reference, [new ManagedBlock(0, [statement])]), types)?.Code == "lowering.Float.Type",
                statement.GetType().Name + " 的错误浮点类型由恢复层出口拦下");
        checks.True(FloatingTypeContract.Check(new(reference, [new ManagedBlock(0, [new ManagedReturn(0, number)])]), types) is null,
            "浮点常量通过恢复层类型核对");
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
    private sealed class FloatUseCodeMap(Dictionary<ulong, BindingEntry> entries) : IBindingCodeMap
    {
        public ImmutableArray<BindingEntry> At(ulong entry) => entries.TryGetValue(entry, out var found) ? [found] : [];
    }
}
