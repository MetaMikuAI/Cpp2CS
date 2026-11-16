using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Tests.Execution;

namespace Cpp2CS.Tests;

internal static partial class InliningChecks
{
    private static void EventAccessorChecks(Assertions checks)
    {
        ReadAnchoredEventChecks(checks);
        ArrayEventAccessorChecks(checks);
        CheckOriginChecks(checks);
        foreach (var mode in new[] { "Simple", "Reversed", "ExtraWrite", "DifferentArgument", "OtherUse", "SecondEntry" })
        {
            var f = new Fixture();
            var second = new FieldDef { Index = 2, Owner = f.Owner, Name = "Count", Type = f.Integer, Attributes = FieldAttributes.Private, Offset = 20, Token = 0x04000003 };
            f.Owner.Fields = [.. f.Owner.Fields, second]; ((List<FieldDef>)f.Program.Fields).Add(second);
            var count = new FieldRef(second, f.OwnerType);
            var outer = f.Method(f.Owner, "Reset", true, false, []);
            var target = f.Method(f.Owner, "Slow", true, true, [f.Integer]);
            var caller = f.Method(f.Caller, "Use", mode != "OtherUse", true, [f.OwnerType]);
            var self = new ArgumentValue(-1, f.OwnerType, 64);
            var version = new FieldValue(self, f.Field, f.Integer, 32); var size = new FieldValue(self, count, f.Integer, 32);
            var oldVersion = new LocalValue(new(0), f.Integer, 32); var oldSize = new LocalValue(new(1), f.Integer, 32);
            var zero = new ConstantValue(0, f.Integer, 32);
            var template = new ManagedBody(MethodRef.Open(outer), [
                new(0, [new ManagedAssignment(0, oldVersion, version), new ManagedAssignment(0, oldSize, size),
                    new ManagedStore(1, version, new BinaryValue(BinaryOperator.Add, oldVersion, new ConstantValue(1, f.Integer, 32), f.Integer, 32)),
                    new ManagedStore(2, size, zero), new ManagedBranch(3, new ComparisonValue(ComparisonKind.SignedGreater, oldSize, zero, f.Types.Boolean), new(1, []), new(2, []))]),
                new(1, [new ManagedCall(4, new(MethodRef.Open(target), null, [oldSize], false), null), new ManagedReturn(5, null)]),
                new(2, [new ManagedReturn(6, null)])]);
            checks.True(AccessorTemplates.Read(template).Template?.Events?.Paths.Count == 2, "带写入和调用的条件模板提取：" + mode);
            var t = new TermTable(); var entry = new BlockIdentity(); var yes = new BlockIdentity(); var no = new BlockIdentity(); var join = new BlockIdentity();
            var builder = new FunctionBuilder(t, entry, 64, new(t.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var input = t.Atom(new EntryAtom(new(SlotKind.Integer)), 64); builder.Inputs.Add(new(new(SlotKind.Integer), input));
            Term Address(int offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, input, t.Constant(offset, 64));
            MemoryRead Read(int offset)
            { var id = new ReadIdentity(); return new(id, Address(offset), 32, t.Atom(new ResultAtom(id), 32)); }
            var a = Read(16); var b = Read(20);
            var condition = t.Apply(new CoreOperator(CoreOperation.SignedLess), 1, t.Constant(0, 32), b.Result);
            bool reversed = mode == "Reversed";
            if (reversed) condition = t.Apply(new CoreOperator(CoreOperation.Not), 1, condition);
            var statements = new List<Statement> { a, b,
                new MemoryWrite(new(), Address(16), 32, t.Apply(new CoreOperator(CoreOperation.Add), 32, a.Result, t.Constant(1, 32))),
                new MemoryWrite(new(), Address(20), 32, t.Constant(0, 32)) };
            builder.Blocks.Add(new(entry, [], statements.ToImmutableArray(), new Branch(condition, reversed ? no : yes, reversed ? yes : no)));
            var arg = mode == "DifferentArgument" ? t.Constant(3, 32) : b.Result;
            builder.Blocks.Add(new(yes, [], [new Call(new(), new ImageFunction(10),
                [new(new(SlotKind.Integer), t.Concat(arg, t.Constant(0, 32))), new(new(SlotKind.Integer, 1), t.Constant(0, 64))], [])], new Jump(join)));
            builder.Blocks.Add(new(no, [], mode == "ExtraWrite" ? [new MemoryWrite(new(), Address(16), 32, t.Constant(8, 32))] : [], new Jump(join)));
            builder.Blocks.Add(new(join, [], [], new Return(mode == "OtherUse" ? [new(new(SlotKind.Integer), t.Concat(b.Result, t.Constant(0, 32)))] : [])));
            if (mode == "SecondEntry")
            {
                var root = new BlockIdentity(); builder = CopyWithEntry(builder, t, root);
                builder.Blocks.Add(new(root, [], [], new Branch(t.Apply(new CoreOperator(CoreOperation.Equal), 1, input, t.Constant(0, 64)), entry, yes)));
            }
            var catalog = RuntimeFunctionCatalog.Select(f.Spec.Layout.UnityVersion, f.Spec.Layout.Triple, f.Spec.Layout.DataModel);
            var calls = new CallNamingQuery(f.Binder, new NamingChecks.Map([new(MethodRef.Open(target), BindingEntryKind.Ordinary)]), new NamingChecks.RuntimeMap(), catalog);
            var lowered = new IntegerLowering(builder.Freeze(), MethodRef.Open(caller), f.Binder, f.Types, calls: calls,
                effects: new ManagedCallEffects(calls), spec: f.Spec, accessors: new(f.Types, new CachedAccessorTemplates(m => m == outer ? template : null))).Run();
            if (mode is "Simple" or "Reversed")
            {
                checks.True(lowered.Body is not null, "事件区域下降：" + mode + " " + lowered.Failure);
                if (lowered.Body is not { } body) continue;
                var recovered = body.Blocks.SelectMany(bk => bk.Statements).ToArray();
                checks.True(recovered.OfType<ManagedCall>().Count(c => c.Inlined && c.Invocation.Method.Method == outer) == 1
                    && !recovered.Any(s => s is ManagedStore or ManagedBranch), "入口写入和各臂一并替换：" + mode);
                using var emission = new EmissionFixture(f);
                checks.True(emission.Emitter.Emit([template, body]).Count == 0, "带事件条件区域通过 CIL 检查：" + mode);
                using var source = new CompiledSource("""
                    public class Owner {
                        private int Value;
                        private int Count;
                        private static int Shared;
                        public void Reset() { int v = Value, n = Count; Value = v + 1; Count = 0; if (n > 0) Slow(n); }
                        public static void Slow(int n) { Shared = n; }
                        public static void Expanded(Owner value) { int v = value.Value, n = value.Count; value.Value = v + 1; value.Count = 0; if (n > 0) Slow(n); }
                    }
                    public static class Caller { public static void UseOut(Owner value) { value.Reset(); } }
                    """);
                var output = source.Method("Caller", "UseOut"); output.Body = emission.Method(caller).Body;
                var core = source.Module.TypeSystem.Object.Resolve().Module;
                Mono.Cecil.TypeReference MapType(Mono.Cecil.TypeReference type) => source.Module.ImportReference(source.Module.GetType(type.FullName) ?? core.GetType(type.FullName));
                foreach (var local in output.Body.Variables) local.VariableType = MapType(local.VariableType);
                foreach (var instruction in output.Body.Instructions) instruction.Operand = instruction.Operand switch
                {
                    Mono.Cecil.MethodReference method => source.Module.ImportReference(source.Module.GetType(method.DeclaringType.FullName).Methods.Single(m => m.FullName == method.FullName)),
                    Mono.Cecil.TypeReference type => MapType(type), Mono.Cecil.ParameterDefinition parameter => output.Parameters[parameter.Index], _ => instruction.Operand,
                };
                var comparison = CilComparison.Compare(source.Method("Owner", "Expanded"), output, cases: 64);
                checks.True(comparison.Status == CilComparisonStatus.Match && comparison.CompletedCases == 64,
                    "带事件区域逐输入比较写入、调用和结局：" + mode + " " + comparison);
                checks.True(comparison.Coverage is { Branches.Length: > 0 } coverage && coverage.Branches.All(bk => bk.Directions.All(d => d)),
                    "执行对照覆盖条件的两臂：" + mode);
            }
            else checks.True(lowered.Body is null, "带事件区域反例保持洞：" + mode + " " + lowered.Failure);
        }
    }
    private static void ReadAnchoredEventChecks(Assertions checks)
    {
        var f = new Fixture();
        var outer = f.Method(f.Owner, "ConditionalCall", true, false, []);
        var target = f.Method(f.Owner, "Sink", true, true, [f.Integer]);
        var caller = f.Method(f.Caller, "UseConditionalCall", true, true, [f.OwnerType]);
        var self = new ArgumentValue(-1, f.OwnerType, 64);
        var field = new FieldValue(self, f.Field, f.Integer, 32);
        var local = new LocalValue(new(0), f.Integer, 32);
        var template = new ManagedBody(MethodRef.Open(outer), [
            new(0, [new ManagedAssignment(0, local, field), new ManagedBranch(1,
                new ComparisonValue(ComparisonKind.SignedGreater, local, new ConstantValue(0, f.Integer, 32), f.Types.Boolean), new(1, []), new(2, []))]),
            new(1, [new ManagedCall(2, new(MethodRef.Open(target), null, [local], false), null), new ManagedReturn(3, null)]),
            new(2, [new ManagedReturn(4, null)])]);
        var t = new TermTable(); var entry = new BlockIdentity(); var yes = new BlockIdentity(); var no = new BlockIdentity(); var join = new BlockIdentity();
        var builder = new FunctionBuilder(t, entry, 64, new(t.Atom(new RootAtom(AddressRoot.Frame), 64)));
        var input = t.Atom(new EntryAtom(new(SlotKind.Integer)), 64); builder.Inputs.Add(new(new(SlotKind.Integer), input));
        var id = new ReadIdentity(); var value = t.Atom(new ResultAtom(id), 32);
        var address = t.Apply(new CoreOperator(CoreOperation.Add), 64, input, t.Constant(16, 64));
        builder.Blocks.Add(new(entry, [], [new MemoryRead(id, address, 32, value)],
            new Branch(t.Apply(new CoreOperator(CoreOperation.SignedLess), 1, t.Constant(0, 32), value), yes, no)));
        builder.Blocks.Add(new(yes, [], [new Call(new(), new ImageFunction(10),
            [new(new(SlotKind.Integer), t.Concat(value, t.Constant(0, 32))), new(new(SlotKind.Integer, 1), t.Constant(0, 64))], [])], new Jump(join)));
        builder.Blocks.Add(new(no, [], [], new Jump(join))); builder.Blocks.Add(new(join, [], [], new Return([])));
        var catalog = RuntimeFunctionCatalog.Select(f.Spec.Layout.UnityVersion, f.Spec.Layout.Triple, f.Spec.Layout.DataModel);
        var calls = new CallNamingQuery(f.Binder, new NamingChecks.Map([new(MethodRef.Open(target), BindingEntryKind.Ordinary)]), new NamingChecks.RuntimeMap(), catalog);
        var lowered = new IntegerLowering(builder.Freeze(), MethodRef.Open(caller), f.Binder, f.Types, calls: calls,
            effects: new ManagedCallEffects(calls), spec: f.Spec, accessors: new(f.Types, new CachedAccessorTemplates(m => m == outer ? template : null))).Run();
        checks.True(lowered.Body is not null, "无返回值的事件模板可以由读取锚点发现：" + lowered.Failure);
        if (lowered.Body is not { } body) return;
        checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>() is var recovered
            && recovered.Count(c => c.Inlined && c.Invocation.Method.Method == outer) == 1,
            "只含条件调用的区域替换为外层一次调用");
        using var emission = new EmissionFixture(f);
        checks.True(emission.Emitter.Emit([template, body]).Count == 0, "读取锚点的无返回条件模板通过 CIL 检查");
    }
    private static FunctionBuilder CopyWithEntry(FunctionBuilder source, TermTable terms, BlockIdentity entry)
    {
        var copy = new FunctionBuilder(terms, entry, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
        copy.Inputs.AddRange(source.Inputs); copy.Blocks.AddRange(source.Blocks); return copy;
    }
}
