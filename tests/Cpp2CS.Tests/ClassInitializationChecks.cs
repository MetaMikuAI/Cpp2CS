using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Structure;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Tests;

internal static class ClassInitializationChecks
{
    private sealed class RuntimeMap(RuntimeFunction initialize, RuntimeFunction allocate, RuntimeFunction metadata) : IRuntimeFunctionMap
    {
        public RuntimeFunction? Find(CallTarget target) => target is ImageFunction { EntryOffset: 20 } ? initialize
            : target is ImageFunction { EntryOffset: 30 } ? allocate
            : target is ImageFunction { EntryOffset: 40 } ? metadata : null;
    }
    public const string Command = "class-initialization";
    public static int Run()
    {
        var checks = new Assertions(); var spec = InputCorpusChecks.Spec("arm64-v8a");
        var layouts = new FieldLayouts(spec, 8, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var runtime = catalog.Functions.First(f => f.Operation.Name == "InitializeClassPrecise" && f.Signature is not null);
        TypeDef Type(int id, string name, string assembly = "test", string ns = "", bool value = false) => new()
        { Index = id, Assembly = assembly, Namespace = ns, Name = name, Token = 0, Attributes = TypeAttributes.Public, IsValueType = value, IsEnum = false, Size = 32, PackingSize = 0, ClassSizeIsDefault = true };
        var owner = Type(1, "Owner"); var other = Type(2, "Other");
        var integer = new DefinitionRef(Type(3, "Int32", "mscorlib.dll", "System", true), []);
        var nothing = new DefinitionRef(Type(4, "Void", "mscorlib.dll", "System", true), []);
        MethodDef Method(TypeDef type, string name, bool isStatic) => new()
        { Index = type.Index, Owner = type, Name = name, Token = 0, Attributes = (isStatic ? MethodAttributes.Static : MethodAttributes.Public) |
                (name is ".ctor" or ".cctor" ? MethodAttributes.SpecialName | MethodAttributes.RTSpecialName : 0),
            ImplAttributes = 0, Slot = -1, ReturnType = nothing, Parameters = [] };
        foreach (var type in new[] { owner, other })
        {
            type.Fields = [new() { Index = type.Index, Owner = type, Name = "Value", Type = integer, Offset = 0, Attributes = FieldAttributes.Static }];
            type.Methods = [Method(type, ".cctor", true)];
        }
        var facts = NamingFacts.Empty with { Slots = new Dictionary<ulong, Outcome<MetadataEntity>>
        { [256] = Outcome<MetadataEntity>.Success(new ClassEntity(new DefinitionRef(owner, []))),
          [512] = Outcome<MetadataEntity>.Success(new ClassEntity(new DefinitionRef(other, []))) }.ToImmutableDictionary() };
        // 直线读写、两臂同类、退出、异类、调用、堆写、循环、静态调用、构造调用、状态读取、帧写、异常边、异类调用。
        for (int scenario = 0; scenario < 16; scenario++)
        {
            var method = Method(scenario == 13 ? other : owner, scenario == 9 ? ".ctor" : "Use", scenario != 9);
            var calls = new CallNamingQuery(binder, new NamingChecks.Map([new(MethodRef.Open(method), BindingEntryKind.Ordinary)]),
                new RuntimeMap(runtime, catalog.Functions.First(f => f.Operation.Name == "AllocateObject" && f.Signature is not null),
                    catalog.Functions.First(f => f.Operation.Name == "InitializeMetadata" && f.Signature is not null)), catalog);
            var t = new TermTable(); var entry = new BlockIdentity(); var yes = new BlockIdentity(); var no = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            var slot = new AbstractSlot(SlotKind.Integer); var argument = t.Atom(new EntryAtom(slot), 64);
            var builder = new FunctionBuilder(t, entry, 64, new(frame)) { ImageBase = image };
            builder.Inputs.Add(new(slot, argument));
            Term Add(Term root, long offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, root, t.Constant(unchecked((ulong)offset), 64));
            Term Read(List<Statement> statements, Term address, int width)
            { var id = new ReadIdentity(); var value = t.Atom(new ResultAtom(id), width); statements.Add(new MemoryRead(id, address, width, value)); return value; }
            var prefix = new List<Statement>(); var klass = Read(prefix, Add(image, 256), 64); var different = Read(prefix, Add(image, 512), 64);
            var init = new Call(new(), new ImageFunction(20), [new(slot, klass)], []) { Unwind = scenario == 12 ? no : null };
            prefix.Add(init);
            List<Statement> Access(bool wrong = false)
            {
                var statements = new List<Statement>();
                var fields = Read(statements, Add(wrong ? different : klass, spec.Layout.Field("Il2CppClass", "static_fields").ByteOffset), 64);
                if (scenario == 1) statements.Add(new MemoryWrite(new(), fields, 32, t.Constant(7, 32)));
                else Read(statements, fields, 32);
                return statements;
            }
            if (scenario is 2 or 3 or 7)
            {
                builder.Blocks.Add(new(entry, [], prefix.ToImmutableArray(), new Branch(t.Slice(argument, 0, 1), yes, no)));
                builder.Blocks.Add(new(yes, [], Access().ToImmutableArray(), new Return([])));
                builder.Blocks.Add(new(no, [], scenario == 2 ? Access().ToImmutableArray() : [], scenario == 7 ? new Jump(no) : new Return([])));
            }
            else
            {
                if (scenario == 15) prefix.Add(new Call(new(), new ImageFunction(40), [new(slot, klass)], []) { Unwind = no });
                if (scenario == 14) prefix.Add(new Call(new(), new ImageFunction(30), [new(slot, klass)], []));
                if (scenario == 5) prefix.Add(new Call(new(), new ComputedTarget(argument), [], []));
                if (scenario == 6) prefix.Add(new MemoryWrite(new(), argument, 32, t.Constant(5, 32)));
                if (scenario == 10) Read(prefix, Add(klass, spec.Layout.Field("Il2CppClass", "cctor_finished_or_no_cctor").ByteOffset), 32);
                if (scenario == 11) prefix.Add(new MemoryWrite(new(), Add(frame, -8), 32, t.Constant(5, 32)));
                if (scenario is 8 or 9 or 13) prefix.Add(new Call(new(), new ImageFunction(10),
                    [new(slot, argument), new(new(SlotKind.Integer, 1), t.Constant(0, 64)),
                        new(new(SlotKind.IndirectResult), t.Constant(7, 64))], []));
                else prefix.AddRange(Access(scenario == 4));
                builder.Blocks.Add(new(entry, [], prefix.ToImmutableArray(), new Return([])));
                if (scenario == 12) builder.Blocks.Add(new(no, [], [], new Return([])));
                if (scenario == 15) builder.Blocks.Add(new(no, [], Access().ToImmutableArray(), new Return([])));
            }
            var f = builder.Freeze(); var state = new StateQueries();
            var names = new ValueNamingQuery(state, calls, facts, spec, binder);
            var locations = new ManagedLocationQuery(state, names, layouts, spec);
            var query = new ClassInitializationQuery(state, calls, names, locations, spec);
            var result = locations.CreateContext(f).Get(query, init.Identity);
            bool expected = scenario is 0 or 1 or 2 or 8 or 9 or 11;
            checks.True(result.IsSuccess && result.Value.CanAbsorb == expected, $"初始化前沿场景 {scenario}：{result.Why ?? result.Value.Why}");
            if (scenario is 8 or 9)
            {
                var output = new UnobservableEffects(state, calls, names, new InputMemoryImage(), new HashSet<AbstractSlot>(), locations, query).Run(f);
                var remaining = output.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single();
                checks.True(remaining.Target is ImageFunction { EntryOffset: 10 } &&
                    remaining.Arguments.All(a => a.Slot.Kind != SlotKind.IndirectResult), "吸收后删除签名不读取的间接返回槽");
                checks.True(ExitChecker.Check(output.Function).IsValid, "输入槽裁剪保持快照出口契约");
            }
        }
        return checks.Finish("类初始化吸收");
    }
}
