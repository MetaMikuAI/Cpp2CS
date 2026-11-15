using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Output;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Tests.Execution;

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    private sealed class NoStructWrites : Cpp2CS.Kernel.State.ICallEffectSource
    {
        public Cpp2CS.Kernel.Queries.Outcome<CallEffects> Get(Cpp2CS.Kernel.Queries.QueryContext context, Call call) =>
            Cpp2CS.Kernel.Queries.Outcome<CallEffects>.Success(new(false, 0, []));
    }
    private sealed class StructBodies(Dictionary<MethodDef, ManagedBody> bodies) : IMethodTemplateSource
    {
        public ManagedBody? GetBody(MethodDef method) => bodies.GetValueOrDefault(method);
    }
    private static void StructConstructorChecks(Assertions checks, ProgramModel primitives)
    {
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").ToList();
        TypeRef Primitive(string n) => new DefinitionRef(definitions.Single(t => t.Name == n), []);
        var integer = Primitive("Int32"); var none = Primitive("Void");
        var methods = new List<MethodDef>(); var fields = new List<FieldDef>();
        TypeDef Define(string name, bool value = true)
        {
            var t = new TypeDef { Index = definitions.Count, Assembly = "StructValues.dll", Namespace = "", Name = name,
                Token = (uint)(0x02000001 + definitions.Count), Attributes = TypeAttributes.Public, IsValueType = value,
                IsEnum = false, Size = value ? 8 : 16, PackingSize = 0, ClassSizeIsDefault = true };
            definitions.Add(t); return t;
        }
        MethodDef Method(TypeDef owner, string name, TypeRef result, MethodAttributes flags, params TypeRef[] args)
        {
            var m = new MethodDef { Index = methods.Count, Owner = owner, Name = name, Token = (uint)(0x06000001 + methods.Count),
                Attributes = flags, ImplAttributes = 0, Slot = -1, ReturnType = result,
                Parameters = args.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray() };
            methods.Add(m); return m;
        }
        var caller = Define("StructCases", false);
        var readBox = Define("CtorBox", false); var readBoxType = new DefinitionRef(readBox, []);
        readBox.Fields = [new FieldDef { Index = fields.Count, Owner = readBox, Name = "Value", Type = integer, Offset = 16, Attributes = FieldAttributes.Public }];
        fields.AddRange(readBox.Fields);
        var bodies = new Dictionary<MethodDef, ManagedBody>(); var cases = new Dictionary<string, (MethodDef Caller, TypeDef Type)>();
        foreach (var name in new[] { "PairC", "PureC", "ChainC", "ZeroC", "AmbiguousC", "ReadC", "PartialC", "RepeatedC", "FromValueC", "ConstantC" })
        {
            var t = Define(name); var type = new DefinitionRef(t, []);
            t.Fields = Enumerable.Range(0, 2).Select(i => new FieldDef { Index = fields.Count + i, Owner = t, Name = i == 0 ? "a" : "b",
                Type = integer, Offset = i * 4, Attributes = FieldAttributes.Private | FieldAttributes.InitOnly }).ToArray();
            fields.AddRange(t.Fields);
            var ctor = Method(t, ".ctor", none, MethodAttributes.Public, name is "PairC" or "AmbiguousC" ? [integer, integer] : name == "FromValueC" ? [type, integer] : name == "ReadC" ? [readBoxType] : [integer]);
            var self = new ArgumentValue(-1, type, 0); var x = new ArgumentValue(0, ctor.Parameters[0].Type, ctor.Parameters[0].Type.Equals(integer) ? 32 : 64);
            FieldValue Target(int i) => new(self, new(t.Fields[i], type), integer, 32);
            var stores = new List<ManagedStatement>();
            if (name == "PartialC")
            {
                var zero = new LocalValue(new(0), type, 0);
                stores.Add(new ManagedAssignment(0, zero, new ComposedValue(type, [])));
                stores.Add(new ManagedStore(0, new IndirectValue(new ArgumentValue(-1, new ByRefRef(type), 64), type), zero));
            }
            if (name == "ChainC")
            {
                var inner = Method(t, ".ctor", none, MethodAttributes.Private, integer, integer);
                bodies[inner] = new(MethodRef.Open(inner), [new(0, [new ManagedStore(0, Target(0), new ArgumentValue(0, integer, 32)),
                    new ManagedStore(0, Target(1), new ArgumentValue(1, integer, 32)), new ManagedReturn(0, null)])]);
                stores.Add(new ManagedCall(0, new(MethodRef.Open(inner), self, [x, new ConstantValue(5, integer, 32)], false), null));
            }
            else
            {
                ManagedValue first = name == "PureC" ? new BinaryValue(BinaryOperator.Add, x, new ConstantValue(1, integer, 32), integer, 32) : x;
                if (name == "FromValueC") first = new FieldValue(new ArgumentValue(0, type, 0), new(t.Fields[0], type), integer, 32);
                if (name == "ReadC") first = new FieldValue(x, new(readBox.Fields[0], readBoxType), integer, 32);
                stores.Add(new ManagedStore(0, Target(0), first));
                if (name != "PartialC") stores.Add(new ManagedStore(0, Target(1), name == "ConstantC"
                    ? new ConversionValue(ConversionKind.Bitcast, new ConstantValue(0, Primitive("UInt32"), 32), integer, 32) : name == "PureC"
                    ? new BinaryValue(BinaryOperator.Multiply, x, new ConstantValue(2, integer, 32), integer, 32)
                    : name == "ReadC" ? new ConstantValue(0, integer, 32) : name is "PairC" or "AmbiguousC" or "FromValueC" ? new ArgumentValue(1, integer, 32) : x));
            }
            stores.Add(new ManagedReturn(0, null)); bodies[ctor] = new(MethodRef.Open(ctor), [new(0, stores)]);
            if (name == "AmbiguousC")
            {
                var duplicate = Method(t, ".ctor", none, MethodAttributes.Public, integer);
                bodies[duplicate] = new(MethodRef.Open(duplicate), [new(0, [new ManagedStore(0, Target(0), x), new ManagedStore(0, Target(1), x), new ManagedReturn(0, null)])]);
            }
            t.Methods = methods.Where(m => m.Owner == t).ToArray();
            var test = Method(caller, name, type, MethodAttributes.Public | MethodAttributes.Static, name == "FromValueC" ? [type, integer] : [integer, integer]);
            cases.Add(name, (test, t));
        }
        caller.Methods = methods.Where(m => m.Owner == caller).ToArray();
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = fields,
            RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [], Assemblies = definitions.GroupBy(t => t.Assembly)
                .Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var layouts = new Cpp2CS.Runtime.Layouts.FieldLayouts(InputCorpusChecks.Spec("arm64-v8a"), 8, 8);
        var types = new ManagedTypes(program, layouts, 8); var binder = new MethodBinder(new(layouts), new Aapcs64());
        var templates = new StructConstructorTemplates(types, new StructBodies(bodies));
        var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        foreach (var (name, item) in cases)
        {
            var terms = new TermTable(); var entry = new BlockIdentity(); var frame = terms.Atom(new RootAtom(AddressRoot.Frame), 64);
            var function = new FunctionBuilder(terms, entry, 64, new(frame));
            Term Input(int i) { var slot = new AbstractSlot(SlotKind.Integer, i); var t = terms.Atom(new EntryAtom(slot), 64); function.Inputs.Add(new(slot, t)); return terms.Slice(t, 0, 32); }
            var x = Input(0); var y = Input(1);
            Term first = name == "PureC" ? terms.Apply(new CoreOperator(CoreOperation.Add), 32, x, terms.Constant(1, 32)) : x;
            Term second = name == "PureC" ? terms.Apply(new CoreOperator(CoreOperation.Multiply), 32, x, terms.Constant(2, 32))
                : name == "ChainC" ? terms.Constant(5, 32) : name is "PartialC" or "ConstantC" ? terms.Constant(0, 32) : name is "AmbiguousC" or "RepeatedC" ? x : y;
            if (name == "ZeroC") { first = terms.Constant(0, 32); second = first; }
            function.Blocks.Add(new(entry, [], [], new Return([new(new(SlotKind.Integer), terms.Concat(first, second))])));
            var lowered = new IntegerLowering(function.Freeze(), MethodRef.Open(item.Caller), binder, types, structConstructors: templates).Run();
            if (name is "AmbiguousC" or "ReadC")
            {
                checks.True(lowered.Body is null && lowered.Failure?.Reason.Code == (name == "AmbiguousC" ? "inline.StructConstructor.Ambiguous" : "inline.StructConstructor.Events"), name + " 必须保持洞：" + lowered.Failure);
                continue;
            }
            checks.True(lowered.Body is not null, name + " 无事件构造下降：" + lowered.Failure);
            if (lowered.Body is not { } body) continue;
            var returned = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedReturn>().Single().Value;
            checks.True(name == "ZeroC" ? returned is ComposedValue { Leaves.Count: 0 } : returned is NewObjectValue, name + " 整体写法");
            checks.True(emitter.Emit([body]).Count == 0, name + " CIL 校验");
        }
        const string source = """
            public readonly struct PairC { private readonly int a,b; public PairC(int x,int y){a=x;b=y;} }
            public readonly struct PureC { private readonly int a,b; public PureC(int x){a=x+1;b=x*2;} }
            public readonly struct ChainC { private readonly int a,b; public ChainC(int x):this(x,5){} private ChainC(int x,int y){a=x;b=y;} }
            public readonly struct ZeroC { private readonly int a,b; public ZeroC(int x){a=x;b=x;} }
            public readonly struct PartialC { private readonly int a,b; public PartialC(int x){a=x;b=0;} }
            public readonly struct RepeatedC { private readonly int a,b; public RepeatedC(int x){a=x;b=x;} }
            public readonly struct FromValueC { private readonly int a,b; public FromValueC(FromValueC p,int y){a=p.a;b=y;} }
            public readonly struct ConstantC { private readonly int a,b; public ConstantC(int x){a=x;b=0;} }
            public static class StructCases {
                public static PairC PairC(int x,int y)=>new PairC(x,y);
                public static PureC PureC(int x,int y)=>new PureC(x);
                public static ChainC ChainC(int x,int y)=>new ChainC(x);
                public static ZeroC ZeroC(int x,int y)=>default;
                public static PartialC PartialC(int x,int y)=>new PartialC(x);
                public static RepeatedC RepeatedC(int x,int y)=>new RepeatedC(x);
                public static FromValueC FromValueC(FromValueC p,int y)=>new FromValueC(p,y);
                public static ConstantC ConstantC(int x,int y)=>new ConstantC(x);
            }
            """;
        using var reference = new CompiledSource(source); using var tested = new CompiledSource(source);
        foreach (var name in new[] { "PairC", "PureC", "ChainC", "ZeroC", "PartialC", "RepeatedC", "FromValueC", "ConstantC" })
        {
            var emitted = skeleton.Method(cases[name].Caller);
            if (emitted.Body.Instructions.Any(i => i.OpCode == Mono.Cecil.Cil.OpCodes.Throw)) continue;
            var output = tested.Method("StructCases", name); output.Body = emitted.Body;
            RebindStructBody(tested.Module, output);
            var comparison = CilComparison.Compare(reference.Method("StructCases", name), output);
            checks.True(comparison.Status == CilComparisonStatus.Match, name + " 构造执行对照：" + comparison);
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
    private static void RebindStructBody(Mono.Cecil.ModuleDefinition module, Mono.Cecil.MethodDefinition method)
    {
        Mono.Cecil.TypeReference MapType(Mono.Cecil.TypeReference t) => t is Mono.Cecil.ByReferenceType byref ? new Mono.Cecil.ByReferenceType(MapType(byref.ElementType))
            : module.GetType(t.FullName) ?? module.ImportReference(module.TypeSystem.Object.Resolve().Module.GetType(t.FullName));
        foreach (var local in method.Body.Variables) local.VariableType = MapType(local.VariableType);
        foreach (var instruction in method.Body.Instructions) instruction.Operand = instruction.Operand switch
        {
            Mono.Cecil.MethodReference m => module.GetType(m.DeclaringType.FullName).Methods.Single(c => c.FullName == m.FullName),
            Mono.Cecil.FieldReference f => module.GetType(f.DeclaringType.FullName).Fields.Single(c => c.Name == f.Name),
            Mono.Cecil.TypeReference t => MapType(t), Mono.Cecil.ParameterDefinition p => method.Parameters[p.Index], _ => instruction.Operand,
        };
    }
}
