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
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Tests.Execution;
using ManagedValues = Cpp2CS.Managed.ManagedValues;

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    private static void StructMergeChecks(Assertions checks, ProgramModel primitives)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").ToList();
        TypeRef Primitive(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        TypeDef Define(string name, bool value)
        {
            var type = new TypeDef { Index = definitions.Count, Assembly = "StructMerges.dll", Namespace = "", Name = name,
                Token = (uint)(0x02000001 + definitions.Count), Attributes = TypeAttributes.Public, IsValueType = value,
                IsEnum = false, Size = 16, PackingSize = 0, ClassSizeIsDefault = true };
            definitions.Add(type); return type;
        }
        var structure = Define("S", true); var type = new DefinitionRef(structure, []);
        structure.Fields = Enumerable.Range(0, 2).Select(i => new FieldDef { Index = i, Owner = structure,
            Name = i == 0 ? "a" : "b", Type = Primitive("Int64"), Offset = i * 8, Attributes = FieldAttributes.Private }).ToArray();
        var owner = Define("StructMergeCases", false); var ownerType = new DefinitionRef(owner, []);
        var shared = new FieldDef { Index = 2, Owner = owner, Name = "Shared", Type = type, Offset = 0,
            Attributes = FieldAttributes.Public | FieldAttributes.Static };
        owner.Fields = [shared];
        var methods = new List<MethodDef>();
        MethodDef Method(string name, TypeRef result, params TypeRef[] parameters)
        {
            var method = new MethodDef { Index = methods.Count, Owner = owner, Name = name,
                Token = (uint)(0x06000001 + methods.Count), Attributes = MethodAttributes.Public | MethodAttributes.Static,
                ImplAttributes = 0, Slot = -1, ReturnType = result,
                Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray() };
            methods.Add(method); return method;
        }
        var a = Method("A", type, Primitive("Int32")); var b = Method("B", type, Primitive("Int32"));
        var consume = Method("Consume", Primitive("Void"), type);
        string[] modes = ["Three", "Zero", "Partial", "Nested", "Loop", "Split", "Slice", "Parameter", "Reuse"];
        var cases = modes.ToDictionary(mode => mode, mode => Method(mode, type, Primitive("Int32"), type));
        owner.Methods = methods;
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods,
            Fields = definitions.SelectMany(t => t.Fields).ToArray(), RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key,
                AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var layouts = new Cpp2CS.Runtime.Layouts.FieldLayouts(spec, 8, 8);
        var types = new ManagedTypes(program, layouts, 8); var binder = new MethodBinder(new(layouts), new Aapcs64());
        var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        const string source = """
            public struct S { private long a,b; public S(long x,long y){a=x;b=y;} }
            public static class StructMergeCases {
                public static S Shared;
                public static S A(int n)=>new S(n+3L,n-5L);
                public static S B(int n)=>new S(n*7L,n*11L);
                public static void Consume(S p) { }
                public static S Three(int n,S p)=>n==0?A(n):n==1?B(n):Shared;
                public static S Zero(int n,S p)=>n==0?A(n):n==1?B(n):default;
                public static S Nested(int n,S p)=>n==0?A(n):n==1?B(n):Shared;
                public static S Split(int n,S p)=>Three(n,p);
                public static S Slice(int n,S p)=>Three(n,p);
                public static S Parameter(int n,S p)=>n==0?A(n):n==1?B(n):p;
                public static S Reuse(int n,S p){S r=Three(n,p);Consume(r);return r;}
            }
            """;
        using var reference = new CompiledSource(source); using var tested = new CompiledSource(source);
        foreach (var mode in modes)
        {
            var terms = new TermTable(); var entry = new BlockIdentity(); var frame = terms.Atom(new RootAtom(AddressRoot.Frame), 64);
            var image = terms.Atom(new RootAtom(AddressRoot.Image), 64);
            var function = new FunctionBuilder(terms, entry, 64, new(frame)) { ImageBase = image };
            Term Input(int i)
            {
                var slot = new AbstractSlot(SlotKind.Integer, i); var value = terms.Atom(new EntryAtom(slot), 64);
                function.Inputs.Add(new(slot, value)); return value;
            }
            var selector = Input(0); var parameter = terms.Concat(Input(1), Input(2));
            Term Equal(int n) => terms.Apply(new CoreOperator(CoreOperation.Equal), 1, terms.Slice(selector, 0, 32), terms.Constant(n, 32));
            Term Add(Term root, int offset) => terms.Apply(new CoreOperator(CoreOperation.Add), 64, root, terms.Constant(offset, 64));
            var left = new BlockIdentity(); var choose = new BlockIdentity(); var right = new BlockIdentity();
            var field = new BlockIdentity(); var join = new BlockIdentity();
            function.Blocks.Add(new(entry, [], [], new Branch(Equal(0), left, choose)));
            function.Blocks.Add(new(choose, [], [], new Branch(Equal(1), right, field)));
            Term Call(BlockIdentity block, ulong target, BlockIdentity continuation)
            {
                var id = new CallIdentity(); var lo = terms.Atom(new ResultAtom(id), 64); var hi = terms.Atom(new ResultAtom(id, 1), 64);
                function.Blocks.Add(new(block, [], [new Call(id, new ImageFunction(target),
                    [new(new(SlotKind.Integer), selector), new(new(SlotKind.Integer, 1), terms.Constant(0, 64))],
                    [new(new(SlotKind.Integer), lo), new(new(SlotKind.Integer, 1), hi)])], new Jump(continuation)));
                return terms.Concat(lo, hi);
            }
            Term Merge(BlockIdentity block, params (BlockIdentity Block, Term Value)[] inputs)
            {
                int width = mode == "Slice" ? 128 : mode == "Split" ? 32 : 64;
                var merges = new List<Merge>(); var pieces = new List<Term>();
                for (int offset = 0; offset < 128; offset += width)
                {
                    var id = new MergeIdentity(); var value = terms.Atom(new ResultAtom(id), width);
                    merges.Add(new(id, value, inputs.Select(i => new Incoming(i.Block, terms.Slice(i.Value, offset, width))).ToImmutableArray()));
                    pieces.Add(value);
                }
                var result = terms.Concat(pieces.ToArray());
                var statements = new List<Statement>();
                if (mode == "Reuse") statements.Add(new Call(new(), new ImageFunction(40),
                    [new(new(SlotKind.Integer), terms.Slice(result, 0, 64)), new(new(SlotKind.Integer, 1), terms.Slice(result, 64, 64)),
                        new(new(SlotKind.Integer, 2), terms.Constant(0, 64))], []));
                function.Blocks.Add(new(block, [.. merges], [.. statements], new Return(
                    [new(new(SlotKind.Integer), terms.Slice(result, 0, 64)), new(new(SlotKind.Integer, 1), terms.Slice(result, 64, 64))])));
                return result;
            }
            var inner = mode == "Nested" ? new BlockIdentity() : join;
            var first = Call(left, 10, inner); var second = Call(right, 30, inner);
            var reads = new List<Statement>();
            Term Read(Term address, int width)
            {
                var id = new ReadIdentity(); var value = terms.Atom(new ResultAtom(id), width);
                reads.Add(new MemoryRead(id, address, width, value)); return value;
            }
            Term third;
            if (mode == "Zero") third = terms.Constant(0, 128);
            else if (mode == "Parameter") third = parameter;
            else
            {
                var klass = Read(Add(image, 256), 64);
                var storage = Read(Add(klass, (int)spec.Layout.Field("Il2CppClass", "static_fields").ByteOffset), 64);
                third = terms.Concat(Read(storage, 64), Read(Add(storage, 8), 64));
            }
            if (mode == "Partial") second = terms.Concat(terms.Slice(second, 0, 64), terms.Constant(17, 64));
            function.Blocks.Add(new(field, [], [.. reads], new Jump(join)));
            if (mode == "Nested")
            {
                var merged = Merge(inner, (left, first), (right, second));
                var block = function.Blocks.Single(block => block.Identity == inner);
                function.Blocks.Remove(block); function.Blocks.Add(block with { End = new Jump(join) });
                Merge(join, (inner, merged), (field, third));
            }
            else if (mode == "Loop")
            {
                var exit = new BlockIdentity();
                var ids = new[] { new MergeIdentity(), new MergeIdentity() };
                var loopValues = ids.Select(id => terms.Atom(new ResultAtom(id), 64)).ToArray();
                function.Blocks.Add(new(join, Enumerable.Range(0, 2).Select(i => new Merge(ids[i], loopValues[i],
                    [new(left, terms.Slice(first, i * 64, 64)), new(right, terms.Slice(second, i * 64, 64)),
                        new(field, terms.Slice(third, i * 64, 64)), new(join, loopValues[i])])).ToImmutableArray(), [], new Branch(Equal(2), join, exit)));
                function.Blocks.Add(new(exit, [], [], new Return([new(new(SlotKind.Integer), loopValues[0]), new(new(SlotKind.Integer, 1), loopValues[1])])));
            }
            else Merge(join, (left, first), (right, second), (field, third));
            var facts = NamingFacts.Empty with { Slots = NamingFacts.Empty.Slots.Add(256,
                Cpp2CS.Kernel.Queries.Outcome<MetadataEntity>.Success(new ClassEntity(ownerType))) };
            var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
            var calls = new CallNamingQuery(binder, new AddressMap(a, b, consume), new NamingChecks.RuntimeMap(), catalog);
            var lowered = new IntegerLowering(function.Freeze(), MethodRef.Open(cases[mode]), binder, types,
                calls: calls, effects: new NoStructWrites(), spec: spec, names: facts).Run();
            if (mode is "Partial" or "Loop")
            {
                checks.True(lowered.Body is null && lowered.Failure?.Reason.Code == "lowering.Struct.Inaccessible",
                    mode + " 保留逐字段写法原有的不可访问洞：" + lowered.Failure);
                continue;
            }
            checks.True(lowered.Body is not null, mode + " 私有结构体整体合流：" + lowered.Failure);
            if (lowered.Body is not { } body) continue;
            var returned = body.Blocks.SelectMany(block => block.Statements).OfType<ManagedReturn>().Single().Value;
            checks.True(returned is LocalValue local && local.Type.Equals(type), mode + " 返回结构体局部");
            var edges = body.Blocks.SelectMany(block => block.Statements).SelectMany(ManagedValues.Edges).ToArray();
            var copies = edges.SelectMany(edge => edge.Copies).ToArray();
            checks.True(copies.Length == (mode == "Nested" ? 4 : 3) && copies.All(copy => copy.Target.Type.Equals(type)
                && copy.Value.Type.Equals(type)), mode + " 每条入边各赋一次整体值");
            var values = body.Blocks.SelectMany(block => block.Statements)
                .SelectMany(statement => ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)))
                .SelectMany(ManagedValues.Walk).ToArray();
            checks.True(!values.OfType<FieldValue>().Any(value => value.Field.Field.Owner == structure), mode + " 不读取 S 的私有字段");
            if (mode == "Zero") checks.True(copies.Count(copy => copy.Value is ComposedValue { Leaves.Count: 0 }) == 1, "零入边写 default(S)");
            if (mode == "Reuse") checks.True(copies.Select(copy => copy.Target).Distinct().Count() == 1, "同一结构体合流重复使用只登记一个局部");
            checks.True(emitter.Emit([body]).Count == 0, mode + " 整体合流 CIL 校验");
            var output = tested.Method("StructMergeCases", mode); output.Body = skeleton.Method(cases[mode]).Body;
            RebindStructBody(tested.Module, output);
            var comparison = CilComparison.Compare(reference.Method("StructMergeCases", mode), output);
            checks.True(comparison.Status == CilComparisonStatus.Match, mode + " 原生路径语义与输出 IL 执行对照：" + comparison);
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
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
            Mono.Cecil.MethodReference m => module.ImportReference((module.GetType(m.DeclaringType.FullName)
                ?? module.TypeSystem.Object.Resolve().Module.GetType(m.DeclaringType.FullName)).Methods.Single(c => c.FullName == m.FullName)),
            Mono.Cecil.FieldReference f => module.GetType(f.DeclaringType.FullName).Fields.Single(c => c.Name == f.Name),
            Mono.Cecil.TypeReference t => MapType(t), Mono.Cecil.ParameterDefinition p => method.Parameters[p.Index], _ => instruction.Operand,
        };
    }
}
