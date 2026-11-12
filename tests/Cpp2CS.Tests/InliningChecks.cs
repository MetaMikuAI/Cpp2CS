using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Input;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Output;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Tests;

internal static partial class InliningChecks
{
    public const string Command = "inlining";
    public static int Run()
    {
        var checks = new Assertions();
        var f = new Fixture();
        var getter = f.Method(f.Owner, "Fetch", false, false);
        var setter = f.Method(f.Owner, "Put", true, false);
        var staticGetter = f.Method(f.Owner, "FetchShared", false, true);
        var staticSetter = f.Method(f.Owner, "PutShared", true, true);
        var caller = f.Method(f.Caller, "Use", false, true, [f.OwnerType, f.Integer]);
        var writer = f.Method(f.Caller, "Write", true, true, [f.OwnerType, f.Integer]);
        f.Owner.Methods = [getter, setter, staticGetter, staticSetter];
        ManagedBody Body(MethodDef method, params ManagedStatement[] statements) => new(MethodRef.Open(method), [new(0, statements)]);
        var receiver = new ArgumentValue(-1, f.OwnerType, 64);
        var argument = new ArgumentValue(0, f.Integer, 32);
        var field = new FieldValue(receiver, f.Field, f.Integer, 32);
        var shared = new StaticFieldValue(f.Shared, f.Integer, 32);
        var local = new LocalValue(new(0), f.Integer, 32);
        var bodies = new Dictionary<MethodDef, ManagedBody>
        {
            [getter] = Body(getter, new ManagedAssignment(0, local, field), new ManagedReturn(1,
                new ConversionValue(ConversionKind.SignExtend, local, f.Integer, 32))),
            [setter] = Body(setter, new ManagedAssignment(0, local, argument), new ManagedStore(1, field, local), new ManagedReturn(2, null)),
            [staticGetter] = Body(staticGetter, new ManagedReturn(0, shared)),
            [staticSetter] = Body(staticSetter, new ManagedStore(0, shared, argument), new ManagedReturn(1, null)),
        };
        foreach (var (method, body) in bodies)
            checks.True(AccessorTemplates.Read(body).Status == AccessorTemplateStatus.Complete, "局部转手与静态模板：" + method.Name);
        var sequential = new ManagedBody(MethodRef.Open(getter), [new(0, [new ManagedJump(0, new(1, []))]),
            new(1, bodies[getter].Blocks[0].Statements)]);
        checks.True(AccessorTemplates.Read(sequential).Status == AccessorTemplateStatus.Complete, "相邻块空跳转不增加模板操作");
        checks.True(AccessorTemplates.Read(sequential with { Blocks = sequential.Blocks.Reverse().ToArray() }).Status == AccessorTemplateStatus.NotTemplate,
            "不为模板重新寻找控制流路径");
        var calls = 0;
        var source = new CachedAccessorTemplates(m => { Interlocked.Increment(ref calls); return bodies.GetValueOrDefault(m); });
        Parallel.For(0, 32, _ => source.Get(getter));
        checks.True(calls == 1, "并发取用同一方法只恢复一次");
        var query = new AccessorQuery(f.Types, source);
        AccessorAnswer Ask(FieldRef target, AccessorKind kind, bool placement = true) => query.Resolve(new(MethodRef.Open(caller), 10, target,
            target.Field.IsStatic ? null : f.OwnerType, kind, placement));
        checks.True(Ask(f.Field, AccessorKind.Getter).Method?.Method == getter, "读模板采用");
        checks.True(Ask(f.Field, AccessorKind.Setter).Method?.Method == setter, "写模板采用");
        checks.True(Ask(f.Shared, AccessorKind.Getter).Method?.Method == staticGetter, "静态读模板采用");
        checks.True(Ask(f.Field, AccessorKind.Getter, false).Failure?.Code == "inline.Accessor.Placement", "无法保持位置时报洞");
        PlacementChecks(checks);
        LocalAccessorChecks(checks);
        GenericAccessorChecks(checks);
        ConstructorChecks(checks);
        var extra = Body(getter, new ManagedStore(0, field, argument), new ManagedReturn(1, field));
        checks.True(AccessorTemplates.Read(extra).Status == AccessorTemplateStatus.NotTemplate, "多一条写入不是模板");
        checks.True(AccessorTemplates.Read(Body(getter, new ManagedCall(0, new(MethodRef.Open(getter), receiver, [], false), local),
            new ManagedReturn(1, local))).Status == AccessorTemplateStatus.NotTemplate, "其他调用不是模板");
        checks.True(AccessorTemplates.Read(Body(getter, new ManagedAssignment(0, local, field), new ManagedReturn(1,
            new BinaryValue(BinaryOperator.Add, local, local, f.Integer, 32)))).Status == AccessorTemplateStatus.NotTemplate, "多次使用局部不是转手");
        checks.True(AccessorTemplates.Read(Body(getter, new ManagedAssignment(0, local, field), new ManagedAssignment(1, local, field),
            new ManagedReturn(2, local))).Status == AccessorTemplateStatus.NotTemplate, "多次赋值局部不是转手");
        checks.True(AccessorTemplates.Read(Body(getter, new ManagedReturn(0,
            new ConversionValue(ConversionKind.FloatToSignedInteger, field, f.Integer, 32)))).Status == AccessorTemplateStatus.NotTemplate, "真实转换不是模板");
        var other = f.Method(f.Owner, "Another", false, false);
        f.Owner.Methods = [getter, other];
        var ambiguous = new AccessorQuery(f.Types, new CachedAccessorTemplates(m => Body(m, new ManagedReturn(0, field))));
        var multiple = ambiguous.Resolve(new(MethodRef.Open(caller), 0, f.Field, f.OwnerType, AccessorKind.Getter, true));
        checks.True(multiple.Failure?.Code == "inline.Accessor.Ambiguous" && multiple.Matches == 2, "两个模板成立时报 Ambiguous 并给出个数");
        var virtualGetter = f.Method(f.Owner, "Virtual", false, false, virtualMethod: true);
        f.Owner.Methods = [virtualGetter];
        checks.True(Ask(f.Field, AccessorKind.Getter).NoneReason == AccessorNoneReason.NoCandidates, "虚方法不进候选");
        var generic = new GenericParameterDef { Name = "T", Position = 0, Attributes = 0 };
        other.GenericParameters = [generic]; f.Owner.Methods = [other];
        checks.True(Ask(f.Field, AccessorKind.Getter).NoneReason == AccessorNoneReason.GenericMethod, "泛型方法不进候选");
        other.GenericParameters = []; f.Owner.Methods = [other];
        checks.True(Ask(f.Field, AccessorKind.Getter).NoneReason == AccessorNoneReason.Incomplete, "未完整恢复单列原因");
        bodies[other] = Body(other, new ManagedReturn(0, new ConstantValue(3, f.Integer, 32)));
        var notTemplate = new AccessorQuery(f.Types, new CachedAccessorTemplates(m => bodies.GetValueOrDefault(m)));
        checks.True(notTemplate.Resolve(new(MethodRef.Open(caller), 0, f.Field, f.OwnerType, AccessorKind.Getter, true)).NoneReason == AccessorNoneReason.NotTemplate,
            "完整恢复但不是模板单列原因");
        f.Owner.Methods = f.Program.Methods.Where(m => m.Owner == f.Owner).ToArray();
        using var emission = new EmissionFixture(f);
        foreach (var (method, target, write) in new[] { (caller, f.Field, false), (writer, f.Field, true), (caller, f.Shared, false), (writer, f.Shared, true) })
        {
            var (native, names) = f.Function(target, write, preserve: !write);
            var lowered = new IntegerLowering(native, MethodRef.Open(method), f.Binder, f.Types,
                calls: f.Calls, spec: f.Spec, names: names, accessors: query).Run();
            checks.True(lowered.Body is not null, "字段调用下降：" + lowered.Failure);
            if (lowered.Body is not { } body) continue;
            var statements = body.Blocks[0].Statements;
            var call = statements.OfType<ManagedCall>().First();
            checks.True(statements.OfType<ManagedCall>().Count() == (write ? 1 : 2), "读后写分别保留一次调用");
            checks.True(call.Invocation.Method.Method == (write ? target.Field.IsStatic ? staticSetter : setter : target.Field.IsStatic ? staticGetter : getter), "调用的是查询选中的方法");
            checks.True(call.Invocation.Virtual == !target.Field.IsStatic, "实例调用带空检查，静态普通调用");
            checks.True(write ? call.Result is null : call.Result is not null && statements[0] == call && statements[1] is ManagedCall,
                "读在原位置定义结果且不跨写入，写替换为调用");
            checks.True(emission.Emitter.Emit([body]).Count == 0, "访问器调用写出并通过 IL 栈检查");
        }
        // 不提供查询就是关闭机制：同一不可访问字段仍由最后一道权限检查拒绝。
        var disabledNative = f.Function(f.Field, false).Function;
        checks.True(new IntegerLowering(disabledNative, MethodRef.Open(caller), f.Binder, f.Types, calls: f.Calls, spec: f.Spec).Run()
            .Failure?.Reason.Code == "lowering.Access.Field", "关闭机制保留权限检查");
        var entries = new[] { getter, caller }.Select((m, i) => new CodeEntry((ulong)(16 + 4 * i), EntryKind.Method, MethodRef.Open(m), i, null)).ToArray();
        var map = new Registrations { CodeRegistration = 0, MetadataRegistration = 0, Entries = entries,
            ByAddress = entries.ToDictionary(e => e.Address, e => ImmutableArray.Create(e)), Rgctx = new Dictionary<(string, uint), ImmutableArray<RgctxEntry>>(),
            MetadataUsageSlots = [], TypePointers = new Dictionary<ulong, int>(), InvokerOf = new Dictionary<MethodDef, int>(), UsageEntities = new Dictionary<ulong, Usage>() };
        var facts = new GlobalFacts(new InputMemoryImage(), f.Program, map, f.Spec, "arm64");
        var frontend = new TemplateFrontend(disabledNative);
        var adapter = new AccessorTemplateSource(facts, frontend);
        checks.True(adapter.Get(caller).Status == AccessorTemplateStatus.Incomplete && adapter.Get(caller).Status == AccessorTemplateStatus.Incomplete
            && frontend.Count == 1, "管线模板恢复关闭内联逆且失败缓存，不递归恢复字段访问器");
        checks.True(adapter.Get(getter) is { Status: AccessorTemplateStatus.Complete, Template.Kind: AccessorKind.Getter }
            && frontend.Count == 2, "模板从候选自己的原生恢复体取得");
        return checks.Finish("字段访问器内联逆");
    }

    private sealed class BodySource(Func<MethodDef, ManagedBody?> get) : IMethodTemplateSource
    {
        public ManagedBody? GetBody(MethodDef method) => get(method);
    }

    private static void ConstructorChecks(Assertions checks)
    {
        var f = new Fixture();
        var root = f.Types.Object.Definition;
        f.Owner.BaseType = f.Types.Object;
        f.Caller.BaseType = f.OwnerType;
        var objectCtor = f.Method(root, ".ctor", true, false, []);
        var parentCtor = f.Method(f.Owner, ".ctor", true, false, []);
        var childCtor = f.Method(f.Caller, ".ctor", true, false, []);
        ManagedBody Body(MethodDef method, params ManagedStatement[] statements) => new(MethodRef.Open(method), [new(0, statements)]);
        ManagedCall Base(MethodDef caller, MethodDef parent) => new(0,
            new(MethodRef.Open(parent), new ArgumentValue(-1, MethodRef.Open(caller).DeclaringType, 64), [], false), null);
        var bodies = new Dictionary<MethodDef, ManagedBody>
        {
            [objectCtor] = Body(objectCtor, new ManagedReturn(0, null)),
            [parentCtor] = Body(parentCtor, Base(parentCtor, objectCtor), new ManagedReturn(1, null)),
            [childCtor] = Body(childCtor, Base(childCtor, parentCtor), new ManagedReturn(1, null)),
        };
        ConstructorTemplates Templates() => new(new BodySource(bodies.GetValueOrDefault), f.Types);
        var templates = Templates();
        checks.True(templates.IsEmpty(objectCtor), "Object 构造模板为空");
        checks.True(templates.IsEmpty(childCtor) && templates.IsEmpty(parentCtor), "两层继承递归判空");
        bodies[parentCtor] = Body(parentCtor, Base(parentCtor, objectCtor), new ManagedStore(1,
            new FieldValue(new ArgumentValue(-1, f.OwnerType, 64), f.Field, f.Integer, 32), new ConstantValue(1, f.Integer, 32)), new ManagedReturn(2, null));
        checks.True(!Templates().IsEmpty(parentCtor) && !Templates().IsEmpty(childCtor), "字段初始值使本类及派生模板不为空");
        checks.True(new ConstructorQuery(f.Types, Templates()).Resolve(new(MethodRef.Open(childCtor), 0, f.OwnerType, ConstructorAnchor.Allocation))
            .Failure?.Code == "inline.Constructor.Template", "分配类的构造有字段初始值时报 Template");
        checks.True(new ConstructorQuery(f.Types, new(new BodySource(_ => null), f.Types)).Resolve(new(MethodRef.Open(childCtor), 0, f.OwnerType, ConstructorAnchor.Base))
            .Failure?.Code == "inline.Constructor.BaseTemplate", "基类构造未恢复时报 BaseTemplate");
        bodies[parentCtor] = Body(parentCtor, new ManagedReturn(0, null));
        checks.True(!Templates().IsEmpty(parentCtor), "有基类时裸 return 不是空模板");
        bodies[parentCtor] = Body(parentCtor, Base(parentCtor, objectCtor), new ManagedReturn(1, null));
        var query = new ConstructorQuery(f.Types, Templates());
        var initialization = query.Initialization(MethodRef.Open(childCtor), [new(0, [new ManagedReturn(0, null)])]);
        checks.True(initialization.Method?.Method == parentCtor, "锚点 A 查询选中唯一空基类构造");
        checks.True(query.Initialization(MethodRef.Open(childCtor), [new(0, [Base(childCtor, objectCtor), new ManagedReturn(1, null)])])
            .Failure?.Code == "lowering.ConstructorInitialization", "已有祖先构造调用时不重复补初始化");
        var extra = f.Method(f.Owner, ".ctor", true, false, [f.Integer]);
        checks.True(query.Resolve(new(MethodRef.Open(childCtor), 0, f.OwnerType, ConstructorAnchor.Base)).Failure?.Code == "inline.Constructor.BaseAmbiguous",
            "基类声明两个构造时报 BaseAmbiguous");
        checks.True(query.Resolve(new(MethodRef.Open(childCtor), 0, f.OwnerType, ConstructorAnchor.Allocation)).Failure?.Code == "inline.Constructor.Ambiguous",
            "分配类声明两个构造时报 Ambiguous");
        f.Owner.Methods = [parentCtor];
        f.Owner.Methods = [extra];
        checks.True(query.Resolve(new(MethodRef.Open(childCtor), 0, f.OwnerType, ConstructorAnchor.Base)).Failure?.Code == "inline.Constructor.BaseTemplate",
            "唯一构造有参或不可访问时报 BaseTemplate");
        f.Owner.Methods = [parentCtor];
        ((List<MethodDef>)f.Program.Methods).Remove(extra);
        // 伪造继承环也不得成为空模板。
        f.Owner.BaseType = new DefinitionRef(f.Caller, []);
        bodies[parentCtor] = Body(parentCtor, Base(parentCtor, childCtor), new ManagedReturn(1, null));
        checks.True(!Templates().IsEmpty(childCtor), "构造模板继承环判为非空");
        f.Owner.BaseType = f.Types.Object;
        bodies[parentCtor] = Body(parentCtor, Base(parentCtor, objectCtor), new ManagedReturn(1, null));
        query = new(f.Types, Templates());
        var terms = new TermTable(); var head = new BlockIdentity();
        var self = terms.Atom(new EntryAtom(new(SlotKind.Integer)), 64);
        var native = new FunctionBuilder(terms, head, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
        native.Inputs.Add(new(new(SlotKind.Integer), self));
        native.Blocks.Add(new(head, [], [], new Return([])));
        var lowered = new IntegerLowering(native.Freeze(), MethodRef.Open(childCtor), f.Binder, f.Types, constructors: query).Run();
        checks.True(lowered.Body?.Blocks[0].Statements is [ManagedCall { Invocation.Method.Method: var selected }, ManagedReturn] && selected == parentCtor,
            "锚点 A 在方法体开头补基类调用");
        var rootBody = new IntegerLowering(native.Freeze(), MethodRef.Open(objectCtor), f.Binder, f.Types, constructors: query).Run().Body;
        checks.True(rootBody is not null, "开启机制后根对象裸 return 完整恢复");
        using (var rootEmission = new EmissionFixture(f))
            checks.True(rootBody is not null && rootEmission.Emitter.Emit([rootBody]).Count == 0, "根对象构造通过输出初始化检查");
        var entries = new[] { objectCtor, parentCtor, childCtor }.Select((m, i) => new CodeEntry((ulong)(16 + 4 * i), EntryKind.Method, MethodRef.Open(m), i, null)).ToArray();
        var map = new Registrations { CodeRegistration = 0, MetadataRegistration = 0, Entries = entries,
            ByAddress = entries.ToDictionary(e => e.Address, e => ImmutableArray.Create(e)), Rgctx = new Dictionary<(string, uint), ImmutableArray<RgctxEntry>>(),
            MetadataUsageSlots = [], TypePointers = new Dictionary<ulong, int>(), InvokerOf = new Dictionary<MethodDef, int>(), UsageEntities = new Dictionary<ulong, Usage>() };
        var frontend = new TemplateFrontend(native.Freeze());
        var adapter = new MethodTemplateSource(new GlobalFacts(new InputMemoryImage(), f.Program, map, f.Spec, "arm64"), frontend, constructors: true);
        checks.True(new ConstructorTemplates(adapter, f.Types).IsEmpty(childCtor) && frontend.Count == 3,
            "管线在机制开启时沿两层基类完整恢复模板");
        Parallel.For(0, 16, _ => adapter.GetBody(childCtor));
        checks.True(frontend.Count == 3, "构造模板完整恢复体并发取用只算一次");
        var catalog = RuntimeFunctionCatalog.Select(f.Spec.Layout.UnityVersion, f.Spec.Layout.Triple, f.Spec.Layout.DataModel);
        var allocation = catalog.Functions.First(op => op.Operation.Il?.Name == "NewObject" && op.Signature is not null);
        var calls = new CallNamingQuery(f.Binder, new NamingChecks.Map([new(MethodRef.Open(parentCtor), BindingEntryKind.Ordinary)]),
            new NamingChecks.RuntimeMap(allocation), catalog);
        var make = f.Method(f.Caller, "Make", false, true, []); make.ReturnType = f.OwnerType;
        foreach (var mode in new[] { "Inline", "Direct", "Deferred", "Branch", "Mixed" })
        {
            var t = new TermTable(); var block = new BlockIdentity(); var left = new BlockIdentity(); var right = new BlockIdentity();
            var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            var function = new FunctionBuilder(t, block, 64, new(t.Atom(new RootAtom(AddressRoot.Frame), 64))) { ImageBase = image };
            var read = new ReadIdentity(); var klass = t.Atom(new ResultAtom(read), 64);
            var id = new CallIdentity(); var result = t.Atom(new ResultAtom(id), 64);
            var statements = new List<Statement> { new MemoryRead(read, t.Apply(new CoreOperator(CoreOperation.Add), 64, image, t.Constant(128, 64)), 64, klass),
                new Call(id, new ImageFunction(20), [new(new(SlotKind.Integer), klass)], [new(new(SlotKind.Integer), result)]) { Trace = new(32) } };
            Call Initialize() => new(new(), new ImageFunction(10), [new(new(SlotKind.Integer), result), new(new(SlotKind.Integer, 1), t.Constant(0, 64))], []) { Trace = new(40) };
            if (mode == "Deferred")
            {
                var other = new CallIdentity();
                statements.Add(new Call(other, new ImageFunction(20), [new(new(SlotKind.Integer), klass)], [new(new(SlotKind.Integer), t.Atom(new ResultAtom(other), 64))]));
            }
            if (mode is "Direct" or "Deferred") statements.Add(Initialize());
            if (mode is "Branch" or "Mixed")
            {
                var condition = t.Atom(new EntryAtom(new(SlotKind.Integer)), 64); function.Inputs.Add(new(new(SlotKind.Integer), condition));
                make.Parameters = [new("condition", f.Types.Int64, 0, null, false)];
                function.Blocks.Add(new(block, [], [.. statements], new Branch(t.Apply(new CoreOperator(CoreOperation.Equal), 1, condition, t.Constant(0, 64)), left, right)));
                function.Blocks.Add(new(left, [], [], new Return([new(new(SlotKind.Integer), result)])));
                function.Blocks.Add(new(right, [], mode == "Mixed" ? [Initialize()] : [], new Return([new(new(SlotKind.Integer), result)])));
            }
            else { make.Parameters = []; function.Blocks.Add(new(block, [], [.. statements], new Return([new(new(SlotKind.Integer), result)]))); }
            var evidence = NamingFacts.Empty with { Slots = NamingFacts.Empty.Slots.Add(128, Outcome<MetadataEntity>.Success(new ClassEntity(f.OwnerType))) };
            var selectedQuery = mode == "Direct" ? new ConstructorQuery(f.Types, new(new BodySource(_ => null), f.Types)) : query;
            var body = new IntegerLowering(function.Freeze(), MethodRef.Open(make), f.Binder, f.Types, calls: calls, spec: f.Spec, names: evidence, constructors: selectedQuery).Run();
            if (mode is "Deferred" or "Mixed") checks.True(body.Failure?.Reason.Code == "lowering.Allocation.Deferred", "延迟或部分路径显式构造保留洞：" + mode);
            else
            {
                var created = body.Body?.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().SingleOrDefault(a => a.Value is NewObjectValue);
                checks.True(created is { Value: NewObjectValue { Constructor.Method: var ctor } } && ctor == parentCtor
                    && created.Address == (mode == "Direct" ? 40UL : 32UL),
                    "分配处 newobj 或原有紧邻配对：" + mode + " " + body.Failure);
                using var emission = new EmissionFixture(f);
                checks.True(body.Body is { } complete && emission.Emitter.Emit([complete]).Count == 0, "构造调用通过输出栈检查：" + mode);
            }
        }
    }

    private static void PlacementChecks(Assertions checks)
    {
        foreach (bool split in new[] { false, true })
        {
            var terms = new TermTable(); var entry = new BlockIdentity(); var yes = new BlockIdentity(); var no = new BlockIdentity();
            var builder = new FunctionBuilder(terms, entry, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var address = terms.Atom(new RootAtom(AddressRoot.Image), 64);
            var first = new ReadIdentity(); var second = new ReadIdentity();
            MemoryRead Read(ReadIdentity id) => new(id, address, 32, terms.Atom(new ResultAtom(id), 32));
            if (split)
            {
                builder.Blocks.Add(new(entry, [], [], new Branch(terms.Constant(1, 1), yes, no)));
                builder.Blocks.Add(new(yes, [], [Read(first)], new Return([])));
                builder.Blocks.Add(new(no, [], [Read(second)], new Return([])));
            }
            else builder.Blocks.Add(new(entry, [], [Read(first), Read(second)], new Return([])));
            var context = new QueryContext(builder.Freeze());
            var placed = context.Get(new AccessorReadPlacementQuery(), new(first, [first, second]));
            checks.True(placed.IsSuccess && placed.Value == !split, "共享读取原定义必须支配其余读取");
        }
    }

    private sealed class TemplateFrontend(NativeFunction function) : IMethodStage<CodeEntry, NativeFunction>
    {
        public int Count;
        public string Name => "前端";
        public StageResult<NativeFunction> Run(CodeEntry input, MethodContext context) { Count++; return new Completed<NativeFunction>(function); }
    }

    private sealed class EmissionFixture : IDisposable
    {
        private readonly Skeleton skeleton;
        public BodyEmitter Emitter { get; }
        public EmissionFixture(Fixture f) { skeleton = new(f.Program, 16); Emitter = new(skeleton, f.Types); }
        public void Dispose() { foreach (var assembly in skeleton.Assemblies) assembly.Dispose(); }
    }

    private sealed class Fixture
    {
        public readonly RuntimeSpec Spec = InputCorpusChecks.Spec("arm64-v8a");
        private readonly List<TypeDef> definitions = [];
        private readonly List<MethodDef> methods = [];
        public TypeDef Owner { get; }
        public TypeDef Caller { get; }
        public DefinitionRef OwnerType { get; }
        public TypeRef Integer { get; }
        public TypeRef Void { get; }
        public FieldRef Field { get; }
        public FieldRef Shared { get; }
        public ProgramModel Program { get; }
        public ManagedTypes Types { get; }
        public MethodBinder Binder { get; }
        public CallNamingQuery Calls { get; }
        public Fixture(bool generic = false, bool genericField = false, bool valueOwner = false)
        {
            TypeDef Define(string name, string ns = "", bool value = false) { var type = new TypeDef { Index = definitions.Count,
                Assembly = ns == "System" ? "mscorlib.dll" : "InliningChecks.dll", Namespace = ns, Name = name, Token = (uint)(0x02000001 + definitions.Count),
                Attributes = TypeAttributes.Public, IsValueType = value, IsEnum = false, Size = 64, PackingSize = 0, ClassSizeIsDefault = true }; definitions.Add(type); return type; }
            foreach (var name in new[] { "Object", "String", "Boolean", "Char", "SByte", "Byte", "Int16", "UInt16", "Int32", "UInt32", "Int64", "UInt64", "Single", "Double", "IntPtr", "UIntPtr", "RuntimeTypeHandle", "RuntimeFieldHandle", "RuntimeMethodHandle", "TypedReference", "Void" })
                Define(name, "System", name is not ("Object" or "String"));
            Integer = new DefinitionRef(definitions.Single(t => t.Name == "Int32"), []); Void = new DefinitionRef(definitions.Single(t => t.Name == "Void"), []);
            Owner = Define("Owner", value: valueOwner); Caller = Define("Caller");
            if (generic) Owner.GenericParameters = [new() { Name = "T", Position = 0, Attributes = 0 }];
            OwnerType = new(Owner, Owner.GenericParameters.Select(p => (TypeRef)new GenericParameterRef(p.Name, false, p.Position) { Parameter = p }).ToArray());
            var field = new FieldDef { Index = 0, Owner = Owner, Name = "Value", Type = genericField ? OwnerType.Arguments[0] : Integer, Attributes = FieldAttributes.Private, Offset = 16, Token = 0x04000001 };
            var shared = new FieldDef { Index = 1, Owner = Owner, Name = "Shared", Type = Integer, Attributes = FieldAttributes.Private | FieldAttributes.Static, Offset = 0, Token = 0x04000002 };
            Owner.Fields = [field, shared]; Field = new(field, OwnerType); Shared = new(shared, OwnerType);
            Program = new() { MetadataVersion = 31, Types = definitions, Methods = methods, Fields = [field, shared], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
                Assemblies = definitions.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key),
                    Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
            var layouts = new FieldLayouts(Spec, 8, 8); Types = new(Program, layouts, 8); Binder = new(new(layouts), new Aapcs64());
            var catalog = RuntimeFunctionCatalog.Select(Spec.Layout.UnityVersion, Spec.Layout.Triple, Spec.Layout.DataModel);
            Calls = new(Binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(), catalog);
        }
        public MethodDef Method(TypeDef owner, string name, bool write, bool statics, TypeRef[]? parameters = null, bool virtualMethod = false)
        {
            var method = new MethodDef { Index = methods.Count, Owner = owner, Name = name, Token = (uint)(0x06000001 + methods.Count),
                Attributes = MethodAttributes.Public | (statics ? MethodAttributes.Static : 0) | (virtualMethod ? MethodAttributes.Virtual : 0)
                    | (name == ".ctor" ? MethodAttributes.SpecialName | MethodAttributes.RTSpecialName : 0), ImplAttributes = 0, Slot = -1,
                ReturnType = write ? Void : Integer, Parameters = (parameters ?? (write ? [Integer] : [])).Select(t => new ParameterDef("value", t, 0, null, false)).ToArray() };
            methods.Add(method); owner.Methods = [.. owner.Methods, method]; return method;
        }
        public (NativeFunction Function, NamingFacts Names) Function(FieldRef field, bool write, bool preserve = false, int width = 32)
        {
            var terms = new TermTable(); var block = new BlockIdentity();
            var builder = new FunctionBuilder(terms, block, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var root = terms.Atom(new EntryAtom(new(SlotKind.Integer)), 64); var input = terms.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64);
            builder.Inputs.Add(new(new(SlotKind.Integer), root)); builder.Inputs.Add(new(new(SlotKind.Integer, 1), input));
            var statements = new List<Statement>(); var names = NamingFacts.Empty;
            Term Add(Term value, long offset) => terms.Apply(new CoreOperator(CoreOperation.Add), 64, value, terms.Constant(offset, 64));
            Term Read(Term address, int width) { var id = new ReadIdentity(); var value = terms.Atom(new ResultAtom(id), width); statements.Add(new MemoryRead(id, address, width, value)); return value; }
            if (field.Field.IsStatic)
            {
                var image = terms.Atom(new RootAtom(AddressRoot.Image), 64); builder.ImageBase = image;
                var klass = Read(Add(image, 256), 64); root = Read(Add(klass, Spec.Layout.Field("Il2CppClass", "static_fields").ByteOffset), 64);
                names = names with { Slots = ImmutableDictionary<ulong, Outcome<MetadataEntity>>.Empty.Add(256, Outcome<MetadataEntity>.Success(new ClassEntity(OwnerType))) };
            }
            var address = Add(root, field.Field.Offset);
            if (write) statements.Add(new MemoryWrite(new(), address, width, terms.Slice(input, 0, width)));
            var result = write ? terms.Constant(0, width) : Read(address, width);
            if (preserve) statements.Add(new MemoryWrite(new(), address, 32, terms.Constant(9, 32)));
            builder.Blocks.Add(new(block, [], statements.ToImmutableArray(), new Return(write ? [] : [new(new(SlotKind.Integer), result.Width == 64 ? result : terms.Concat(result, terms.Constant(0, 64 - result.Width)))])));
            return (builder.Freeze(), names);
        }
    }
}
