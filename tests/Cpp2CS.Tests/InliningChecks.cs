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

internal static class InliningChecks
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
        f.Owner.GenericParameters = [generic];
        checks.True(Ask(f.Field, AccessorKind.Getter).NoneReason == AccessorNoneReason.Generic, "泛型类型不进候选");
        f.Owner.GenericParameters = [];
        other.GenericParameters = [generic]; f.Owner.Methods = [other];
        checks.True(Ask(f.Field, AccessorKind.Getter).NoneReason == AccessorNoneReason.Generic, "泛型方法不进候选");
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
        public Fixture()
        {
            TypeDef Define(string name, string ns = "", bool value = false) { var type = new TypeDef { Index = definitions.Count,
                Assembly = ns == "System" ? "mscorlib.dll" : "InliningChecks.dll", Namespace = ns, Name = name, Token = (uint)(0x02000001 + definitions.Count),
                Attributes = TypeAttributes.Public, IsValueType = value, IsEnum = false, Size = 64, PackingSize = 0, ClassSizeIsDefault = true }; definitions.Add(type); return type; }
            foreach (var name in new[] { "Object", "String", "Boolean", "Char", "SByte", "Byte", "Int16", "UInt16", "Int32", "UInt32", "Int64", "UInt64", "Single", "Double", "IntPtr", "UIntPtr", "RuntimeTypeHandle", "RuntimeFieldHandle", "RuntimeMethodHandle", "TypedReference", "Void" })
                Define(name, "System", name is not ("Object" or "String"));
            Integer = new DefinitionRef(definitions.Single(t => t.Name == "Int32"), []); Void = new DefinitionRef(definitions.Single(t => t.Name == "Void"), []);
            Owner = Define("Owner"); Caller = Define("Caller"); OwnerType = new(Owner, []);
            var field = new FieldDef { Index = 0, Owner = Owner, Name = "Value", Type = Integer, Attributes = FieldAttributes.Private, Offset = 16, Token = 0x04000001 };
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
                Attributes = MethodAttributes.Public | (statics ? MethodAttributes.Static : 0) | (virtualMethod ? MethodAttributes.Virtual : 0), ImplAttributes = 0, Slot = -1,
                ReturnType = write ? Void : Integer, Parameters = (parameters ?? (write ? [Integer] : [])).Select(t => new ParameterDef("value", t, 0, null, false)).ToArray() };
            methods.Add(method); owner.Methods = [.. owner.Methods, method]; return method;
        }
        public (NativeFunction Function, NamingFacts Names) Function(FieldRef field, bool write, bool preserve = false)
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
            if (write) statements.Add(new MemoryWrite(new(), address, 32, terms.Slice(input, 0, 32)));
            var result = write ? terms.Constant(0, 32) : Read(address, 32);
            if (preserve) statements.Add(new MemoryWrite(new(), address, 32, terms.Constant(9, 32)));
            builder.Blocks.Add(new(block, [], statements.ToImmutableArray(), new Return(write ? [] : [new(new(SlotKind.Integer), terms.Concat(result, terms.Constant(0, 32)))])));
            return (builder.Freeze(), names);
        }
    }
}
