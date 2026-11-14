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
        ExpressionAccessorChecks(checks);
        ForwardingChecks(checks);
        ConditionalAccessorChecks(checks);
        PlacementChecks(checks);
        LocalAccessorChecks(checks);
        GenericAccessorChecks(checks);
        ConstructorChecks(checks);
        StraightConstructorChecks(checks);
        PairingConstructorChecks(checks);
        PairedBaseLoweringChecks(checks);
        StraightAllocationChecks(checks);
        var extra = Body(getter, new ManagedStore(0, field, argument), new ManagedReturn(1, field));
        checks.True(AccessorTemplates.Read(extra).Status == AccessorTemplateStatus.NotTemplate, "多一条写入不是模板");
        checks.True(AccessorTemplates.Read(Body(getter, new ManagedCall(0, new(MethodRef.Open(getter), receiver, [], false), local),
            new ManagedReturn(1, local))).Status == AccessorTemplateStatus.NotTemplate, "其他调用不是模板");
        checks.True(AccessorTemplates.Read(Body(getter, new ManagedAssignment(0, local, field), new ManagedReturn(1,
            new BinaryValue(BinaryOperator.Add, local, local, f.Integer, 32)))).Status == AccessorTemplateStatus.Complete, "单定义局部可在纯表达式中复用");
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

    private static void StraightConstructorChecks(Assertions checks)
    {
        var f = new Fixture();
        f.Owner.BaseType = f.Types.Object; f.Caller.BaseType = f.OwnerType;
        var root = f.Method(f.Types.Object.Definition, ".ctor", true, false, []);
        var one = f.Method(f.Owner, ".ctor", true, false, [f.Integer]);
        var constant = f.Method(f.Owner, ".ctor", true, false, []);
        var child = f.Method(f.Caller, ".ctor", true, false, [f.Integer]);
        var secondDef = new FieldDef { Index = 2, Owner = f.Owner, Name = "Other", Type = f.Integer,
            Attributes = FieldAttributes.Private, Offset = 20, Token = 0x04000003 };
        var second = new FieldRef(secondDef, f.OwnerType); f.Owner.Fields = [.. f.Owner.Fields, secondDef];
        ManagedBody Body(MethodDef m, params ManagedStatement[] statements) => new(MethodRef.Open(m), [new(0, statements)]);
        ManagedCall Call(MethodDef caller, MethodDef target, params ManagedValue[] args) => new(0,
            new(MethodRef.Open(target), new ArgumentValue(-1, MethodRef.Open(caller).DeclaringType, 64), args, false), null);
        ManagedStore Store(MethodDef m, FieldRef field, ManagedValue value) => new(1,
            new FieldValue(new ArgumentValue(-1, MethodRef.Open(m).DeclaringType, 64), field, value.Type, value.Width), value);
        var parameter = new ArgumentValue(0, f.Integer, 32);
        var literal = new ConstantValue(7, f.Integer, 32);
        var boolean = new DefinitionRef(f.Program.Types.Single(t => t.Namespace == "System" && t.Name == "Boolean"), []);
        var narrow = new ArgumentValue(0, boolean, 64);
        var representation = new ConversionValue(ConversionKind.ZeroExtend,
            new BinaryValue(BinaryOperator.And, new ConversionValue(ConversionKind.ZeroExtend, narrow, f.Integer, 32),
                new ConstantValue(255, f.Integer, 32), f.Integer, 32), boolean, 8);
        checks.True(ConstructorTemplates.Normalize(representation, f.Types).Equals(narrow), "窄标量表示经公共项规范化证明为原形参");
        var signedByte = new DefinitionRef(f.Program.Types.Single(t => t.Namespace == "System" && t.Name == "SByte"), []);
        checks.True(ConstructorTemplates.Normalize(new ConversionValue(ConversionKind.SignExtend,
            new ConstantValue(255, signedByte, 8), f.Integer, 32), f.Types) is ConstantValue { Bits: uint.MaxValue }, "常量符号扩展使用公共位型语义");
        var bodies = new Dictionary<MethodDef, ManagedBody>
        {
            [root] = Body(root, new ManagedReturn(0, null)),
            [one] = Body(one, Call(one, root), Store(one, f.Field, parameter), new ManagedReturn(2, null)),
            [constant] = Body(constant, Call(constant, root), Store(constant, f.Field, literal), new ManagedReturn(2, null)),
            [child] = Body(child, Call(child, one, parameter), new ManagedReturn(2, null)),
        };
        ConstructorTemplates Templates() => new(new BodySource(bodies.GetValueOrDefault), f.Types);
        ConstructorQuery Query() => new(f.Types, Templates());
        var access = new ConstructorAccess(MethodRef.Open(child), 0, f.OwnerType, ConstructorAnchor.Allocation);
        f.Owner.Methods = [one];
        var answer = Query().Resolve(access, [new(f.Field, literal)]);
        checks.True(answer.Method?.Method == one && answer.Arguments.SequenceEqual([literal]) && answer.Writes.SequenceEqual([0]), "形参字段逐项绑定并消费写入");
        f.Owner.Methods = [constant];
        checks.True(Query().Resolve(access, [new(f.Field, literal)]).Method?.Method == constant, "常量字段匹配");
        checks.True(Query().Resolve(access, [new(f.Field, literal with { Bits = 8 })]).Failure?.Code == "inline.Constructor.Template", "常量不同拒绝");
        checks.True(Templates().Alternatives(MethodRef.Open(child)).Last().Fields is [{ Value: ArgumentValue { Index: 0 } }], "基类直线模板展开为最外层形参");
        bodies[one] = Body(one, Call(one, root), Store(one, f.Field, parameter), Store(one, second, parameter), new ManagedReturn(3, null));
        f.Owner.Methods = [one, constant];
        answer = Query().Resolve(access, [new(f.Field, literal), new(second, literal)]);
        checks.True(answer.Method?.Method == one && answer.Writes.Count == 2, "多个匹配候选取字段最多的");
        checks.True(Query().Resolve(access, [new(f.Field, literal), new(second, literal with { Bits = 8 })]).Method?.Method == constant,
            "形参冲突的候选不匹配");
        f.Owner.Methods = [one];
        checks.True(Query().Resolve(access, [new(f.Field, literal), new(second, literal with { Bits = 8 })]).Failure?.Message.Contains("绑定冲突") == true,
            "形参冲突报告差异");
        checks.True(Query().Resolve(access, [new(f.Field, literal)]).Failure?.Message.Contains("缺少字段") == true, "写入缺字段不匹配");
        checks.True(Query().Resolve(access, [new(f.Field, literal), new(f.Field, literal), new(second, literal)]).Failure is not null,
            "组内重复目标字段不匹配");
        var duplicate = f.Method(f.Owner, ".ctor", true, false, [f.Integer]);
        bodies[duplicate] = Body(duplicate, Call(duplicate, root), Store(duplicate, f.Field, parameter), Store(duplicate, second, parameter), new ManagedReturn(3, null));
        checks.True(Query().Resolve(access, [new(f.Field, literal), new(second, literal)]).Failure?.Code == "inline.Constructor.Ambiguous", "字段数并列报歧义");
        f.Owner.Methods = [one];
        bodies[one] = Body(one, Call(one, root), Store(one, f.Field, literal), new ManagedReturn(2, null));
        checks.True(Query().Resolve(access, [new(f.Field, literal)]).Failure?.Message.Contains("未绑定") == true, "未绑定形参不匹配");
        bodies[one] = Body(one, Call(one, root), Store(one, f.Field, parameter), Store(one, f.Field, literal), new ManagedReturn(3, null));
        var expanded = Templates().Get(one).Template;
        checks.True(expanded is { Overwritten: 1, Fields: [{ Value: ConstantValue { Bits: 7 } }] }, "重复模板字段保留最后一次并计数");
        bodies[one] = Body(one, Call(one, root), Store(one, f.Field, parameter), new ManagedReturn(2, null));
        var initialization = Query().Initialization(MethodRef.Open(child), [new ManagedBlock(0,
            [Store(child, f.Field, literal), new ManagedReturn(2, null)])]);
        checks.True(initialization.Method?.Method == one && initialization.Arguments.SequenceEqual([literal]), "基类入口字段绑定与消费");
        checks.True(Query().Initialization(MethodRef.Open(child), [new ManagedBlock(0,
            [Call(child, root), Store(child, f.Field, literal), new ManagedReturn(2, null)])]).Failure?.Code == "lowering.ConstructorInitialization",
            "已有祖先构造调用不补初始化");
        bodies[one] = Body(one, new ManagedCall(0, new(MethodRef.Open(one), parameter, [], false), null), new ManagedReturn(1, null));
        checks.True(Templates().Get(one).Failure?.Message.StartsWith("ManagedCall：", StringComparison.Ordinal) == true, "其他调用记录第一条语句种类");
        bodies[one] = Body(one, Call(one, root), Store(one, f.Field, new FieldValue(new ArgumentValue(-1, f.OwnerType, 64), f.Field, f.Integer, 32)), new ManagedReturn(2, null));
        checks.True(Templates().Get(one).Failure?.Code == "inline.Constructor.NotStraight", "字段读取不是直线模板值");
        bodies[one] = Body(one, Call(one, root), new ManagedReturn(1, null));
        var delegated = f.Method(f.Caller, ".ctor", true, false, []);
        bodies[delegated] = Body(delegated, Call(delegated, one, literal), new ManagedReturn(1, null));
        checks.True(Query().MatchInitialization(MethodRef.Open(child), []).Method?.Method == delegated,
            "基类形参不可绑定时才回退到同类其他构造");
        bodies[child] = Body(child, Call(child, delegated), new ManagedReturn(1, null));
        bodies[delegated] = Body(delegated, Call(delegated, child, literal), new ManagedReturn(1, null));
        checks.True(!Templates().Alternatives(MethodRef.Open(child)).Any(t => t.Call is null), "同类构造展开成环不能完全展开");
    }

    private static void PairingConstructorChecks(Assertions checks)
    {
        var f = new Fixture(); f.Owner.BaseType = f.Types.Object; f.Caller.BaseType = f.OwnerType;
        var root = f.Method(f.Types.Object.Definition, ".ctor", true, false, []);
        var opaque = f.Method(f.Types.Object.Definition, ".ctor", true, false, [f.Integer]);
        var parent = f.Method(f.Owner, ".ctor", true, false, [f.Integer]);
        var shortCtor = f.Method(f.Owner, ".ctor", true, false, []);
        var child = f.Method(f.Caller, ".ctor", true, false, []);
        var secondDef = new FieldDef { Index = 2, Owner = f.Owner, Name = "Other", Type = f.Integer,
            Attributes = FieldAttributes.Private, Offset = 20, Token = 0x04000003 };
        var second = new FieldRef(secondDef, f.OwnerType); f.Owner.Fields = [.. f.Owner.Fields, secondDef];
        var self = new ArgumentValue(-1, f.OwnerType, 64); var parameter = new ArgumentValue(0, f.Integer, 32);
        var literal = new ConstantValue(7, f.Integer, 32);
        ManagedCall Call(MethodDef target, params ManagedValue[] args) => new(0, new(MethodRef.Open(target), self, args, false), null);
        ManagedStore Store(FieldRef field, ManagedValue value) => new(0, new FieldValue(self, field, f.Integer, 32), value);
        ManagedBody Body(MethodDef method, params ManagedStatement[] statements) => new(MethodRef.Open(method), [new(0, statements)]);
        var bodies = new Dictionary<MethodDef, ManagedBody>
        {
            [root] = Body(root, new ManagedReturn(0, null)),
            // 被调方没有完整恢复体也能成为真实调用的配对目标。
            [parent] = Body(parent, Store(f.Field, parameter), Call(opaque, parameter), Store(second, literal), new ManagedReturn(0, null)),
        };
        ConstructorQuery Query() => new(f.Types, new(new BodySource(bodies.GetValueOrDefault), f.Types));
        var access = new ConstructorAccess(MethodRef.Open(child), 0, f.OwnerType, ConstructorAnchor.Base);
        ConstructorActualCall Actual(ManagedValue value) => new(MethodRef.Open(opaque), [new(value)]);
        ConstructorWrite[] writes = [new(f.Field, literal), new(second, literal, AfterCall: true)];
        var answer = Query().MatchInitialization(MethodRef.Open(child), writes, Actual(literal));
        checks.True(answer.Method?.Method == parent && answer.ConsumesCall && answer.Arguments.SequenceEqual([literal]), "非直线祖先调用配对并恢复直接基类调用");
        checks.True(Query().Resolve(access, writes, Actual(literal with { Bits = 8 })).Failure is not null, "真实调用与字段的形参绑定必须一致");
        checks.True(Query().Resolve(access, [new(f.Field, literal, AfterCall: true), new(second, literal)], Actual(literal)).Failure is not null, "调用前后的字段写入不能交换");
        checks.True(Query().MatchInitialization(MethodRef.Open(child), writes, Actual(literal with { Bits = 8 })).Failure?.Code == "lowering.ConstructorInitialization", "没有被模板消费的祖先调用仍触发保护");
        checks.True(Query().MatchInitialization(MethodRef.Open(child), writes, Actual(literal), unconsumedAncestor: true).Failure?.Code == "lowering.ConstructorInitialization", "消费一处调用不解除另一处祖先调用的保护");
        bodies[parent] = Body(parent, Store(f.Field, parameter), Call(opaque, literal), Store(second, literal), new ManagedReturn(0, null));
        checks.True(Query().Resolve(access, writes, Actual(literal with { Bits = 8 })).Failure?.Message.Contains("常量不同") == true, "祖先调用常量实参不同不配对");
        bodies[parent] = Body(parent, Call(root), Store(f.Field, parameter), new ManagedReturn(0, null));
        bodies[shortCtor] = Body(shortCtor, Call(opaque, literal), new ManagedReturn(0, null));
        answer = Query().Resolve(access, [new(f.Field, literal)], Actual(literal));
        checks.True(answer.Method?.Method == shortCtor && answer.ConsumesCall && answer.Writes.Count == 0, "消费真实调用优先于匹配更多字段但没有消费调用的候选");
        bodies[shortCtor] = Body(shortCtor, Call(root), new ManagedReturn(0, null));
        f.Owner.Methods = [shortCtor];
        answer = Query().Resolve(access, [], new(MethodRef.Open(root), []));
        checks.True(answer.Method?.Method == shortCtor && answer.ConsumesCall && answer.Failure is null, "同一候选的展开和配对都成立时取消费真实调用的对法");
        bodies[parent] = Body(parent, Store(f.Field, parameter), Call(root), Store(second, literal), new ManagedReturn(0, null));
        bodies[shortCtor] = Body(shortCtor, Store(f.Field, literal), Call(root), new ManagedReturn(0, null));
        f.Owner.Methods = [parent, shortCtor];
        answer = Query().Resolve(access, writes, new(MethodRef.Open(root), []));
        checks.True(answer.Method?.Method == parent && answer.Failure is null && answer.Writes.Count == 2,
            "较少字段候选的两种对法不覆盖更完整的唯一候选");
        bodies[parent] = Body(parent, Store(f.Field, literal with { Bits = 1 }), Call(opaque, literal), Store(f.Field, parameter), new ManagedReturn(0, null));
        f.Owner.Methods = [parent];
        answer = Query().Resolve(access, [new(f.Field, literal with { Bits = 1 }), new(f.Field, literal, AfterCall: true)], Actual(literal));
        checks.True(answer.Method?.Method == parent && answer.Writes.Count == 2, "同一字段跨调用的两次写入不能折叠");
        f.Owner.Methods = [shortCtor];
        // 父模板展开到更远一层，再在那一层配对；形参仍绑定到最外层。
        bodies[parent] = Body(parent, Call(opaque, parameter), new ManagedReturn(0, null));
        bodies[shortCtor] = Body(shortCtor, Call(parent, literal), new ManagedReturn(0, null));
        answer = Query().Resolve(access, [], Actual(literal));
        checks.True(answer.Method?.Method == shortCtor && answer.ConsumesCall, "递归展开后仍可在内层配对并替换实参");
        f.Owner.Methods = [parent];
        answer = Query().Resolve(access, [], Actual(literal));
        checks.True(answer.Method?.Method == parent && answer.Arguments.SequenceEqual([literal]) && answer.Writes.Count == 0,
            "仅在被配对调用中出现的形参也能完整绑定");
    }

    private static void StraightAllocationChecks(Assertions checks)
    {
        var f = new Fixture(explicitOwner: true); f.Owner.BaseType = f.Types.Object;
        var overlap = new FieldDef { Index = 2, Owner = f.Owner, Name = "Overlap", Type = f.Types.Int64,
            Attributes = FieldAttributes.Private, Offset = 16, Token = 0x04000003 };
        f.Owner.Fields = [.. f.Owner.Fields, overlap]; ((List<FieldDef>)f.Program.Fields).Add(overlap);
        var root = f.Method(f.Types.Object.Definition, ".ctor", true, false, []);
        var ctor = f.Method(f.Owner, ".ctor", true, false, [f.Integer]);
        var make = f.Method(f.Caller, "Create", false, true, [f.Integer]); make.ReturnType = f.OwnerType;
        var sink = f.Method(f.Caller, "Observe", true, true, [f.OwnerType]);
        var discard = f.Method(f.Caller, "Discard", true, true, [f.Integer]);
        var bodies = new Dictionary<MethodDef, ManagedBody>
        {
            [root] = new(MethodRef.Open(root), [new(0, [new ManagedReturn(0, null)])]),
            [ctor] = new(MethodRef.Open(ctor), [new(0, [new ManagedCall(0,
                new(MethodRef.Open(root), new ArgumentValue(-1, f.OwnerType, 64), [], false), null),
                new ManagedStore(1, new FieldValue(new ArgumentValue(-1, f.OwnerType, 64), f.Field, f.Integer, 32), new ArgumentValue(0, f.Integer, 32)),
                new ManagedReturn(2, null)])]),
        };
        var query = new ConstructorQuery(f.Types, new(new BodySource(bodies.GetValueOrDefault), f.Types));
        var catalog = RuntimeFunctionCatalog.Select(f.Spec.Layout.UnityVersion, f.Spec.Layout.Triple, f.Spec.Layout.DataModel);
        var allocation = catalog.Functions.First(op => op.Operation.Il?.Name == "NewObject" && op.Signature is not null);
        var calls = new CallNamingQuery(f.Binder, new NamingChecks.Map([new(MethodRef.Open(sink), BindingEntryKind.Ordinary)]),
            new NamingChecks.RuntimeMap(allocation), catalog);
        foreach (var mode in new[] { "Field", "Escape", "Read", "Linear", "Merge", "Partial", "Overlap", "Paired", "PairedUnused" })
        {
            var modeCalls = mode is "Paired" or "PairedUnused" ? new CallNamingQuery(f.Binder, new NamingChecks.Map([new(MethodRef.Open(root), BindingEntryKind.Ordinary)]),
                new NamingChecks.RuntimeMap(allocation), catalog) : calls;
            var t = new TermTable(); var head = new BlockIdentity(); var tail = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            var fn = new FunctionBuilder(t, head, 64, new(frame)) { ImageBase = image };
            var input = t.Atom(new EntryAtom(new(SlotKind.Integer)), 64); fn.Inputs.Add(new(new(SlotKind.Integer), input));
            var read = new ReadIdentity(); var klass = t.Atom(new ResultAtom(read), 64);
            var allocationId = new CallIdentity(); var value = t.Atom(new ResultAtom(allocationId), 64);
            var address = t.Apply(new CoreOperator(CoreOperation.Add), 64, value, t.Constant(16, 64));
            var statements = new List<Statement>
            {
                new MemoryRead(read, t.Apply(new CoreOperator(CoreOperation.Add), 64, image, t.Constant(128, 64)), 64, klass),
                new Call(allocationId, new ImageFunction(20), [new(new(SlotKind.Integer), klass)], [new(new(SlotKind.Integer), value)]) { Trace = new(32) },
            };
            if (mode is "Paired" or "PairedUnused") statements.Add(new Call(new(), new ImageFunction(10), [new(new(SlotKind.Integer), value), new(new(SlotKind.Integer, 1), t.Constant(0, 64))], []));
            if (mode == "Escape") statements.Add(new Call(new(), new ImageFunction(10), [new(new(SlotKind.Integer), value), new(new(SlotKind.Integer, 1), t.Constant(0, 64))], []));
            if (mode == "Read") { var id = new ReadIdentity(); statements.Add(new MemoryRead(id, address, 32, t.Atom(new ResultAtom(id), 32))); }
            if (mode == "Overlap") statements.Add(new MemoryWrite(new(), address, 64, t.Constant(9, 64)));
            int width = mode == "Partial" ? 16 : 32;
            var store = new MemoryWrite(new(), address, width, t.Slice(input, 0, width));
            if (mode == "Merge")
            {
                var other = new BlockIdentity();
                fn.Blocks.Add(new(head, [], [.. statements], new Branch(t.Apply(new CoreOperator(CoreOperation.Equal), 1, input, t.Constant(0, 64)), tail, other)));
                fn.Blocks.Add(new(other, [], [], new Jump(tail)));
                fn.Blocks.Add(new(tail, [], [store], new Return(mode == "PairedUnused" ? [] : [new(new(SlotKind.Integer), value)])));
            }
            else if (mode == "Linear")
            {
                fn.Blocks.Add(new(head, [], [.. statements], new Jump(tail)));
                fn.Blocks.Add(new(tail, [], [store], new Return(mode == "PairedUnused" ? [] : [new(new(SlotKind.Integer), value)])));
            }
            else
            {
                statements.Add(store);
                fn.Blocks.Add(new(head, [], [.. statements], new Return(mode == "PairedUnused" ? [] : [new(new(SlotKind.Integer), value)])));
            }
            var names = NamingFacts.Empty with { Slots = NamingFacts.Empty.Slots.Add(128, Outcome<MetadataEntity>.Success(new ClassEntity(f.OwnerType))) };
            var lowered = new IntegerLowering(fn.Freeze(), MethodRef.Open(mode == "PairedUnused" ? discard : make), f.Binder, f.Types, calls: modeCalls, spec: f.Spec, names: names, constructors: query).Run();
            if (mode is "Field" or "Linear" or "Paired" or "PairedUnused")
            {
                var created = lowered.Body?.Blocks[0].Statements.OfType<ManagedAssignment>().SingleOrDefault(a => a.Value is NewObjectValue)?.Value as NewObjectValue;
                checks.True(created is { Constructor.Method: var selected, Arguments.Count: 1 } && selected == ctor
                    && !lowered.Body!.Blocks.SelectMany(b => b.Statements).OfType<ManagedStore>().Any(), "分配处绑定实参并移除私有字段写入：" + lowered.Failure);
                using var emission = new EmissionFixture(f);
                checks.True(lowered.Body is { } complete && emission.Emitter.Emit([complete]).Count == 0, "直线构造 newobj 通过输出检查");
            }
            else checks.True(lowered.Failure?.Reason.Code == "inline.Constructor.Template", "首次其他使用、汇合或不完整字段截断写入组：" + mode + " " + lowered.Failure);
        }
        var child = f.Method(f.Caller, ".ctor", true, false, [f.Integer]); f.Caller.BaseType = f.OwnerType;
        var (native, _) = f.Function(f.Field, true);
        var baseBody = new IntegerLowering(native, MethodRef.Open(child), f.Binder, f.Types, calls: f.Calls, spec: f.Spec, constructors: query).Run();
        checks.True(baseBody.Body?.Blocks[0].Statements is [ManagedCall { Invocation.Method.Method: var selectedBase, Invocation.Arguments.Count: 1 }, ManagedReturn]
            && selectedBase == ctor, "基类入口写入转为带参调用：" + baseBody.Failure);
    }

    private static void PairedBaseLoweringChecks(Assertions checks)
    {
        var f = new Fixture(); f.Owner.BaseType = f.Types.Object; f.Caller.BaseType = f.OwnerType;
        var root = f.Method(f.Types.Object.Definition, ".ctor", true, false, []);
        var parent = f.Method(f.Owner, ".ctor", true, false, [f.Integer]);
        var child = f.Method(f.Caller, ".ctor", true, false, [f.Integer]);
        var own = new FieldDef { Index = 2, Owner = f.Caller, Name = "Initial", Type = f.Integer,
            Attributes = FieldAttributes.Private, Offset = 24, Token = 0x04000003 };
        f.Caller.Fields = [own]; ((List<FieldDef>)f.Program.Fields).Add(own);
        var self = new ArgumentValue(-1, f.OwnerType, 64);
        var body = new ManagedBody(MethodRef.Open(parent), [new(0, [new ManagedCall(0,
            new(MethodRef.Open(root), self, [], false), null), new ManagedStore(0,
            new FieldValue(self, f.Field, f.Integer, 32), new ArgumentValue(0, f.Integer, 32)), new ManagedReturn(0, null)])]);
        var query = new ConstructorQuery(f.Types, new(new BodySource(m => m == parent ? body : null), f.Types));
        var native = f.Function(f.Field, true).Function;
        var fn = new FunctionBuilder(native.Terms, native.Entry, 64, native.Frame); fn.Inputs.AddRange(native.Inputs);
        var call = new Call(new(), new ImageFunction(10), [new(new(SlotKind.Integer), native.Inputs[0].Value),
            new(new(SlotKind.Integer, 1), native.Terms.Constant(0, 64))], []);
        var block = native.Blocks[0];
        var address = native.Terms.Apply(new CoreOperator(CoreOperation.Add), 64, native.Inputs[0].Value, native.Terms.Constant(24, 64));
        var before = new MemoryWrite(new(), address, 32, native.Terms.Constant(1, 32));
        var after = new MemoryWrite(new(), address, 32, native.Terms.Constant(2, 32));
        fn.Blocks.Add(block with { Statements = block.Statements.Insert(0, call).Insert(0, before).Add(after) });
        var calls = new CallNamingQuery(f.Binder, new NamingChecks.Map([new(MethodRef.Open(root), BindingEntryKind.Ordinary)]), new NamingChecks.RuntimeMap(), RuntimeFunctionCatalog.Select(f.Spec.Layout.UnityVersion, f.Spec.Layout.Triple, f.Spec.Layout.DataModel));
        var lowered = new IntegerLowering(fn.Freeze(), MethodRef.Open(child), f.Binder, f.Types, calls: calls, spec: f.Spec, constructors: query).Run();
        checks.True(lowered.Body?.Blocks[0].Statements is [ManagedStore, ManagedCall { Invocation.Method.Method: var selected, Invocation.Arguments.Count: 1 }, ManagedStore, ManagedReturn]
            && selected == parent, "祖先调用与模板字段被消费，自有字段保留在调用前后：" + lowered.Failure);
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
            .Failure?.Code == "inline.Constructor.NotStraight", "基类构造未恢复单列非直线原因");
        bodies[parentCtor] = Body(parentCtor, new ManagedReturn(0, null));
        checks.True(!Templates().IsEmpty(parentCtor), "有基类时裸 return 不是空模板");
        bodies[parentCtor] = Body(parentCtor, Base(parentCtor, objectCtor), new ManagedReturn(1, null));
        var query = new ConstructorQuery(f.Types, Templates());
        var initialization = query.Initialization(MethodRef.Open(childCtor), [new(0, [new ManagedReturn(0, null)])]);
        checks.True(initialization.Method?.Method == parentCtor, "锚点 A 查询选中唯一空基类构造");
        checks.True(query.Initialization(MethodRef.Open(childCtor), [new(0, [Base(childCtor, objectCtor), new ManagedReturn(1, null)])])
            .Failure?.Code == "lowering.ConstructorInitialization", "已有祖先构造调用时不重复补初始化");
        var extra = f.Method(f.Owner, ".ctor", true, false, [f.Integer]);
        checks.True(query.Resolve(new(MethodRef.Open(childCtor), 0, f.OwnerType, ConstructorAnchor.Base)).Method?.Method == parentCtor,
            "基类额外有未恢复候选不妨碍唯一匹配");
        checks.True(query.Resolve(new(MethodRef.Open(childCtor), 0, f.OwnerType, ConstructorAnchor.Allocation)).Method?.Method == parentCtor,
            "分配类额外有未恢复候选不妨碍唯一匹配");
        f.Owner.Methods = [parentCtor];
        f.Owner.Methods = [extra];
        checks.True(query.Resolve(new(MethodRef.Open(childCtor), 0, f.OwnerType, ConstructorAnchor.Base)).Failure?.Code == "inline.Constructor.NotStraight",
            "唯一候选未完整恢复单列非直线原因");
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
            // Deferred：中间隔着另一次没有构造的同类分配；Mixed：构造调用只在一条路径上。两者都不能写出。
            if (mode == "Mixed") checks.True(body.Failure?.Reason.Code == "lowering.Allocation.Deferred.Flow", "部分路径的显式构造保留洞");
            else if (mode == "Deferred") checks.True(body.Failure?.Reason.Code.StartsWith("lowering.Allocation.", StringComparison.Ordinal) == true,
                "未构造的分配保留洞（" + body.Failure?.Reason.Code + "）");
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
        public Fixture(bool generic = false, bool genericField = false, bool valueOwner = false, bool explicitOwner = false)
        {
            TypeDef Define(string name, string ns = "", bool value = false, TypeAttributes layout = 0) { var type = new TypeDef { Index = definitions.Count,
                Assembly = ns == "System" ? "mscorlib.dll" : "InliningChecks.dll", Namespace = ns, Name = name, Token = (uint)(0x02000001 + definitions.Count),
                Attributes = TypeAttributes.Public | layout, IsValueType = value, IsEnum = false, Size = 64, PackingSize = 0, ClassSizeIsDefault = true }; definitions.Add(type); return type; }
            foreach (var name in new[] { "Object", "String", "Boolean", "Char", "SByte", "Byte", "Int16", "UInt16", "Int32", "UInt32", "Int64", "UInt64", "Single", "Double", "IntPtr", "UIntPtr", "RuntimeTypeHandle", "RuntimeFieldHandle", "RuntimeMethodHandle", "TypedReference", "Void" })
                Define(name, "System", name is not ("Object" or "String"));
            Integer = new DefinitionRef(definitions.Single(t => t.Name == "Int32"), []); Void = new DefinitionRef(definitions.Single(t => t.Name == "Void"), []);
            Owner = Define("Owner", value: valueOwner, layout: explicitOwner ? TypeAttributes.ExplicitLayout : 0); Caller = Define("Caller");
            if (generic) Owner.GenericParameters = [new() { Name = "T", Position = 0, Attributes = 0 }];
            OwnerType = new(Owner, Owner.GenericParameters.Select(p => (TypeRef)new GenericParameterRef(p.Name, false, p.Position) { Parameter = p }).ToArray());
            var field = new FieldDef { Index = 0, Owner = Owner, Name = "Value", Type = genericField ? OwnerType.Arguments[0] : Integer, Attributes = FieldAttributes.Private, Offset = 16, Token = 0x04000001 };
            var shared = new FieldDef { Index = 1, Owner = Owner, Name = "Shared", Type = Integer, Attributes = FieldAttributes.Private | FieldAttributes.Static, Offset = 0, Token = 0x04000002 };
            Owner.Fields = [field, shared]; Field = new(field, OwnerType); Shared = new(shared, OwnerType);
            Program = new() { MetadataVersion = 31, Types = definitions, Methods = methods, Fields = new List<FieldDef> { field, shared }, RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
                Assemblies = definitions.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key),
                    Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
            var layouts = new FieldLayouts(Spec, 8, 8); Types = new(Program, layouts, 8); Binder = new(new(layouts), new Aapcs64());
            var catalog = RuntimeFunctionCatalog.Select(Spec.Layout.UnityVersion, Spec.Layout.Triple, Spec.Layout.DataModel);
            Calls = new(Binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(), catalog);
        }
        public MethodDef Method(TypeDef owner, string name, bool write, bool statics, TypeRef[]? parameters = null, bool virtualMethod = false, int slot = -1)
        {
            var method = new MethodDef { Index = methods.Count, Owner = owner, Name = name, Token = (uint)(0x06000001 + methods.Count),
                Attributes = MethodAttributes.Public | (statics ? MethodAttributes.Static : 0) | (virtualMethod ? MethodAttributes.Virtual : 0)
                    | (name == ".ctor" ? MethodAttributes.SpecialName | MethodAttributes.RTSpecialName : 0), ImplAttributes = 0, Slot = slot,
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
