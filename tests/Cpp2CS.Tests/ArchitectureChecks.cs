using System.Reflection;
using Cpp2CS.Calls;
using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Output;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Recovery.Runtime;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;
using Cpp2CS.Tests.Execution;

namespace Cpp2CS.Tests;

/// <summary>用匹配输入提供类型与运行时定义；证明边界使用独立的小型托管方法体。</summary>
internal static class ArchitectureChecks
{
    public static int Run(string binary, string metadata, string cache)
    {
        var facts = FactsBuilder.Build(binary, metadata, options: new RecoveryOptions { FactCacheFile = Path.GetFullPath(cache) });
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var checks = new Assertions();
        Convergence(checks, types);
        Identities(checks, types);
        EntryKinds(checks, facts, types);
        Templates(checks, types);
        Barriers(checks, types);
        Verdicts(checks);
        return checks.Finish("架构边界");
    }

    private static void Convergence(Assertions check, ManagedTypes types)
    {
        var phi = new PhiSym(new Block(0), new object(), 32);
        var solution = new TypeSolution();
        check.Equal(TypeSolveState.Changed, solution.Accept(new() { [phi] = types.Int32 }), "第一次类型解");
        check.Equal(TypeSolveState.Stable, solution.Accept(new() { [phi] = types.Int32 }), "相同类型解收敛");
        check.Equal(TypeSolveState.Changed, solution.Accept(new() { [phi] = types.Int64 }), "类型变化继续求解");
        check.Equal(TypeSolveState.Cycle, solution.Accept(new() { [phi] = types.Int32 }), "类型循环不能当成稳定");
        var growing = new TypeSolution();
        var state = new Dictionary<PhiSym, TypeRef?>();
        TypeSolveState result = default;
        for (var i = 0; i < 65; i++)
        {
            state[new PhiSym(new Block((ulong)i), new object(), 32)] = types.Int32;
            result = growing.Accept(state);
            if (i == 3) check.Equal(TypeSolveState.Changed, result, "超过两轮仍继续求解");
        }
        check.Equal(TypeSolveState.BudgetExceeded, result, "预算耗尽不能当成收敛");
    }

    private static void Identities(Assertions check, ManagedTypes types)
    {
        var owner = Type("Generic", 1);
        owner.GenericParameters = [new() { Name = "T", Position = 0, Attributes = 0 }];
        var definition = Method(owner, ".ctor", 1);
        var reference = new GenericParameterRef("T", false, 0) { Binding = new(NativeBindingKind.Reference, types.Object, 1) };
        var scalar = reference with { Binding = new(NativeBindingKind.Scalar, types.Int32, 1) };
        var a = new MethodRef(definition, [reference], []);
        var b = new MethodRef(definition, [scalar], []);
        check.Equal(a, b, "托管泛型身份不包含原生布局");
        check.True(new MethodRequest(a, 1) != new MethodRequest(b, 1), "分析缓存区分原生布局");
        var entries = new NativeMethodEntry[]
        {
            new(new(definition, [types.Int32], []), 1),
            new(new(definition, [types.String], []), 3),
            new(new(definition, [types.Object], []), 2),
        };
        check.Equal(entries[2], MethodEntries.SelectDefinition(entries), "定义选择引用共享见证");
        check.Equal(MethodEntries.SelectDefinition(entries), MethodEntries.SelectDefinition(entries.Reverse()), "定义选择不受枚举顺序影响");
        var local = new LocalValue(new Variable(Storage.Temp(1), 1), types.Object, 64);
        var rootMethod = new MethodRef(Method(Type("Caller", 2), "Run", 2), [], []);
        var edge = new ManagedEdge(4, [new(local, new NewObjectValue(entries[0].Instance, []) { Transparent = true })]);
        var body = new ManagedBody(rootMethod, [new(0, [new ManagedJump(0, edge)]), new(4, [new ManagedReturn(4, null)])]);
        var root = new MethodRecoveryResult(rootMethod, 0, body, []);
        var dependencies = new List<MethodRecoveryResult>();
        var provider = new MissingDefinitions();
        DependencyClosure.Complete([root], dependencies, new() { [rootMethod.Method] = root }, provider);
        check.Equal(definition, provider.Requests.Single(), "边复制中的实例依赖转为定义请求");
        var problems = new Dictionary<ManagedBody, EmissionProblem>();
        DependencyClosure.Validate([root, .. dependencies], problems);
        check.True(problems.ContainsKey(body), "未写出的透明依赖阻止调用方发布");
    }

    private static void Templates(Assertions check, ManagedTypes types)
    {
        var owner = Type("Storage", 10);
        var ownerRef = new DefinitionRef(owner, []);
        var first = new FieldDef { Index = 10, Owner = owner, Name = "first", Type = types.Int32, Attributes = FieldAttributes.Private, Offset = 16 };
        var second = new FieldDef { Index = 11, Owner = owner, Name = "second", Type = types.Int32, Attributes = FieldAttributes.Private, Offset = 20 };
        owner.Fields = [first, second];
        var definition = Method(owner, "Set", 10);
        definition.Parameters = [new ParameterDef("value", types.Int32, 0, null, false)];
        owner.Methods = [definition];
        var method = new MethodRef(definition, [], []);
        var self = new ArgumentValue(-1, ownerRef, 64);
        FieldValue Field(ManagedValue receiver, FieldDef field) => new(receiver, new FieldRef(field, ownerRef), types.Int32, 32);
        var input = new ArgumentValue(0, types.Int32, 32);
        var template = new ManagedBody(method, [new(0, [new ManagedStore(0, Field(self, first), input),
            new ManagedStore(4, Field(self, second), input), new ManagedReturn(8, null)])]);
        MethodRecoveryResult? Summary(MethodRef requested) => requested.Method == definition ? new(method, 0, template, []) : null;
        var caller = new MethodRef(Method(Type("Consumer", 11), "Write", 11), [], []);
        var receiver = new ArgumentValue(0, ownerRef, 64);
        var value = new ArgumentValue(1, types.Int32, 32);
        ManagedBody Body(ManagedValue last) => new(caller, [new(0,
        [
            new ManagedStore(0, Field(receiver, first) with { Pending = (0, "待证字段") }, value),
            new ManagedStore(4, Field(receiver, second) with { Pending = (4, "待证字段") }, last),
            new ManagedReturn(8, null),
        ])]);
        var fields = new FieldAccessModel(types, caller, Summary);
        var recovery = new TemplateRecovery(types, caller, Summary, fields);
        var success = recovery.Run(Body(value), new Dictionary<Variable, PendingConstruction>(), 0);
        check.Equal(0, success.Holes.Count, "两次字段写入的模板证明成功");
        check.True(success.Body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Any(c => c.Inlined && c.Invocation.Method == method), "证明区域被替换成调用");
        var failure = recovery.Run(Body(new ConstantValue(7, types.Int32, 32)), new Dictionary<Variable, PendingConstruction>(), 0);
        check.True(failure.Holes.Count > 0, "写入不一致时保留缺口");
        check.True(!failure.Body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Any(c => c.Inlined), "失败的证明不改写成调用");
        var inaccessible = new TypeDef { Index = 12, Name = "Hidden", Namespace = "Tests", Assembly = "Other.dll", Token = 0,
            Attributes = TypeAttributes.NotPublic, IsValueType = false, IsEnum = false };
        var exposed = new FieldDef { Index = 12, Owner = inaccessible, Name = "value", Type = types.Int32, Offset = 16, Attributes = FieldAttributes.Public };
        check.True(!fields.Accessible(new(exposed, new DefinitionRef(inaccessible, [])), null), "公共字段不能绕过声明类型的权限");
    }

    private static void EntryKinds(Assertions check, ProgramFacts facts, ManagedTypes types)
    {
        var entries = new MethodEntries(facts, types);
        var thunks = facts.Registrations.Entries.Where(e => e.Kind == EntryKind.AdjustorThunk
            && e.Method is { Method.Address: not 0 } && e.Address != e.Method.Method.Address).ToArray();
        check.True(thunks.Length > 0, "输入包含可检查的值类型调整桩");
        check.True(thunks.All(e => entries.Of(e.Method!) == e.Method!.Method.Address), "普通方法索引始终指向本体，不受调整桩地址影响");
        var generic = facts.Registrations.Entries.Where(e => e.Kind == EntryKind.GenericMethod && e.Method is not null)
            .GroupBy(e => e.Method!).ToDictionary(g => g.Key, g => g.Select(e => e.Address).ToHashSet());
        check.True(entries.Definitions.Where(e => e.Instance.Method.Address == 0)
            .All(e => generic.TryGetValue(e.Instance, out var bodies) && bodies.Contains(e.Address)), "泛型定义见证来自方法本体注册");
    }

    private static void Barriers(Assertions check, ManagedTypes types)
    {
        var context = new BarrierContext(types);
        check.True(RuntimeOps.Of(OpKind.MemoryBarrier)!.Lower!(context, out var terminal), "内存屏障可下降");
        check.True(terminal is null && context.Statements is [ManagedCall { Invocation.Method.Method.Name: "MemoryBarrier" }], "内存屏障保留为托管调用");
        context.Statements.Clear();
        check.True(RuntimeOps.Of(OpKind.WriteBarrier)!.Lower!(context, out _) && context.Statements.Count == 0, "GC 写屏障由托管存储承担");
    }

    private static void Verdicts(Assertions check)
    {
        check.Equal(ExecutionVerdict.Partial, ExecutionVerdicts.Classify(32, 30, 0), "部分种子通过不能称为完整验证");
        check.Equal(3, ExecutionVerdicts.ExitCode([]), "空清单不能成功");
        check.Equal(3, ExecutionVerdicts.ExitCode([ExecutionVerdict.NotWritten]), "没有写出不能成功");
        check.Equal(3, ExecutionVerdicts.ExitCode([ExecutionVerdict.Verified, ExecutionVerdict.NotCheckable]), "不支持的用例使验证不完整");
        check.Equal(1, ExecutionVerdicts.ExitCode([ExecutionVerdict.Mismatch, ExecutionVerdict.Partial]), "差异优先报告失败");
        check.Equal(0, ExecutionVerdicts.ExitCode([ExecutionVerdict.Verified]), "全部请求用例通过才成功");
    }

    private static TypeDef Type(string name, int index) => new()
    {
        Index = index, Name = name, Namespace = "Tests", Assembly = "Tests.dll", Token = 0,
        Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false,
    };

    private static MethodDef Method(TypeDef owner, string name, int index) => new()
    {
        Index = index, Owner = owner, Name = name, Token = 0, Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1,
    };

    private sealed class MissingDefinitions : IMethodResults
    {
        public List<MethodDef> Requests { get; } = [];
        public MethodRecoveryResult RecoverDefinition(MethodDef method)
        {
            Requests.Add(method);
            return new(MethodRef.Open(method), 0, null, [new(0, "无定义体")]);
        }
        public MethodRecoveryResult Recover(MethodRef method, ulong entry) => throw new NotSupportedException();
        public MethodRecoveryResult RecoverInstance(MethodRef method, ulong entry) => throw new NotSupportedException();
    }

    private sealed class BarrierContext(ManagedTypes types) : IRuntimeLowering
    {
        public ManagedTypes Types => types;
        public Call Call { get; } = new(0, CallKind.Direct, new Const(0, 64));
        public List<ManagedStatement> Statements { get; } = [];
        public void Emit(ManagedStatement statement) => Statements.Add(statement);
        public RuntimeOp Op => new(OpKind.MemoryBarrier, null);
        public IReadOnlyList<Sym> Arguments => [];
        public TypeRef? ClassOperand => throw new NotSupportedException();
        public Sym Result => throw new NotSupportedException();
        public bool InFault => throw new NotSupportedException();
        public ManagedValue View(Sym sym, TypeRef? expected) => throw new NotSupportedException();
        public TypeRef? TypeOf(Sym sym) => throw new NotSupportedException();
        public LocalValue Local(Sym sym, TypeRef type) => throw new NotSupportedException();
        public Sym? Pointee(int value) => throw new NotSupportedException();
        public ManagedValue? Location(int argument, TypeRef type) => throw new NotSupportedException();
        public ManagedValue Field(Sym receiver, FieldRef field) => throw new NotSupportedException();
        public void AwaitConstruction() => throw new NotSupportedException();
        public bool Absorb(Sym target) => throw new NotSupportedException();
        public bool KnownNonNull(Sym target) => throw new NotSupportedException();
        public bool AbsorbBounds(Sym index, Sym length) => throw new NotSupportedException();
        public bool InCatchOf(Sym exception) => throw new NotSupportedException();
        public MethodRef? ExceptionConstructor(string fullName) => throw new NotSupportedException();
        public ManagedValue Hole(string reason, TypeRef? type) => throw new NotSupportedException();
        public Sym? ClassOwner(Sym klass) => throw new NotSupportedException();
        public bool InitializesNext(TypeRef owner) => throw new NotSupportedException();
    }
}
