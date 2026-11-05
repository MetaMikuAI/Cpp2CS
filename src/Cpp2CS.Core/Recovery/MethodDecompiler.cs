using Cpp2CS.Calls;
using Cpp2CS.Facts;
using Cpp2CS.Facts.Derived;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Lifting;
using Cpp2CS.Recovery.Calls;
using Cpp2CS.Recovery.Control;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Memory;
using Cpp2CS.Recovery.Shape;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery;

/// <summary>一次方法分析的各层产物，供下降与检查使用。</summary>
public sealed record MethodAnalysis(MethodRef Method, ulong Entry, MachineSignature Signature, MachineFunction Function,
    IdiomResult Idioms, MemoryLayout Memory, ValueModel Values)
{
    internal MethodEnvironment Environment { get; init; } = null!;
    /// <summary>路径拆分复制的合流块数。</summary>
    public int Splits { get; init; }
}

/// <summary>
/// 单个托管方法的恢复入口：签名 → 提升 → L2 → 符号值 → 类型 → 下降。
/// 实例不是线程安全的，并行时每个线程各用一个。
/// </summary>
public sealed class MethodDecompiler
{
    private readonly ProgramFacts facts;
    private readonly ManagedTypes types;
    private readonly FunctionLifter lifter;
    private readonly IdiomRewriter rewriter;
    private readonly ManagedAbi abi;
    private readonly CallShapes shapes;
    private readonly NativeMethodFacts native;
    private readonly Dictionary<MethodRequest, MethodRecoveryResult?> summaries = [];
    private MethodEntries? entries;

    public MethodDecompiler(ProgramFacts facts, ManagedTypes types)
    {
        this.facts = facts;
        this.types = types;
        lifter = new FunctionLifter(facts) { InlinesClosures = true };
        rewriter = new IdiomRewriter(facts) { RecordFilter = _ => false, RecoverUnusedInputs = true };
        abi = new ManagedAbi(facts.Layouts);
        shapes = new CallShapes(facts, abi, rewriter.UnusedInput);
        native = new NativeMethodFacts(facts, lifter, rewriter);
    }

    public ManagedTypes Types => types;
    public ProgramFacts Facts => facts;
    public CallShapes Shapes => shapes;

    public MethodRecoveryResult Recover(MethodRef method, ulong entry) => Declaration(method, entry) ?? PlatformInvoke(method, entry) ?? Run(method, entry);

    /// <summary>恢复泛型类型或泛型方法的封闭实例，方法体以封闭类型表达。</summary>
    public MethodRecoveryResult RecoverInstance(MethodRef method, ulong entry) => Declaration(method, entry) ?? PlatformInvoke(method, entry) ?? Run(method, entry);

    /// <summary>从已知原生实例恢复开放泛型体：类型参数带上实例的原生绑定，输出保留类型参数。</summary>
    public MethodRecoveryResult RecoverShared(MethodRef instance, ulong entry)
    {
        var open = BindShared(instance, entry);
        return Declaration(open, entry) ?? PlatformInvoke(open, entry) ?? Run(open, entry);
    }

    /// <summary>开放泛型的托管身份及当前入口提供的原生布局见证。</summary>
    public MethodRef BindShared(MethodRef instance, ulong entry)
    {
        var open = MethodRef.Open(instance.Method);
        return open with
        {
            TypeArguments = open.TypeArguments.Zip(instance.TypeArguments, Bind).ToArray(),
            MethodArguments = open.MethodArguments.Zip(instance.MethodArguments, Bind).ToArray(),
        };
        TypeRef Bind(TypeRef parameter, TypeRef actual) => parameter is GenericParameterRef g
            ? g with
            {
                Binding = new(FieldLayouts.IsFullyShared(actual) ? NativeBindingKind.Shared
                    : ManagedTypes.IsReferenceType(actual) ? NativeBindingKind.Reference
                    : types.Kind(actual) == TypeKind.Struct ? NativeBindingKind.Aggregate : NativeBindingKind.Scalar, actual, entry)
            } : parameter;
    }

    private static MethodRecoveryResult? Declaration(MethodRef method, ulong entry) => DelegateFacts.IsRuntimeMethod(method.Method)
        ? new(method, entry, null, []) { Declaration = RuntimeDeclarationKind.Delegate } : null;

    /// <summary>extern 方法没有 CIL 方法体，原生入口只是解析并转发的桩：结果是一条带库名与入口的声明。</summary>
    private MethodRecoveryResult? PlatformInvoke(MethodRef method, ulong entry)
    {
        if ((method.Method.Attributes & System.Reflection.MethodAttributes.PinvokeImpl) == 0) return null;
        var lifted = lifter.Lift(entry, null, null, simplify: true, promoteFrameSlots: false);
        if (!lifted.Succeeded) return new(method, entry, null, [new(entry, $"提升 {lifted.Errors[0]}")]);
        rewriter.Run(lifted.Function);
        var effects = new CallMemoryEffects(shapes.Of, abi);
        return PlatformInvokeStub.Read(lifted.Function, facts.Model.Image, effects) is { } import
            ? new(method, entry, null, []) { Declaration = RuntimeDeclarationKind.PlatformInvoke, PlatformImport = import }
            : new(method, entry, null, [new(entry, "运行时 P/Invoke 桩的描述符不能识别")]);
    }

    private MethodRecoveryResult Run(MethodRef method, ulong entry)
    {
        if (!Analyze(method, entry).TryGet(out var analysis, out var failure))
            return new(method, entry, null, [new(failure.Address, failure.Reason)]);
        return Lower(analysis) with { Rejections = Attribution(analysis.Idioms) };
    }

    /// <summary>L2 留下的归因线索：证明被拒绝的规则，以及没有归一的运行时痕迹。</summary>
    private static Cpp2CS.Diagnostics.RuleRejection[] Attribution(IdiomResult idioms) => idioms.Rejections
        .Concat(idioms.Residuals.Select(r => new Cpp2CS.Diagnostics.RuleRejection("residual", r.Address, r.Category))).ToArray();

    /// <summary>类型与下降。</summary>
    public MethodRecoveryResult Lower(MethodAnalysis analysis)
    {
        var oracle = new TypeOracle(types, facts, analysis.Method, analysis.Environment.Shape, analysis.Values, analysis.Memory);
        var uses = new TypeUseAnalysis(analysis, oracle).Run();
        if (uses.State != TypeSolveState.Stable)
            return new(analysis.Method, analysis.Entry, null, [new(analysis.Entry,
                uses.State == TypeSolveState.Cycle ? "类型 φ 类型求解循环" : "类型 φ 类型求解超过预算")]);
        var referenced = analysis.Function.Blocks.SelectMany(b => b.Statements).SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk)
            .OfType<Symbol>().Where(s => s.Kind == SymbolKind.Method).Select(s => (MethodRef)s.Value).Distinct().ToArray();
        var fields = new InlineEvidence(types, analysis.Method, Summary, referenced);
        var templates = new TemplateRecovery(types, analysis.Method, Summary, fields);
        var lowered = BodyBuilder.Build(analysis, oracle, uses, fields, templates);
        if (lowered.Body is null) return new(analysis.Method, analysis.Entry, null, lowered.Holes);
        var recovered = templates.Run(lowered.Body, lowered.Constructions, lowered.NextLocal);
        var body = LocalCoalescing.Run(recovered.Body);
        var holes = lowered.Holes.Concat(recovered.Holes).DistinctBy(h => (h.Address, h.Reason)).ToArray();
        return holes.Length == 0 ? new(analysis.Method, analysis.Entry, body, [])
            : new(analysis.Method, analysis.Entry, null, holes) { Partial = body };
    }

    /// <summary>写出定义：使用统一索引选择的原生见证；实例模板分析仍走 Summary。</summary>
    public MethodRecoveryResult RecoverDefinition(MethodDef definition)
    {
        entries ??= new MethodEntries(facts, types);
        if (entries.ForDefinition(definition) is not { } target)
            return new(MethodRef.Open(definition), 0, null, [new(0, "依赖 定义没有原生见证")]);
        return new RecoveryTarget(target.Instance, target.Address).Recover(this);
    }

    /// <summary>
    /// 另一个方法自身原生代码的恢复结果，作为内联证明的依据。入口取自方法实例索引（泛型实例可取共享实现）；
    /// 按方法、入口与原生布局绑定缓存；递归恢复中的方法返回 null。
    /// </summary>
    public MethodRecoveryResult? Summary(MethodRef method)
    {
        entries ??= new MethodEntries(facts, types);
        var entry = entries.Of(method);
        if (entry == 0) return null;
        var request = new MethodRequest(method, entry, RecoveryMode.Instance);
        if (summaries.TryGetValue(request, out var known)) return known;
        summaries[request] = null;
        var result = method.TypeArguments.Count + method.MethodArguments.Count > 0 ? RecoverInstance(method, entry) : Recover(method, entry);
        summaries[request] = result;
        return result;
    }

    private static Func<Variable> FreshTemporaries(MachineFunction function)
    {
        var next = function.Blocks.SelectMany(b => b.Statements).SelectMany(s => s switch
            { Define d => new[] { d.Target }, Phi p => [p.Target], Call c => c.Defines.OfType<Variable>(), _ => [] })
            .Concat(function.Dead.Select(d => d.Define.Target)).Where(v => v.Storage.Bank == Bank.Temp)
            .Select(v => v.Storage.Index).DefaultIfEmpty(-1).Max() + 1;
        return () => new Variable(Storage.Temp(next++), 1);
    }

    /// <summary>委托根的类型：委托常与结构体的其他字段一起放在宽寄存器里，取低位的根按值的位片定型。</summary>
    private static Func<Expr, TypeRef?> RootType(TypeOracle oracle, ValueModel values) => e => e switch
    {
        Use { Width: var width, Variable: var variable } when width < variable.Width => oracle.TypeOf(values.Syms.Slice(values.Of(variable), 0, width)),
        Use use => oracle.TypeOf(values.Of(use.Variable)),
        _ => null,
    };

    /// <summary>运行到符号值为止的各层。</summary>
    public RecoveryResult<MethodAnalysis> Analyze(MethodRef method, ulong entry)
    {
        if (abi.Machine(method, out var problem) is not { } signature)
            return RecoveryDiagnostics.Fail(entry, $"签名 {problem}", rule: "Prepare");
        var returnPieces = signature.Return is { Transfer: Transfer.Value } ret
            ? ret.Pieces.Select(p => new ReturnPiece(p.Offset, new Read(p.Register, p.Width))).ToArray() : null;
        var lifted = lifter.Lift(entry, null, returnPieces, simplify: true, promoteFrameSlots: false);
        if (!lifted.Succeeded)
            return RecoveryDiagnostics.Fail(entry, $"提升 {lifted.Errors[0]}", rule: "Prepare");
        var function = lifted.Function;
        var idioms = rewriter.Run(function);
        if (idioms.Errors.Count > 0)
            return RecoveryDiagnostics.Fail(entry, $"L2 {idioms.Errors[0]}", rule: "Prepare");
        GenericContext.Instantiate(function, method);
        CleanupCalls.Run(function, address => facts.Helpers.At(address)?.Kind == HelperKind.Unknown
            ? native.CleanupThunk(address, method.Method.Owner) : null);
        ExceptionNormalization.Run(function, ExceptionFacts.WrapperWithoutDestructor(facts.Checks));
        var environment = new MethodEnvironment(method, signature, shapes);
        var splits = PathSplitting.Run(function, f => ValueModel.Build(f, environment),
            v => new TypeOracle(types, facts, method, environment.Shape, v), lifter.Calls, lifter.Machine.Convention.StackPointer, rewriter.RecognizeSplitTypeChecks);
        InvokerCallsPass.AfterSplitting(function, method, rewriter);
        // 分派在内存提升之前解析，使经指针的调用效果有签名可依。
        var preliminary = ValueModel.Build(function, environment);
        // 路径拆分后才唯一确定的接收者。
        if (StackBoxingPass.Run(function, new CallMemoryEffects(environment.Shape, abi), environment.Shape, abi.Size, FreshTemporaries(function)))
            preliminary = ValueModel.Build(function, environment);
        DispatchResolution.Run(function, preliminary, new TypeOracle(types, facts, method, environment.Shape, preliminary));
        // 每轮从稳定输入构建分析图，只累积已证明的调用目标，不回滚生产语句和 SSA。
        var prepared = function;
        var targets = new Dictionary<CallSite, MethodRef>();
        MemoryLayout layout;
        while (true)
        {
            function = prepared.Copy(call => targets.TryGetValue(call.Site, out var target) ? call with { Resolved = target } : call);
            environment = new MethodEnvironment(method, signature, shapes);
            if (!MemoryPromotion.Run(function, signature, environment.Shape, abi, lifter.Calls, lifter.Machine.Convention.StackPointer).TryGet(out layout, out var memoryFailure))
                return memoryFailure;
            environment.Layout = layout;
            var promoted = ValueModel.Build(function, environment);
            var promotedOracle = new TypeOracle(types, facts, method, environment.Shape, promoted, layout);
            var discovered = DispatchResolution.Find(function, promoted, promotedOracle).ToDictionary();
            foreach (var (site, invoke) in DelegateCallNormalizer.Discover(facts, function, RootType(promotedOracle, promoted)))
                discovered.TryAdd(site, invoke);
            if (discovered.Count == 0) break;
            foreach (var (site, target) in discovered) targets.Add(site, target);
        }
        // 活动异常栈的长度字段提升之后才是 SSA 值：栈顶可以按路径求出，读完之后 push 不再被观察。
        // 读取换掉之后，下标地址的定义要清理掉，下一轮才能确认 push 没人读。
        for (var round = 0; round < 3 && (ExceptionStackValues.TopValues(function, new CallMemoryEffects(environment.Shape, abi, settled: true), FreshTemporaries(function)) | ExceptionStackValues.Run(function)); round++)
        {
            var errors = Cpp2CS.Machine.Ssa.Lowering.Cleanup(function);
            if (errors.Count > 0) return RecoveryDiagnostics.Fail(entry, $"L2 {errors[0]}", rule: "ExceptionStack");
        }
        // 帧提升消去异常值的栈副本后，落地跳板可能才成为纯传值链。
        if (StackGuardNormalizer.Run(function))
        {
            var errors = Cpp2CS.Machine.Ssa.Lowering.Cleanup(function);
            if (errors.Count > 0) return RecoveryDiagnostics.Fail(entry, $"L2 {errors[0]}", rule: "StackGuard");
        }
        ExceptionNormalization.Run(function, ExceptionFacts.WrapperWithoutDestructor(facts.Checks));
        environment.Layout = layout;
        var values = ValueModel.Build(function, environment);
        var oracle = new TypeOracle(types, facts, method, environment.Shape, values, layout);
        if (DelegateCallNormalizer.Run(facts, function, idioms, RootType(oracle, values)))
            values = ValueModel.Build(function, environment);
        return new MethodAnalysis(method, entry, signature, function, idioms, layout, values) { Environment = environment, Splits = splits };
    }
}
