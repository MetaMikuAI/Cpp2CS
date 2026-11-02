using Cpp2CS.Facts;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Lifting;
using Cpp2CS.Recovery.Calls;
using Cpp2CS.Recovery.Control;
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
    private readonly Dictionary<(MethodRef, ulong), MethodRecoveryResult?> summaries = [];
    private MethodEntries? entries;

    public MethodDecompiler(ProgramFacts facts, ManagedTypes types)
    {
        this.facts = facts;
        this.types = types;
        lifter = new FunctionLifter(facts);
        rewriter = new IdiomRewriter(facts) { RecordFilter = _ => false, RecoverUnusedInputs = true };
        abi = new ManagedAbi(facts.Layouts);
        shapes = new CallShapes(facts, abi, rewriter.UnusedInput);
    }

    public ManagedTypes Types => types;
    public ProgramFacts Facts => facts;
    public CallShapes Shapes => shapes;

    public MethodRecoveryResult Recover(MethodRef method, ulong entry) => Declaration(method, entry) ?? Run(method, entry);

    /// <summary>恢复泛型类型或泛型方法的封闭实例，方法体以封闭类型表达。</summary>
    public MethodRecoveryResult RecoverInstance(MethodRef method, ulong entry) => Declaration(method, entry) ?? Run(method, entry);

    /// <summary>从已知原生实例恢复开放泛型体：类型参数带上实例的原生绑定，输出保留类型参数。</summary>
    public MethodRecoveryResult RecoverShared(MethodRef instance, ulong entry)
    {
        var open = MethodRef.Open(instance.Method);
        if (Declaration(open, entry) is { } declaration) return declaration;
        open = open with
        {
            TypeArguments = open.TypeArguments.Zip(instance.TypeArguments, Bind).ToArray(),
            MethodArguments = open.MethodArguments.Zip(instance.MethodArguments, Bind).ToArray(),
        };
        return Run(open, entry);
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

    private MethodRecoveryResult Run(MethodRef method, ulong entry)
    {
        if (!Analyze(method, entry).TryGet(out var analysis, out var failure))
            return new(method, entry, null, [new(failure.Address, failure.Reason)]);
        return Lower(analysis);
    }

    /// <summary>类型与下降。</summary>
    public MethodRecoveryResult Lower(MethodAnalysis analysis)
    {
        var oracle = new TypeOracle(types, facts, analysis.Method, analysis.Environment.Shape, analysis.Values, analysis.Memory);
        return BodyBuilder.Build(analysis, oracle, Summary);
    }

    /// <summary>写出所需的依赖方法：按方法实例的原生入口恢复；泛型实例恢复为开放的共享体。</summary>
    public MethodRecoveryResult RecoverDependency(MethodRef method)
    {
        entries ??= new MethodEntries(facts, types);
        var entry = entries.Of(method);
        if (entry == 0) return new(MethodRef.Open(method.Method), 0, null, [new(0, "依赖 没有原生入口")]);
        return method.TypeArguments.Count + method.MethodArguments.Count > 0 ? RecoverShared(method, entry) : Recover(method, entry);
    }

    /// <summary>
    /// 另一个方法自身原生代码的恢复结果，作为内联证明的依据。入口取自方法实例索引（泛型实例可取共享实现）；
    /// 按方法与入口缓存；递归恢复中的方法返回 null。
    /// </summary>
    public MethodRecoveryResult? Summary(MethodRef method)
    {
        entries ??= new MethodEntries(facts, types);
        var entry = entries.Of(method);
        if (entry == 0) return null;
        if (summaries.TryGetValue((method, entry), out var known)) return known;
        summaries[(method, entry)] = null;
        var result = method.TypeArguments.Count + method.MethodArguments.Count > 0 ? RecoverInstance(method, entry) : Recover(method, entry);
        summaries[(method, entry)] = result;
        return result;
    }

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
        ExceptionNormalization.Run(function, ExceptionFacts.WrapperWithoutDestructor(facts.Checks));
        var environment = new MethodEnvironment(method, signature, shapes);
        var splits = PathSplitting.Run(function, f => ValueModel.Build(f, environment), lifter.Calls, lifter.Machine.Convention.StackPointer);
        // 分派在内存提升之前解析，使经指针的调用效果有签名可依。
        var preliminary = ValueModel.Build(function, environment);
        if (StackBoxing.Run(function, preliminary, new TypeOracle(types, facts, method, environment.Shape, preliminary)) > 0)
            preliminary = ValueModel.Build(function, environment);
        DispatchResolution.Run(function, preliminary, new TypeOracle(types, facts, method, environment.Shape, preliminary));
        if (!MemoryPromotion.Run(function, signature, environment.Shape, abi, lifter.Calls, lifter.Machine.Convention.StackPointer).TryGet(out var layout, out var memoryFailure))
            return memoryFailure;
        // 帧提升消去异常值的栈副本后，落地跳板可能才成为纯传值链。
        ExceptionNormalization.Run(function, ExceptionFacts.WrapperWithoutDestructor(facts.Checks));
        environment.Layout = layout;
        var values = ValueModel.Build(function, environment);
        return new MethodAnalysis(method, entry, signature, function, idioms, layout, values) { Environment = environment, Splits = splits };
    }
}
