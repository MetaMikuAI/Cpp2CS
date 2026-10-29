using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;
using Cpp2CS.Lifting;
using Cpp2CS.Model;
using Cpp2CS.Recovery.Analysis;
using Cpp2CS.Calls;
using Convert = Cpp2CS.Ir.Convert;

namespace Cpp2CS.Recovery;

/// <summary>
/// L3 最小版本：把 L2 归一之后的寄存器 SSA 翻译成带类型的托管方法体（<see cref="ManagedBody"/>）。
/// 只处理能逐条说明语义的形态；其余之处记为洞（<see cref="RecoveryHole"/>），有洞的方法不输出方法体。
/// 规则：
/// 1. 参数与返回值按 <see cref="ManagedAbi"/> 对应到寄存器；提升时把返回值寄存器作为返回语句的读取，避免返回值的计算被当作死定义删去。
/// 2. 每个 SSA 定义成为一个局部变量（ILSpy 再内联）；局部变量的位宽等于定义值的位宽，寄存器中更高的位为 0（W 写入清零高位）。
/// 3. 访存按运行时布局解释为字段、静态字段、数组长度或元素；解释不了即为洞。
/// 4. 判空在同一直线路径上被随后对同一对象的字段访问或实例调用（改用 callvirt）吸收；越界被随后对同一数组同一下标的元素访问吸收；
///    之间只允许无副作用的定义与其他判空（它们抛出同一种异常）。没被吸收的检查显式输出为 if (条件) throw new 异常()。
/// 5. 写屏障只通知 GC、不写入（Il2CppCodeGenWriteBarrier），直接删去；InitClass（类元数据初始化）没有托管可见的效果，删去。
/// 6. 被调用者保存寄存器在序言中存入栈帧、尾声读回（读回已作为死定义删去）：只被这样使用的栈槽删去。
/// 7. 显式的类构造（RunClassConstructor&lt;T&gt;）之后，直线路径上第一个有副作用的操作是访问 T 的静态字段、调用 T 的构造函数或静态方法时，删去显式调用。
///    依据 ECMA-335 II.10.5.3：T 没有 beforefieldinit 时，这些操作本身就在该处触发类型初始化；T 有 beforefieldinit 时，
///    初始化只保证在首次访问静态字段之前（"at, or sometime before"）完成，IL2CPP 的提前运行与 CLR 的延后运行是同一程序的两种合规执行。
/// 8. 不含访存、只在同一块内被（非 φ）使用一次的定义内联到使用处：SSA 值不可变、块内没有对 φ 局部变量的重新赋值，内联不改变结果。
///    例如构造函数里被编译器提到基类构造调用之前的参数运算（C# 中 base(...) 之前不能有语句）。
/// 实例不是线程安全的。
/// </summary>
public sealed partial class MethodRecovery
{
    private static readonly HashSet<Storage> CalleeSaved =
        [.. Enumerable.Range(19, 12).Select(Storage.Gpr), .. Enumerable.Range(8, 8).Select(Storage.Vec)];

    private readonly ProgramFacts facts;
    private readonly ManagedTypes types;
    private readonly FunctionLifter lifter;
    private readonly IdiomRewriter rewriter;
    private readonly ManagedAbi abi;
    private readonly MethodRef? runClassConstructor;
    private readonly MethodRef? memoryBarrier;
    private readonly Dictionary<string, MethodRef?> exceptionConstructors = new();

    public MethodRecovery(ProgramFacts facts, ManagedTypes types)
    {
        this.facts = facts;
        this.types = types;
        lifter = new FunctionLifter(facts);
        rewriter = new IdiomRewriter(facts) { RecordFilter = _ => false, RecoverUnusedInputs = true };
        abi = new ManagedAbi(facts.Layouts);
        runClassConstructor = types.CorlibMethod("System.Runtime.CompilerServices.RuntimeHelpers", "RunClassConstructor", types.RuntimeTypeHandle);
        memoryBarrier = types.CorlibMethod("System.Threading.Thread", "MemoryBarrier");
    }

    public ManagedTypes Types => types;

    private readonly Dictionary<(DefinitionRef, ulong), MethodDef?> forwarding = new();

    /// <summary>
    /// type 自己的无参构造函数是否只把 this 转给 target（基类的构造函数）：原生代码中只有这一个调用（尾调用或调用后返回），
    /// 首个实参是入口的 x0，没有分支、没有其他调用、没有栈帧之外的写入。clang 把这样的构造函数内联后，调用者分配对象后直接调用基类构造。
    /// </summary>
    private MethodDef? ForwardingConstructor(DefinitionRef type, ulong target)
    {
        if (forwarding.TryGetValue((type, target), out var known)) return known;
        MethodDef? result = null;
        if (type.Definition.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic && m.Parameters.Count == 0).ToArray() is [var constructor]
            && ConstructorEntry(new(constructor, type.Arguments, [])) is > 0 and var entry
            && facts.Code.RegionOf(entry) == CodeRegion.Managed && lifter.Lift(entry) is { Succeeded: true } lifted)
        {
            var statements = lifted.Function.Blocks.SelectMany(b => b.Statements).ToArray();
            var calls = statements.OfType<Call>().ToArray();
            static bool OnFrame(Expr address) => address is FrameAddress || address is Binary { Op: BinOp.Add, Left: FrameAddress, Right: Const };
            if (calls is [{ Target: Const called, Kind: CallKind.Tail or CallKind.Direct } call] && called.Value == target
                && call.Arguments.FirstOrDefault() is Use { Variable: { Version: 0 } self } && self.Storage == Storage.Gpr(0)
                && statements.All(s => s is Define or Phi or Nop or Jump or Return or Call || s is Store store && OnFrame(store.Target)))
                result = constructor;
        }
        return forwarding[(type, target)] = result;
    }

    private MethodRecoveryResult? RuntimeDeclaration(MethodRef method, ulong entry) => DelegateFacts.IsRuntimeMethod(method.Method)
        ? new(method, entry, null, []) { Declaration = RuntimeDeclarationKind.Delegate } : PlatformDeclaration(method, entry);

    public MethodRecoveryResult Recover(MethodRef method, ulong entry) => RuntimeDeclaration(method, entry) ?? new Context(this, method, entry).Run();

    /// <summary>
    /// 恢复泛型类型或泛型方法的封闭实例，用于认出访问器等形态；
    /// 方法体以封闭类型表达，不写成泛型定义的 CIL。
    /// </summary>
    public MethodRecoveryResult RecoverInstance(MethodRef method, ulong entry) => RuntimeDeclaration(method, entry) ?? new Context(this, method, entry) { ClosedInstance = true }.Run();

    /// <summary>从已知原生实例恢复开放泛型体；标量实例只提供传参布局，输出保留类型参数。</summary>
    public MethodRecoveryResult RecoverShared(MethodRef instance, ulong entry)
    {
        var open = MethodRef.Open(instance.Method);
        if (RuntimeDeclaration(open, entry) is { } declaration) return declaration;
        if (instance.TypeArguments.Count != open.TypeArguments.Count || instance.MethodArguments.Count != open.MethodArguments.Count
            || instance.TypeArguments.Concat(instance.MethodArguments).Any(t => !ManagedTypes.IsReferenceType(t)
                && types.Kind(t) is not (TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double)
                && !(types.Kind(t) == TypeKind.Struct && types.Size(t) > 0) && !FieldLayouts.IsFullyShared(t)))
            return new(open, entry, null, [new(entry, "泛型 实例缺少可用的共享或标量布局")]);
        open = open with
        {
            TypeArguments = open.TypeArguments.Zip(instance.TypeArguments, Bind).ToArray(),
            MethodArguments = open.MethodArguments.Zip(instance.MethodArguments, Bind).ToArray(),
        };
        return new Context(this, open, entry) { SharedDefinition = true }.Run();
        TypeRef Bind(TypeRef parameter, TypeRef instance) => parameter is GenericParameterRef g
            ? g with { Binding = new(FieldLayouts.IsFullyShared(instance) ? NativeBindingKind.Shared
                : ManagedTypes.IsReferenceType(instance) ? NativeBindingKind.Reference
                : types.Kind(instance) == TypeKind.Struct ? NativeBindingKind.Aggregate : NativeBindingKind.Scalar, instance, entry) } : parameter;
    }

    /// <summary>异常类型的无参实例构造函数（全名，含 mscorlib 之外的类型）。</summary>
    private MethodRef? ExceptionConstructor(string fullName)
    {
        if (exceptionConstructors.TryGetValue(fullName, out var known)) return known;
        var type = types.CorlibDefinition(fullName) ?? facts.Model.Types.FirstOrDefault(t => t.FullName == fullName && t.GenericParameters.Count == 0);
        var constructor = type?.Methods.FirstOrDefault(m => m.Name == ".ctor" && !m.IsStatic && m.Parameters.Count == 0);
        return exceptionConstructors[fullName] = constructor is null ? null : new MethodRef(constructor, [], []);
    }

    private sealed record Argument(int Index, TypeRef Type, int Width);

    private sealed partial class Context(MethodRecovery owner, MethodRef method, ulong entry)
    {
        private readonly ManagedTypes types = owner.types;
        private readonly ProgramFacts facts = owner.facts;
        private HoleLedger? ledgerStore;
        /// <summary>洞账本（<see cref="HoleLedger"/>）：独立洞、毒化、依赖边与已诊断的语句。</summary>
        private HoleLedger ledger => ledgerStore ??= new(DefinedBy);
        private readonly Dictionary<Storage, Argument> arguments = new();
        /// <summary>定义索引（<see cref="Definitions"/>）；帧改写之后重建。</summary>
        private Definitions definitions = Definitions.Empty;
        private readonly MethodAnalyses analyses = new();
        private readonly List<AnalysisStep> analysisSteps = [];
        private readonly List<RuleTrace> ruleTraces = [];
        private IReadOnlyDictionary<Variable, Expr> values => definitions.Values;
        private IReadOnlyDictionary<Variable, Phi> phis => definitions.Phis;
        private IReadOnlyDictionary<Variable, (Call Call, int Index)> results => definitions.Results;
        private IReadOnlyDictionary<Variable, IReadOnlyList<Phi>> phiUses => definitions.PhiUses;
        private readonly Dictionary<Variable, TypeRef> known = new();
        private readonly HashSet<Variable> runtime = [];
        private readonly Dictionary<Variable, Use> objectClasses = new();
        private readonly Dictionary<Call, Use> typeChecks = new(ReferenceEqualityComparer.Instance);
        private readonly HashSet<Stmt> dropped = new(ReferenceEqualityComparer.Instance);
        private readonly HashSet<Call> virtualCalls = new(ReferenceEqualityComparer.Instance);
        /// <summary>对象分配 → 与之合并的构造调用；构造调用 → 分配结果变量。</summary>
        private readonly Dictionary<Call, Variable> constructed = new(ReferenceEqualityComparer.Instance);
        /// <summary>与分配合并的基类构造调用 → 类型自己（只转调基类构造）的无参构造函数。</summary>
        private readonly Dictionary<Call, MethodRef> forwardedConstructors = new(ReferenceEqualityComparer.Instance);
        /// <summary>装箱调用 → 写入被装箱栈槽的值。</summary>
        private readonly Dictionary<Call, Expr> boxed = new(ReferenceEqualityComparer.Instance);
        private readonly CallBindingState callBindings = new();
        /// <summary>内联到使用处的定义（见类注释第 8 条）。</summary>
        private readonly HashSet<Variable> inlined = [];
        private readonly Dictionary<long, RecoveryHole> frameHoles = new();
        private IReadOnlyList<Block> blocks = null!;
        private RecoveryHole? returnHole;
        private MachineFunction function = null!;
        private TypeRef returnType = null!;

        private RecoveryHole Hole(ulong address, string reason, bool derived = false, [System.Runtime.CompilerServices.CallerMemberName] string rule = "unknown")
            => ledger.Add(address, reason, derived, "recovery." + rule);
        private static RecoveryFailure Fail(ulong address, string reason, [System.Runtime.CompilerServices.CallerMemberName] string rule = "unknown")
            => new(address, reason, Code: "recovery." + rule);

        private static RecoveryFailure Derived(RecoveryHole cause, string reason) => new(0, HoleLedger.DerivedReason(cause, reason), true, cause);

        private RecoveryFailure? CheckPoison(Variable variable) => ledger.TryGetPoison(variable, out var cause)
            ? Derived(cause, $"变量 {variable} 依赖未恢复的值") : null;

        private void Poison(Variable variable, RecoveryHole cause) => ledger.Poison(variable, cause);
        private void Poison(Stmt statement, RecoveryHole cause) => ledger.Poison(statement, cause);

        private IEnumerable<Variable> DefinedBy(Stmt statement)
        {
            if (statement is Define define) yield return define.Target;
            if (statement is Call call)
            {
                foreach (var result in call.Defines) if (result is not null) yield return result;
                if (constructed.TryGetValue(call, out var created)) yield return created;
            }
        }

        private RecoveryHole Record(RecoveryFailure exception, ulong address, Stmt? statement = null)
        {
            var hole = ledger.Add(exception.Address == 0 ? address : exception.Address, exception.Message, exception.Derived, exception.Code);
            if (exception.Cause is { } source) ledger.Link(hole, source);
            if (exception.Unresolved is { } variable) ledger.Unresolved(variable, statement);
            // 未定型的定义可能来自尚未遍历到的调用/回边；等全部语句诊断完再决定根因。
            if (statement is not null && (exception.Unresolved is null || statement is Call))
                Poison(statement, exception.Cause ?? hole);
            return exception.Cause ?? hole;
        }

        /// <summary>值中有 L3 内部的值（结构体片等，ManagedValues 不认识的类型）。</summary>
        private static bool FragmentInside(ManagedValue value)
        {
            if (value is Fragment or AggregatePiece) return true;
            return ManagedValues.Children(value).Any(FragmentInside);
        }

        public MethodRecoveryResult Run()
        {
            ManagedBody? partial = null;
            if (Prepare())
            {
                if (Analyze() is { } analysisFailure) Record(analysisFailure, entry);
                else if (!Build().TryGet(out var built, out var buildFailure)) Record(buildFailure, entry);
                else
                {
                    var body = DropUnusedRegisterCopies(RewriteAwaiters(built));
                    bool Leftover(ManagedStatement s) => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)).Any(FragmentInside);
                    partial = body with { Blocks = body.Blocks.Select(b => b with { Statements = b.Statements.Select(s => Leftover(s)
                        ? new ManagedHole(s.Address, "结构体 片未拆回叶子", s is ManagedJump or ManagedBranch or ManagedSwitch or ManagedReturn or ManagedCall { Tail: true }) : s).ToArray() }).ToArray() };
                    if (body.Blocks.SelectMany(b => b.Statements).FirstOrDefault(Leftover) is { } leftover)
                        Record(Fail(leftover.Address, "结构体 片未拆回叶子"), entry);
                    else foreach (var proof in Registry.Proofs) proof(this, body);
                    if (ledger.Count == 0) return new(method, entry, owner.RestoreBaseConstructor(body), ledger.Holes)
                        { Analyses = analysisSteps.ToArray(), Calls = callBindings.Resolutions.ToArray(), Rules = ruleTraces.ToArray() };
                    ledger.Finish();
                }
            }
            return new(method, entry, null, ledger.Holes) { Partial = partial is null ? null : Summarized(partial, ledger.Holes),
                Analyses = analysisSteps.ToArray(), Calls = callBindings.Resolutions.ToArray(), Rules = ruleTraces.ToArray() };
        }

        /// <summary>没有落在某条语句上的洞（异常区域、签名等方法级的洞）汇总成方法入口处的一条标记。</summary>
        private static ManagedBody Summarized(ManagedBody partial, IReadOnlyList<RecoveryHole> holes)
        {
            var marked = partial.Blocks.SelectMany(b => b.Statements).OfType<ManagedHole>().Select(h => h.Reason).ToHashSet();
            var unmarked = holes.Where(h => !h.Derived && !marked.Contains(h.Reason)).Select(h => $"0x{h.Address:x} {h.Reason}").Distinct().ToArray();
            if (unmarked.Length == 0 || partial.Blocks.Count == 0) return partial;
            var first = partial.Blocks[0];
            var summary = new ManagedHole(0, "未恢复：" + string.Join("；", unmarked.Take(4)) + (unmarked.Length > 4 ? $"；等 {unmarked.Length} 处" : ""), false);
            return partial with { Blocks = partial.Blocks.Skip(1).Prepend(first with { Statements = first.Statements.Prepend(summary).ToArray() }).ToArray() };
        }

        // ---------- 准备：签名、提升、L2 ----------

        /// <summary>允许具体实参或已有引用布局见证的泛型实例（RecoverInstance）。</summary>
        public bool ClosedInstance { get; init; }
        public bool SharedDefinition { get; init; }

        private bool Prepare()
        {
            var definition = method.Method;
            // 依赖访问器可以沿用调用者的引用布局见证，保留其 T 身份；没有见证的开放参数仍拒绝。
            var closed = ClosedInstance && method.MethodArguments.Count == definition.GenericParameters.Count
                && method.TypeArguments.Count == definition.Owner.GenericParameters.Count && method.TypeArguments.Concat(method.MethodArguments).All(a =>
                    a is DefinitionRef or ArrayRef or GenericParameterRef { Binding: { Kind: NativeBindingKind.Reference, Entry: > 0 } });
            if (!closed && !SharedDefinition && (definition.GenericParameters.Count > 0 || definition.Owner.GenericParameters.Count > 0 || method.TypeArguments.Count > 0))
            {
                Hole(entry, "泛型 方法或类型带泛型参数");
                return false;
            }
            if (owner.abi.Classify(method, out var problem) is not { } signature)
            {
                Hole(entry, $"签名 {problem}");
                return false;
            }
            if (signature.This is { } self) arguments[self.Pieces[0].Register] = new(-1, self.Type, 64);
            var incomingStack = owner.abi.StackArguments(signature);
            for (var i = 0; i < signature.Parameters.Length; i++)
            {
                var parameter = signature.Parameters[i];
                if (Registry.Parameters.Any(rule => rule(this, parameter, i))) continue;
                if (incomingStack.Parameters.FirstOrDefault(p => p.Index == i) is { Indirect: false } stackParameter
                    && (types.Kind(parameter.Type) is TypeKind.Int or TypeKind.Bool or TypeKind.Reference or TypeKind.Float or TypeKind.Double
                        || ManagedTypes.IsNativePointer(parameter.Type)))
                {
                    arguments[Storage.Slot(stackParameter.Offset)] = new(i, parameter.Type, stackParameter.Size * 8);
                    continue;
                }
                if (parameter.Passing != Passing.Registers || parameter.Pieces.Length != 1 || types.Kind(parameter.Type) is TypeKind.Struct or null
                    || types.Kind(parameter.Type) == TypeKind.Pointer && !ManagedTypes.IsNativePointer(parameter.Type) && (parameter.Type is not ByRefRef parameterReference
                        || types.Kind(parameterReference.Element) is not (TypeKind.Struct or TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Reference)))
                {
                    var hole = Hole(entry, $"参数 {definition.Parameters[i].Name} 的类型 {parameter.Type} 尚未支持");
                    foreach (var piece in parameter.Pieces) Poison(new Variable(piece.Register, 0), hole);
                    continue;
                }
                arguments[parameter.Pieces[0].Register] = new(i, parameter.Type, parameter.Pieces[0].Width);
            }
            returnType = definition.ReturnType.Substitute(method.TypeArguments, method.MethodArguments);
            PrepareReturnBuffer(signature.Return);
            Expr? returnValue = null;
            if (signature.Return is { } ret)
            {
                if (!RegisterStruct(ret) && !IndirectStruct(ret) && (ret.Passing != Passing.Registers || ret.Pieces.Length != 1 || types.Kind(ret.Type) is TypeKind.Struct or null
                    || types.Kind(ret.Type) == TypeKind.Pointer && !ManagedTypes.IsNativePointer(ret.Type)))
                {
                    returnHole = Hole(entry, $"返回值 类型 {ret.Type} 尚未支持");
                }
                // 寄存器聚合返回保留全部片；间接返回只写入口缓冲区，返回时的 x8 内容不属于结果。
                if (!IndirectStruct(ret))
                    returnValue = ret.Pieces.Length == 1 ? new Read(ret.Pieces[0].Register, ret.Pieces[0].Width)
                        : new Intrinsic("diagnostic_return", ret.Pieces.Select(p => (Expr)new Read(p.Register, p.Width)).ToArray(), 64);
            }
            var lifted = owner.lifter.Lift(entry, returnValue);
            if (!lifted.Succeeded)
            {
                Hole(entry, $"提升 {lifted.Errors[0]}");
                return false;
            }
            function = lifted.Function;
            var idioms = owner.rewriter.Run(function);
            if (SharedDefinition) BindSharedReferences();
            if (method.TypeArguments.Concat(method.MethodArguments).Any(t => t is GenericParameterRef { NativeAggregate: not null }))
                PromotePrivateFrameSlots();
            NormalizeSharedFields();
            NormalizeSharedValues();
            StackCanaryRecognition.Run(function, extent: new ManagedCallFrames(facts, owner.abi).ArgumentSize);
            NormalizeDelegateChoices();
            foreach (var error in idioms.Errors) Hole(entry, $"L2 {error}");
            if (idioms.Errors.Count > 0) return false;
            NormalizeScalarVectors();
            VectorPhiProjection.Run(function.Blocks);
            CallArgumentProjection.Run(function.Blocks, StructArgumentWidths);
            TrimIndirectArguments();
            Ssa.Propagate.RemoveDead(function);
            // 库内存操作归一后也可能产生新栈读写；普通方法与异常方法采用同一有界提升规则。
            FrameWritebacks.Run(function);
            var constantFrameIndices = FrameConstantIndices.Run(function) > 0;
            ManagedFramePromotion.Run(facts, function, owner.abi, owner.lifter.Calls, owner.lifter.Machine.Convention.StackPointer);
            if (constantFrameIndices)
            {
                Ssa.Propagate.Run(function, Ssa.Dominators.Compute(function));
                PromotePrivateFrameSlots();
            }
            NormalizeCleanupThunks();
            NormalizeOutlinedCalls(idioms);
            // 清理 thunk 拆开后，栈上的 this 可回代为参数；用同一套委托证明消费新出现的类型证据。
            if (DelegateCallNormalizer.Run(facts, function, idioms))
            {
                function.Problems.AddRange(Ssa.Lowering.Cleanup(function));
                var delegates = function.Blocks.SelectMany(b => b.Statements).OfType<Call>()
                    .Where(c => c is { Op.Kind: OpKind.CallDelegate, Target: Symbol { Kind: SymbolKind.Method }, DelegateReceiver: not null })
                    .Select(c => c.Address).ToHashSet();
                idioms.Residuals.RemoveAll(r => r.Category.StartsWith("indirect:", StringComparison.Ordinal) && delegates.Contains(r.Address));
            }
            if (function.Blocks.Any(b => b.IsLandingPad))
                while (ExceptionNullBranches.Run(facts, function)) function.Problems.AddRange(Ssa.Lowering.Cleanup(function));
            foreach (var residual in idioms.Residuals)
                // 没有身份证据的未注册调用交给 L3 的调用解析（方法的本地副本，CopyOf）；解析不了时在调用处留洞。
                if (residual.Category is not ("helper:WriteBarrier" or "call:unregistered-managed") && !cleanupSites.Contains(residual.Address) && !sharedSites.Contains(residual.Address))
                {
                    var hole = Hole(residual.Address, $"残余 {residual.Category}");
                    foreach (var statement in function.Blocks.SelectMany(b => b.Statements).Where(s => s.Address == residual.Address))
                        ledger.Block(statement, hole);
                }
            blocks = function.Blocks;
            if (function.Blocks.FirstOrDefault(b => b.IsLandingPad) is { } landing && !PrepareExceptionRegions())
            {
                var hole = Hole(landing.Start, $"异常区域 {exceptionLayout?.Reason ?? "尚未恢复"} {exceptionLayout?.Detail}");
                // Handler 是受保护块的异常后继，不能把受保护块本身排除。只保留入口的正常边闭包。
                var normal = new HashSet<Block>();
                var pending = new Stack<Block>();
                pending.Push(function.EntryBlock);
                while (pending.TryPop(out var block))
                    if (!block.IsLandingPad && normal.Add(block))
                        foreach (var successor in block.NormalSuccessors) pending.Push(successor);
                blocks = function.Blocks.Where(normal.Contains).ToArray();
                foreach (var statement in function.Blocks.Where(b => !normal.Contains(b)).SelectMany(b => b.Statements))
                {
                    Poison(statement, hole);
                    if (statement is Phi phi) Poison(phi.Target, hole);
                }
            }
            foreach (var problem2 in function.Problems) Hole(entry, $"控制流 {problem2}");
            return true;
        }

        // ---------- 分析：定义、运行时引用、配对、类型 ----------

        private RecoveryFailure? Analyze()
        {
            definitions = IndexDefinitions();
            // 依赖边取改写前的数据流：帧改写把别名换成 TypedFrame，但值仍然来自原来的来源。
            foreach (var (source, target) in definitions.DataFlow) ledger.Dependency(source, target);
            ledger.PropagateExisting();
            foreach (var (name, run) in Registry.Analyses)
            {
                var version = analyses.Version;
                var inputTypes = known.Count;
                var started = System.Diagnostics.Stopwatch.GetTimestamp();
                var failure = run(this);
                if (analyses.Refresh(blocks, exceptionPhis)) definitions = analyses.Get(Definitions.Analysis);
                analysisSteps.Add(new(name, version, analyses.Version, inputTypes, known.Count,
                    System.Diagnostics.Stopwatch.GetElapsedTime(started).TotalMilliseconds));
                if (failure is not null) return failure;
            }
            return null;
        }

        /// <summary>类型推断；认出新的类型检查后（klass 加载成为运行时引用），标记运行时值再推断一次。</summary>
        [Analysis("类型", 90, After = ["运行时引用", "内联", "帧槽", "分配", "检查吸收"])]
        private void Typing()
        {
            InferTypes();
            if (PrepareTypeChecks())
            {
                MarkRuntime();
                InferTypes();
            }
            PrepareUnusedReceiverPhis();
            TrimIndirectArguments(typed: true);
            NarrowTypedScalars();
        }

        /// <summary>
        /// 只接受 L2 已证明的继承检查，且 klass 必须由已知托管引用的零偏移 64 位加载得到。
        /// 原加载位置保留判空；类指针不作为托管局部变量，也不把值类型 this 的首字段误认成 klass。
        /// </summary>
        private bool PrepareTypeChecks()
        {
            PrepareExceptionTypeChecks();
            foreach (var call in blocks.SelectMany(b => b.Statements).OfType<Call>())
                if (call is { Op: { Kind: OpKind.TypeCheck, Operand: DefinitionRef { Definition: { IsValueType: false, IsInterface: false } } }, Arguments: [Use klass] }
                    && values.TryGetValue(klass.Variable, out var value) && value is Load { Width: 64, Address: Use obj }
                    && TypeOfValue(obj) is { } type && ManagedTypes.IsReferenceType(type))
                {
                    objectClasses[klass.Variable] = obj;
                    typeChecks[call] = obj;
                    runtime.Add(klass.Variable);
                    callBindings.InvalidateTypes();
                }
            return PrepareSealedChecks() | typeChecks.Count > 0;
        }

        /// <summary>
        /// sealed 引用类型的 isinst 快速路径：IL2CPP 直接比较对象的类指针与 Class&lt;T&gt;（如 <c>klass == Texture2D ? obj : null</c>）。
        /// T 没有子类，类指针相等即 obj is T（ECMA-335 III.4.6）。类指针的读取只被这种比较使用时，读取处保留判空（同 TypeCheck），比较写成 isinst。
        /// </summary>
        private bool PrepareSealedChecks()
        {
            var found = false;
            var compares = blocks.SelectMany(b => b.Statements).SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).OfType<Compare>().ToArray();
            var uses = blocks.SelectMany(b => b.Statements).SelectMany(s => s is Phi phi ? phi.Sources.Select(v => new Use(v, v.Width)) : ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>())
                .GroupBy(u => u.Variable).ToDictionary(g => g.Key, g => g.Count());
            foreach (var (variable, value) in values)
            {
                if (runtime.Contains(variable) || value is not Load { Width: 64, Address: Use obj } || TypeOfValue(obj) is not { } type || !ManagedTypes.IsReferenceType(type)) continue;
                var sealedCompares = compares.Count(c => c.Cond is Cond.Eq or Cond.Ne && SealedOperands(c) is var (klass, _) && klass == variable);
                if (sealedCompares == 0 || uses.GetValueOrDefault(variable) != sealedCompares) continue;
                objectClasses[variable] = obj;
                runtime.Add(variable);
                callBindings.InvalidateTypes();
                found = true;
            }
            return found;
        }

        /// <summary>比较的两侧是（类指针变量, sealed 引用类型的 Class 符号）时返回二者。</summary>
        private static (Variable Klass, DefinitionRef Type)? SealedOperands(Compare c)
        {
            static bool Sealed(Expr e, out DefinitionRef type)
            {
                type = null!;
                if (e is not Symbol { Kind: SymbolKind.Class, Value: DefinitionRef d } || d.Definition.IsInterface || d.Definition.IsValueType
                    || (d.Definition.Attributes & System.Reflection.TypeAttributes.Sealed) == 0) return false;
                type = d;
                return true;
            }
            if (c.Left is Use { Width: 64 } l && Sealed(c.Right, out var right)) return (l.Variable, right);
            if (c.Right is Use { Width: 64 } r && Sealed(c.Left, out var left)) return (r.Variable, left);
            return null;
        }

        private Definitions IndexDefinitions()
        {
            analyses.Refresh(blocks, exceptionPhis);
            return analyses.Get(Definitions.Analysis);
        }

        /// <summary>运行时引用：值是类、方法等运行时结构（不是托管值）的变量。只能出现在运行时操作的参数中。</summary>
        [Analysis("运行时引用", 40, After = ["帧区域", "异常值"])]
        private void MarkRuntime()
        {
            MarkVtableLoads();
            MarkGenericVirtualLoads();
            MarkVirtualDelegateLoads();
            bool changed;
            do
            {
                changed = false;
                foreach (var (variable, value) in values)
                    if (!runtime.Contains(variable) && (value is Symbol { Kind: not SymbolKind.String } or FrameAddress or TypedFrame || FrameAccess(value) is not null || value is Use u && runtime.Contains(u.Variable) || IsInterfaceMetadataLoad(value)))
                        changed |= runtime.Add(variable);
                foreach (var (variable, (call, _)) in results)
                    if (!runtime.Contains(variable) && call.Op?.Kind is OpKind.InitClass or OpKind.InitMethodRgctx or OpKind.InterfaceInvokeData or OpKind.ResolveGenericVirtual)
                        changed |= runtime.Add(variable);
                foreach (var (variable, phi) in phis)
                    if (!runtime.Contains(variable) && phi.Sources.Any(runtime.Contains))
                        changed |= runtime.Add(variable);
            } while (changed);
            callBindings.InvalidateTypes();
        }

        /// <summary>
        /// 虚表分派（CallVirtual）的类指针与虚表项：目标是 klass->vtable[n].methodPtr，klass = *接收者，klass->vtable[n].method 作为 MethodInfo 实参。
        /// 类指针只用于这些虚表项的读取（以及尾调用保守读取的 x8 等调用实参）时是运行时值，虚表项也是；callvirt 自身对接收者判空。
        /// </summary>
        private void MarkVtableLoads()
        {
            var calls = blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => c.Op?.Kind == OpKind.CallVirtual && c.Arguments.Length > 0).ToArray();
            if (calls.Length == 0) return;
            var users = blocks.SelectMany(b => b.Statements)
                .SelectMany(s => (s is Phi phi ? phi.Sources.Select(v => (Variable: v, Expr: (Expr?)null)) : ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => (u.Variable, Expr: (Expr?)u)))
                    .Select(p => (p.Variable, Statement: s))).ToLookup(p => p.Variable, p => p.Statement);
            foreach (var call in calls)
            {
                // 目标：Load(klass + 常量)；klass：Load(接收者, 64)
                if (call.Target is not Use { Variable: var methodPointer } || !values.TryGetValue(methodPointer, out var target) || target is not Load { Width: 64 } entry) continue;
                var terms = new List<Expr>();
                void Add(Expr e) { if (e is Binary { Op: BinOp.Add } b) { Add(b.Left); Add(b.Right); } else terms.Add(e); }
                Add(Expand(entry.Address));
                if (terms.OfType<Use>().ToArray() is not [{ Variable: var klass }] || terms.Count(t => t is not Const) != 1) continue;
                var receiverValue = Expand(call.Arguments[0]);
                // 已通过同一引用的强制类型检查，isinst 结果与原对象身份相同。
                if (receiverValue is Use cast && results.TryGetValue(cast.Variable, out var castResult)
                    && castResult.Call is { Op.Kind: OpKind.IsInst, Op.Operand: TypeRef castType, Arguments: [Use original] }
                    && CheckedReference(original, castType, call.Address)) receiverValue = Expand(original);
                var joined = new List<Variable>();
                if (phis.TryGetValue(klass, out var klassPhi))
                {
                    if (!klassPhi.Sources.All(v => users[v].All(s => s is Phi p && p.Target == klassPhi.Target))) continue;
                    var sameReceiver = klassPhi.Sources.All(v => values.GetValueOrDefault(v) is Load { Width: 64 } load
                        && Expand(load.Address) == receiverValue);
                    var pairedReceivers = call.Arguments[0] is Use receiver && phis.TryGetValue(receiver.Variable, out var objectPhi)
                        && blocks.Any(b => b.Statements.OfType<Phi>().Any(p => p.Target == klassPhi.Target)
                            && b.Statements.OfType<Phi>().Any(p => p.Target == objectPhi.Target))
                        && klassPhi.Sources.Length == objectPhi.Sources.Length
                        && klassPhi.Sources.Zip(objectPhi.Sources).All(pair => values.GetValueOrDefault(pair.First) is Load { Width: 64, Address: Use obj }
                            && obj.Variable == pair.Second);
                    if (!sameReceiver && !pairedReceivers) continue;
                    joined.AddRange(klassPhi.Sources);
                }
                else if (!values.TryGetValue(klass, out var klassValue) || klassValue is not Load { Width: 64, Address: var objectAddress }
                    || Expand(objectAddress) != receiverValue) continue;
                // 类指针的使用：虚表项的读取，或作为调用实参（保守约定）。
                var entries = values.Where(p => p.Value is Load { Width: 64 } l && ReadsKlass(l.Address, klass)).Select(p => p.Key).ToHashSet();
                if (users[klass].Any(s => s is not Call && !(s is Define d && entries.Contains(d.Target)))) continue;
                runtime.Add(klass);
                runtime.UnionWith(joined);
                foreach (var e in entries) runtime.Add(e);
            }
        }

        private bool ReadsKlass(Expr address, Variable klass)
        {
            var expanded = Expand(address);
            if (expanded is Use { Variable: var only } && only == klass) return true;
            return expanded is Binary { Op: BinOp.Add } b && (b.Left is Use { Variable: var l } && l == klass && b.Right is Const
                || b.Left is Binary inner && ReadsKlass(inner, klass) && b.Right is Const);
        }

        /// <summary>VirtualInvokeData 只有 methodPtr(+0) 与 method(+8) 两个指针；不把任意运行时结构的读取当作可删除值。</summary>
        private bool IsInterfaceMetadataLoad(Expr value)
        {
            if (value is not Load { Width: 64 } load) return false;
            var address = Expand(load.Address);
            if (address is Binary { Op: BinOp.Add, Right: Const { Value: 0 or 8 } } add) address = Expand(add.Left);
            return address is Use u && results.TryGetValue(u.Variable, out var result) && result.Call.Op?.Kind == OpKind.InterfaceInvokeData;
        }

        [Analysis("内联", 50, After = ["运行时引用"])]
        private void Inline()
        {
            var uses = new Dictionary<Variable, List<(Block Block, int Index)>>();
            foreach (var block in blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    var statement = block.Statements[i];
                    // 写屏障地址由托管存储承担；保留值参数的使用，避免引用选择表达式丢失局部变量类型。
                    var operands = statement is Call { Op.Kind: OpKind.WriteBarrier, Arguments.Length: 2 } barrier
                        ? barrier.Arguments.Skip(1) : ExprMap.Operands(statement);
                    var used = statement is Phi phi ? phi.Sources.AsEnumerable()
                        : operands.SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable);
                    foreach (var v in used)
                    {
                        if (!uses.TryGetValue(v, out var list)) uses[v] = list = [];
                        list.Add((statement is Phi ? null! : block, i));
                    }
                }
            foreach (var block in blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                    if (block.Statements[i] is Define define && !runtime.Contains(define.Target) && !ExprMap.Walk(define.Value).Any(e => e is Load or FrameAddress)
                        && uses.TryGetValue(define.Target, out var at) && at is [var only] && only.Block == block && only.Index > i)
                        inlined.Add(define.Target);
            InlineStructArgumentLoads(uses);
        }

        /// <summary>
        /// 寄存器传递的结构体实参，其片直接读自内存（如 <c>r1 = this.ct._source</c> 再传 CancellationToken）：读取只被这次调用使用、
        /// 与调用在同一块且之间没有写内存或调用时，内联到实参处。片的叶子因此保留位置信息，可以整体传递该结构体字段，
        /// 不必单独读它的私有字段（<c>Compose</c>）。之间只有纯定义，读取推迟到调用处结果不变。
        /// </summary>
        private void InlineStructArgumentLoads(Dictionary<Variable, List<(Block Block, int Index)>> uses)
        {
            foreach (var block in blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Define { Value: Load } define || runtime.Contains(define.Target)
                        || !uses.TryGetValue(define.Target, out var at) || at is not [var only] || only.Block is null) continue;
                    // 沿直线链（唯一正常后继且它只有一个前驱，含 try 中调用自成一块时的直落）找到唯一的使用；之间只能有纯定义，
                    // 以及被调用方所属类型的类初始化（CIL 中由这次调用隐含触发，在实参求值之后，读取推迟到调用处顺序不变）。
                    TypeRef? initialized = null;
                    foreach (var statement in Straight(block, i))
                    {
                        // 已证明只承载调用元数据的写入不会改变托管实参的求值顺序。
                        if (dropped.Contains(statement)) continue;
                        if (statement is Call { Op: { Kind: OpKind.RunClassConstructor, Operand: TypeRef initType } } && initialized is null)
                        {
                            initialized = initType;
                            continue;
                        }
                        // 寄存器返回的结构体：片的读取只被返回使用时同样内联，叶子保留位置，可以整体返回该结构体字段（如 return this._ctx）。
                        if (statement is Return ret && ReferenceEquals(ret, only.Block.Statements[only.Index]))
                        {
                            if (owner.abi.Classify(method, out _)?.Return is { } returned && RegisterStruct(returned)) inlined.Add(define.Target);
                            break;
                        }
                        if (statement is Call { Op: null } call && ReferenceEquals(call, only.Block.Statements[only.Index]))
                        {
                            if (Resolve(call) is { } callee && (initialized is null || callee.Method.IsStatic && callee.DeclaringType.Equals(initialized))
                                && owner.abi.Classify(callee, out _) is { } signature
                                && signature.Parameters.Where(RegisterStruct).SelectMany(p => p.Pieces)
                                    .Any(p => ArgumentsOf(call).TryGetValue(p.Register, out var argument) && argument is Use u && u.Variable == define.Target))
                                inlined.Add(define.Target);
                            break;
                        }
                        if (statement is not (Define or Phi or Nop)) break;
                    }
                }
        }

        private Expr Expand(Expr e) => e is Use u && runtime.Contains(u.Variable) && values.TryGetValue(u.Variable, out var value) ? Expand(value) : e;

        /// <summary>栈帧：序言保存的被调用者保存寄存器删去；只被写入一次再装箱的栈槽并入装箱。其余栈访问为洞。</summary>
        [Analysis("帧槽", 60, After = ["帧区域", "栈上调用"])]
        private void FrameSlots()
        {
            var callFrames = new ManagedCallFrames(facts, owner.abi);
            var deadWrites = new HashSet<Stmt>(ReferenceEqualityComparer.Instance);
            var references = new Dictionary<long, List<Stmt>>();
            foreach (var block in blocks)
                foreach (var statement in block.Statements)
                    if (!dropped.Contains(statement) && (statement is not Call enumCall || !stackEnums.ContainsKey(enumCall))
                        && (statement is not Store savedArgument || !stackArgumentStores.ContainsKey(savedArgument) && !boxArgumentStores.ContainsKey(savedArgument)))
                    foreach (var e in ExprMap.Operands(statement).SelectMany(ExprMap.Walk))
                        if (e is FrameAddress frame)
                        {
                            if (!references.TryGetValue(frame.Offset, out var list)) references[frame.Offset] = list = [];
                            list.Add(statement);
                        }
            foreach (var (offset, users) in references)
            {
                var distinct = users.Distinct(ReferenceEqualityComparer.Instance).Cast<Stmt>().ToArray();
                if (distinct.All(s => s is Store { Target: FrameAddress at, Value: Use or Const } && at.Offset == offset)
                    && distinct.Cast<Store>().All(store => FrameWritebacks.Unread(blocks.SelectMany(b => b.Statements).Where(s => !dropped.Contains(s)),
                        store, callFrames.ArgumentSize, NoStackRead)))
                {
                    dropped.UnionWith(distinct);
                    deadWrites.UnionWith(distinct);
                    continue;
                }
                if (distinct is [Store { Target: FrameAddress, Value: Use { Variable: { Version: 0 } saved } } spill] && CalleeSaved.Concat([Storage.Gpr(29), Storage.Gpr(30)]).Contains(saved.Storage))
                {
                    dropped.Add(spill);
                    continue;
                }
                if (distinct is [Store { Target: FrameAddress } store, Call { Op.Kind: OpKind.Box } box] && box.Arguments is [_, FrameAddress] && SameBlockBefore(store, box))
                {
                    dropped.Add(store);
                    boxed[box] = store.Value;
                    continue;
                }
                var hole = Hole(distinct[0].Address, conflictingFrames.Contains(offset) ? $"栈 栈槽类型冲突 {offset:x}" : $"栈 栈槽 {offset:x} 的使用形态尚未支持");
                frameHoles[offset] = hole;
                foreach (var user in distinct)
                {
                    ledger.Block(user, hole);
                }
            }
            if (deadWrites.Count > 0)
            {
                foreach (var block in blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                    if (deadWrites.Contains(block.Statements[i])) block.Statements[i] = new Nop(block.Statements[i].Address, "未读取的栈快照");
                RemoveDeadDefinitions();
                definitions = IndexDefinitions();
            }
        }

        private bool SameBlockBefore(Stmt first, Stmt second) => blocks.Any(b =>
        {
            var i = b.Statements.IndexOf(first);
            var j = b.Statements.IndexOf(second);
            return i >= 0 && j > i;
        });

        /// <summary>对象分配与直线链上的构造调用合并为 newobj；跨块时另证可观察顺序与异常去向。</summary>
        [Analysis("分配", 70, After = ["运行时引用"])]
        private void Allocations()
        {
            foreach (var block in blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Call { Op: { Kind: OpKind.NewObject, Operand: DefinitionRef type } } allocation || allocation.Defines.FirstOrDefault() is not { } created) continue;
                    if (DelegateFacts.IsDelegate(type)) { DelegateAllocation(block, i, allocation, type, created); continue; }
                    if (BranchConstructors(block, i, allocation, type, created)) continue;
                    Call? constructor = null;
                    var inline = false;
                    RecoveryHole? failure = null;
                    var middle = new List<Stmt>();
                    foreach (var (current, statement) in AllocationPairing.Following(block, i))
                    {
                        if (!AllocationPairing.Uses(statement, created)) { middle.Add(statement); continue; }
                        MethodDef? forwarded = null;
                        if (statement is Call call && Receiver(call) is Use { Variable: var receiver } && receiver == created
                            && (call.Op is { Kind: OpKind.CallMethodPointer or OpKind.InvokeGeneric, Operand: MethodRef { Method: { Name: ".ctor", IsStatic: false } pointerCtor } } && pointerCtor.Owner == type.Definition
                                || call is { Op: null, Kind: CallKind.Direct, Target: Const target }
                                    && (facts.EntriesAt(target.Value).Any(e => e.Method is { Method: { Name: ".ctor", IsStatic: false } ctor } && ctor.Owner == type.Definition)
                                        || facts.EntriesAt(target.Value).Any(e => e.Method is { Method: { Name: ".ctor", IsStatic: false, Parameters.Count: 0 } ctor } && ctor.Owner != type.Definition)
                                            && (forwarded = owner.ForwardingConstructor(type, target.Value)) is not null)))
                        {
                            if (current != block && AllocationPairing.MotionProblem(function.Range, block, allocation, current, call,
                                middle.Where(s => !PrivateInvokerInitializer(s, call)), created) is { } problem)
                            {
                                failure = Hole(allocation.Address, $"分配 {type} {problem}");
                                break;
                            }
                            constructor = call;
                            if (forwarded is not null) forwardedConstructors[call] = new MethodRef(forwarded, type.Arguments, []);
                        }
                        else if (InlineConstructor(block, i, allocation, type, created))
                            inline = true;
                        else
                            failure = Hole(statement.Address, $"分配 {type} 在构造之前被使用");
                        break;
                    }
                    if (inline) continue;
                    if (constructor is null)
                    {
                        failure ??= Hole(allocation.Address, $"分配 {type} 没有配对的构造调用");
                        ledger.Block(allocation, failure);
                        continue;
                    }
                    dropped.Add(allocation);
                    constructed[constructor] = created;
                }
        }

        private static Expr? Receiver(Call call) => call.DelegateReceiver ?? (call.Op?.Kind == OpKind.InvokeGeneric
            || call.Sources.Length > 0 && call.Sources[0] == Storage.Gpr(0) ? call.Arguments[0] : null);

        // invoker 的独占实参栈槽不可被异常处理器或其他调用观察；纯值写入不限制分配配对。
        private bool PrivateInvokerInitializer(Stmt statement, Call constructor)
        {
            if (constructor.Op?.Kind != OpKind.InvokeGeneric || statement is not Store { Target: TypedFrame frame } store
                || frame.Region.Offset >= 0 || store.Value.Width != frame.Region.Size * 8) return false;
            return AllocationPairing.PrivateArgumentStore(store, constructor, blocks.SelectMany(b => b.Statements));
        }

        /// <summary>判空与越界的吸收（见类注释第 4 条）。</summary>
        [Analysis("检查吸收", 80, After = ["帧区域"])]
        private void Checks()
        {
            // 现有吸收规则只证明普通 CFG；EH 的保护域按语句划分，不能跨界移动抛出点。
            if (exceptionLayout is { Succeeded: true }) return;
            foreach (var block in blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Call { Op.Kind: OpKind.NullCheck or OpKind.BoundsCheck or OpKind.RunClassConstructor } check) continue;
                    var absorbed = check.Op!.Kind switch
                    {
                        OpKind.NullCheck => AbsorbNull(block, i, check.Arguments[0]),
                        OpKind.BoundsCheck => AbsorbBounds(block, i, check),
                        _ => check.Op.Operand is DefinitionRef type && Implied(block, i, type),
                    };
                    if (absorbed) dropped.Add(check);
                }
        }

        /// <summary>从 (block, index) 之后沿唯一正常后继（它只有一个前驱）依次列出语句；块末尾可以是跳转，也可以直接落入后继。</summary>
        private static IEnumerable<Stmt> Straight(Block block, int index)
        {
            var visited = new HashSet<Block>();
            while (visited.Add(block))
            {
                for (var k = index + 1; k < block.Statements.Count; k++)
                {
                    if (block.Statements[k] is Jump) break;
                    yield return block.Statements[k];
                }
                if (block.Statements.LastOrDefault() is Branch or Return or IndirectJump || block.NormalSuccessors.Count() != 1) yield break;
                var next = block.NormalSuccessors.Single();
                if (next.Predecessors.Count != 1 || next.IsLandingPad) yield break;
                block = next;
                index = -1;
            }
        }

        /// <summary>从 (block, index) 之后沿直线路径（无条件跳转进入只有一个前驱的块）依次列出语句。</summary>
        private static IEnumerable<Stmt> Following(Block block, int index)
        {
            var visited = new HashSet<Block>();
            while (visited.Add(block))
            {
                for (var k = index + 1; k < block.Statements.Count; k++)
                {
                    if (block.Statements[k] is Jump) break;
                    yield return block.Statements[k];
                }
                if (block.Statements.LastOrDefault() is not Jump || block.NormalSuccessors.Count() != 1) yield break;
                var next = block.NormalSuccessors.Single();
                if (next.Predecessors.Count != 1) yield break;
                block = next;
                index = -1;
            }
        }

        private bool AbsorbNull(Block block, int index, Expr value)
        {
            foreach (var statement in Following(block, index))
            {
                switch (statement)
                {
                    case Phi or Nop or Call { Op.Kind: OpKind.NullCheck }:
                        continue;
                    case Define define:
                        if (ExprMap.Walk(define.Value).Any(e => e is Load load && BaseOf(load.Address) == value)) return true;
                        continue;
                    case Store store:
                        return BaseOf(store.Target) == value && !IsStatic(store.Target);
                    case Call call when Receiver(call) == value:
                        if (call.Op is null or { Kind: OpKind.CallVirtual or OpKind.CallInterface or OpKind.CallDelegate or OpKind.CallGenericVirtual })
                        {
                            virtualCalls.Add(call);
                            return true;
                        }
                        return false;
                    default:
                        return false;
                }
            }
            return false;
        }

        private bool Implied(Block block, int index, DefinitionRef type)
        {
            bool Static(Expr address) => Split(address).Base is Symbol { Kind: SymbolKind.StaticFields, Value: DefinitionRef owner } && owner.Equals(type);
            foreach (var statement in Following(block, index))
            {
                switch (statement)
                {
                    case Phi or Nop or Call { Op.Kind: OpKind.InitClass }:
                        continue;
                    case Define define:
                        // 类构造可能改写其他字段或抛出；不能越过更早的业务读取推迟触发。
                        if (ExprMap.Walk(define.Value).OfType<Load>().FirstOrDefault() is { } load) return Static(load.Address);
                        continue;
                    case Store store:
                        return !ExprMap.Walk(store.Value).Any(e => e is Load) && Static(store.Target);
                    // beforefieldinit 静态调用不保证触发初始化；原生显式初始化必须保留。
                    case Call { Op: null, Kind: CallKind.Direct or CallKind.Tail, Target: Const target } call:
                        return !call.Arguments.SelectMany(ExprMap.Walk).Any(e => e is Load)
                            && facts.EntriesAt(target.Value).Any(e => e.Method is { Method: var m } && m.Owner == type.Definition && (m.IsStatic && (m.Owner.Attributes & System.Reflection.TypeAttributes.BeforeFieldInit) == 0
                            || m.Name == ".ctor" && !(m.Owner.IsValueType && (m.Owner.Attributes & System.Reflection.TypeAttributes.BeforeFieldInit) != 0)));
                    default:
                        return false;
                }
            }
            return false;
        }

        private bool AbsorbBounds(Block block, int index, Call check)
        {
            if (check.Arguments is not [var checkedIndex, var length] || BaseOf(StripLength(length)) is not { } array) return false;
            foreach (var statement in Following(block, index))
            {
                switch (statement)
                {
                    case Phi or Nop:
                        continue;
                    case Define define:
                        if (ExprMap.Walk(define.Value).OfType<Load>().Any(l => ElementOf(l.Address) is var (a, x) && a == array && SameIndex(x, checkedIndex))) return true;
                        continue;
                    case Store store:
                        return ElementOf(store.Target) is var (a2, x2) && a2 == array && SameIndex(x2, checkedIndex);
                    default:
                        return false;
                }
            }
            return false;
        }

        private Expr StripLength(Expr length)
        {
            if (length is Use u && values.TryGetValue(u.Variable, out var value)) length = value;
            while (length is Convert { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate } c) length = c.Operand;
            return length is Load { Address: var address } && Split(address).Offset == RuntimeLayout.ArrayMaxLength ? address : new Unknown("length", 64);
        }

        private bool SameIndex(Expr element, Expr checkedIndex)
        {
            Expr Strip(Expr e)
            {
                while (true)
                {
                    if (e is Convert { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend } c) e = c.Operand;
                    else if (e is Use { Width: < 64 } u) return new Use(u.Variable, u.Variable.Width);
                    else return e;
                }
            }
            return Strip(element) == Strip(checkedIndex);
        }

        // ---------- 调用目标（地址分解见 MethodRecovery.Memory.cs） ----------

        private static Dictionary<Storage, Expr> ArgumentsOf(Call call) => call.ArgumentsBySource();

        /// <summary>托管调用的方法（具体实例）；依据尚不足（接收者类型未定）时为 null。</summary>
        private MethodRef? Resolve(Call call)
        {
            if (callBindings.Cached(call, analyses.Version) is { } cached) return cached;
            var result = ResolveOnce(call);
            // 封闭实例：经自身 MethodInfo/RGCTX 得到的方法保留泛型参数形式（如 IUniTaskSource<T>.GetResult），代入实例的实参。
            if ((ClosedInstance || SharedDefinition) && result is not null)
                result = result with
                {
                    TypeArguments = result.TypeArguments.Select(t => t.Substitute(method.TypeArguments, method.MethodArguments)).ToArray(),
                    MethodArguments = result.MethodArguments.Select(t => t.Substitute(method.TypeArguments, method.MethodArguments)).ToArray(),
                };
            callBindings.Remember(call, result, analyses.Version);
            return result;
        }

        private MethodRef? ResolveOnce(Call call)
        {
            if (call.Op is null && call.Target is Const inferredTarget && facts.Unregistered.At(inferredTarget.Value) is { } identity)
                return UnregisteredMethods.Resolve(identity, call, Expand, owner.abi, out _);
            var receiver = Receiver(call) is { } r ? TypeOfValue(r) : null;
            if (receiver is GenericParameterRef { ReferenceBase: { } constraint }) receiver = constraint;
            switch (call.Op)
            {
                case { Kind: OpKind.CallMethodPointer, Operand: MethodRef pointerMethod }:
                    return pointerMethod;
                case null when call.Target is Const target:
                {
                    var candidates = facts.EntriesAt(target.Value).Where(e => e.Kind is EntryKind.Method or EntryKind.GenericMethod && e.Method is not null)
                        .Select(e => e.Method!.Method).Distinct().ToArray();
                    // 未注册的本地副本：与接收者类型上某个方法 L2 形状相同（CopyOf），按该方法解析。
                    if (candidates.Length == 0)
                    {
                        foreach (var candidateType in ReceiverTypes(call, receiver))
                            if (candidateType is DefinitionRef { Arguments.Count: 0 } receiverType && owner.CopyOf(target.Value, receiverType.Definition) is { } copy)
                                return new MethodRef(copy, [], []);
                        return ConversionCopy(call, target.Value);
                    }
                    var symbolic = call.Arguments.Select(Expand).OfType<Symbol>().Where(s => s.Kind == SymbolKind.Method).Select(s => (MethodRef)s.Value)
                        .FirstOrDefault(m => candidates.Contains(m.Method));
                    if (symbolic is not null) return symbolic;
                    // RGCTX 的 constrained 项携带值类型及接口身份；用槽位核对直接目标后保留该实例实参。
                    for (var i = 0; i < call.Arguments.Length; i++)
                        if (Expand(call.Arguments[i]) is Symbol { Kind: SymbolKind.Constrained, Value: ValueTuple<TypeRef, MethodRef> constrained }
                            && ConstrainedImplementation(constrained.Item1, constrained.Item2, candidates) is { } implementation
                            && owner.abi.Classify(implementation, out _)?.MethodInfo?.Register == call.Sources[i]) return implementation;
                    // 编译器生成的嵌套类型沿用外层泛型实参；未读取 this 的直接入口仍可由这层身份解析。
                    if (candidates is [var nestedTarget] && nestedTarget.GenericParameters.Count == 0
                        && nestedTarget.Owner.GenericParameters.Count > 0 && nestedTarget.Owner.GenericParameters.Count <= method.TypeArguments.Count)
                    {
                        for (var parent = method.Method.Owner; parent is not null; parent = parent.DeclaringType)
                        {
                            if (parent != nestedTarget.Owner) continue;
                            var inferred = new MethodRef(nestedTarget, method.TypeArguments.Take(parent.GenericParameters.Count).ToArray(), []);
                            if (inferred.Method.IsStatic || owner.abi.Classify(inferred, out _)?.This is { } unused && UnusedInput(call, inferred, unused)) return inferred;
                        }
                    }
                    // 唯一直接入口的 this 若确实未用，前一次调用留下的无关对象不能否定其方法身份。
                    if (candidates is [var unique] && !unique.IsStatic && unique.GenericParameters.Count == 0 && unique.Owner.GenericParameters.Count == 0
                        && receiver is not null && !types.IsAssignable(receiver, new DefinitionRef(unique.Owner, [])))
                    {
                        var direct = new MethodRef(unique, [], []);
                        if (owner.abi.Classify(direct, out _)?.This is { } unusedThis && UnusedInput(call, direct, unusedThis)) return direct;
                    }
                    var available = new List<CallCandidate>();
                    foreach (var candidate in candidates.OrderBy(c => c.Index))
                    {
                        if (candidate.GenericParameters.Count > 0)
                        {
                            available.Add(new(MethodRef.Open(candidate), "native-entry", "call.generic-arguments-missing"));
                            continue;
                        }
                        if (candidate.Owner.GenericParameters.Count == 0)
                        {
                            var compatible = candidate.IsStatic || receiver is null || types.IsAssignable(receiver, new DefinitionRef(candidate.Owner, [])) || receiver is ByRefRef
                                || Receiver(call) is Use reference && CheckedReference(reference, new DefinitionRef(candidate.Owner, []), call.Address);
                            available.Add(new(new(candidate, [], []), "native-entry+receiver", compatible ? null : "call.receiver-incompatible"));
                            continue;
                        }
                        if (!candidate.IsStatic && (Instantiation(receiver, candidate.Owner) ?? StructReceiverArguments(Receiver(call), candidate.Owner)) is { } typeArguments)
                            available.Add(new(new(candidate, typeArguments, []), "native-entry+receiver-instance"));
                        else available.Add(new(MethodRef.Open(candidate), "native-entry", "call.type-arguments-missing"));
                    }
                    var accepted = available.Where(c => c.Rejection is null).Select(c => c.Method).Distinct().ToArray();
                    var selected = accepted.Length == 1 ? accepted[0] : null;
                    callBindings.Candidates(call, target.Value, available, selected,
                        accepted.Length == 0 ? "blocked" : accepted.Length == 1 ? "bound" : "conflict");
                    return selected;
                }
                case { Kind: OpKind.CallVirtual, Operand: int slot }:
                    // 接收者静态类型的 vtable 槽位：callvirt 按对象的实际类型在同一槽位分派
                    if (receiver is not DefinitionRef { Definition: var type } || slot >= type.VTable.Count || type.VTable[slot] is not { } entry) return null;
                    if (entry.Method.Owner.GenericParameters.Count == 0) return entry with { TypeArguments = [] };
                    return Instantiation(receiver, entry.Method.Owner) is { } arguments ? entry with { TypeArguments = arguments } : null;
                case { Kind: OpKind.CallGenericVirtual, Operand: MethodRef generic } when generic.Method.IsVirtual:
                    return generic;
                case { Kind: OpKind.CallInterface, Operand: ValueTuple<object?, int> pair } when pair.Item1 is DefinitionRef itf:
                    return itf.Definition.Methods.FirstOrDefault(m => m.Slot == pair.Item2) is { } interfaceMethod ? new MethodRef(interfaceMethod, itf.Arguments, []) : null;
                case { Kind: OpKind.CallDelegate } when receiver is DefinitionRef d:
                    return d.Definition.Methods.FirstOrDefault(m => m.Name == "Invoke" && !m.IsStatic) is { } invoke ? new MethodRef(invoke, d.Arguments, []) : null;
                case { Kind: OpKind.CallDelegate, Operand: MethodRef knownInvoke } when receiver is null:
                    return knownInvoke;
                default:
                    return null;
            }
        }

        /// <summary>接收者可能的类型：值的类型（ByRef 取元素），以及地址指向已定型根中某个偏移处的结构体字段类型（值类型实例方法的 this）。</summary>
        private IEnumerable<TypeRef> ReceiverTypes(Call call, TypeRef? receiver)
        {
            if (receiver is ByRefRef { Element: var element }) yield return element;
            else if (receiver is not null) yield return receiver;
            if (Receiver(call) is not { } address) yield break;
            var (root, offset, rest) = Split(address);
            if (root is null || rest.Count != 0 || TypeOfAddressBase(root) is not { } rootType) yield break;
            if (offset == 0 && rootType is ByRefRef { Element: var self }) yield return self;
            foreach (var path in StructPaths(rootType).Where(p => p.Offset == offset && types.Kind(p.Type) == TypeKind.Struct)) yield return path.Type;
        }

        /// <summary>type 或其基类中 definition 的实例实参。</summary>
        private static IReadOnlyList<TypeRef>? Instantiation(TypeRef? type, TypeDef definition)
        {
            if (type is ByRefRef byRef) type = byRef.Element;
            if (type is GenericParameterRef { ReferenceBase: { } constraint }) type = constraint;
            for (var current = type; current is DefinitionRef d; current = d.Definition.BaseType?.Substitute(d.Arguments, []))
                if (d.Definition == definition) return d.Arguments;
            return null;
        }

        private static TypeRef Concrete(MethodRef m, TypeRef type) => type.Substitute(m.TypeArguments, m.MethodArguments);

        // ---------- 类型推导 ----------

        private TypeRef? TypeOfValue(Expr e)
        {
            return Recover(e, null).TryGet(out var value, out _) ? value.Type : null;
        }

        /// <summary>局部变量的类型与位宽：整数类型按位宽取同符号的整数类型，使二者一致（布尔值允许 1 位或 8 位）。</summary>
        private RecoveryResult<LocalValue> LocalOf(Variable v)
        {
            if (CheckPoison(v) is { } poison) return poison;
            if (runtime.Contains(v)) return Fail(0, $"运行时引用 {v} 作为托管值");
            if (!known.TryGetValue(v, out var type)) return new RecoveryFailure(0, $"变量 {v} 的类型未确定", Unresolved: v, Code: "recovery.variable-type");
            var width = LocalWidth(v);
            switch (types.Kind(type))
            {
                case TypeKind.Float or TypeKind.Double when types.Bits(type) != width:
                    return Fail(0, $"浮点 变量 {v} 的类型 {type} 与定义位宽 {width} 不一致");
                case TypeKind.Int when types.Bits(type) != width && type is not GenericParameterRef:
                case TypeKind.Bool when width is not (1 or 8):
                    if (width is not (1 or 8 or 16 or 32 or 64)) return Fail(0, $"变量 {v} 的位宽 {width}");
                    type = IntegerOf(width, ManagedTypes.IsSigned(type));
                    break;
                case TypeKind.Pointer when type is ByRefRef: break;
                case TypeKind.Pointer when width == 64 && ManagedTypes.IsNativePointer(type): break;
                case TypeKind.Struct or TypeKind.Pointer or TypeKind.Void or null:
                    return Fail(0, $"变量 {v} 的类型 {type} 尚未支持");
            }
            return new LocalValue(v, type, width);
        }

        private int LocalWidth(Variable v)
        {
            if (values.TryGetValue(v, out var value)) return value.Width;
            if (results.TryGetValue(v, out var result))
                return known.TryGetValue(v, out var t) ? Math.Max(types.Bits(t), 8) : result.Call.Results[result.Index].Width;
            if (phis.TryGetValue(v, out var phi))
            {
                if (known.TryGetValue(v, out var reference) && types.Kind(reference) == TypeKind.Reference) return 64;
                // 各来源位宽的最大值；常量来源只要求容得下它的值。环上的来源（正在计算的 φ）跳过。
                if (!phiInProgress.Add(v)) return 0;
                try
                {
                    var width = 0;
                    foreach (var source in phi.Sources)
                    {
                        if (values.TryGetValue(source, out var c) && c is Const constant)
                            width = Math.Max(width, constant.Value == 0 ? 1 : 64 - System.Numerics.BitOperations.LeadingZeroCount(constant.Value));
                        else if (source.Version == 0 && arguments.TryGetValue(source.Storage, out var argument)) width = Math.Max(width, argument.Width);
                        else width = Math.Max(width, LocalWidth(source));
                    }
                    if (width == 0) width = known.TryGetValue(v, out var t) ? Math.Max(types.Bits(t), 8) : 64;
                    // 结构体 ABI 返回片可含高位填充；终端整数 φ 只保留所有实际读取需要的低位。
                    if (known.TryGetValue(v, out var integer) && types.Kind(integer) is TypeKind.Int or TypeKind.Bool
                        && !phiUses.GetValueOrDefault(v, []).Any()
                        && phi.Sources.Any(s => results.TryGetValue(s, out var r) && Resolve(r.Call) is { } callee
                            && owner.abi.Classify(callee, out _)?.Return is { } returned && RegisterStruct(returned)))
                    {
                        var reads = blocks.SelectMany(b => b.Statements).Where(s => s is not Phi)
                            .SelectMany(s => ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>()).Where(u => u.Variable == v).ToArray();
                        if (reads.Length > 0) width = Math.Min(width, reads.Max(u => u.Width));
                    }
                    return width switch { 1 => 1, <= 8 => 8, <= 16 => 16, <= 32 => 32, _ => 64 };
                }
                finally { phiInProgress.Remove(v); }
            }
            return v.Width;
        }

        private readonly HashSet<Variable> phiInProgress = [];

        // ---------- 值恢复 ----------

        private NullPathFacts? nullPaths;

        private RecoveryResult<ManagedValue> RecoverAs(Expr e, TypeRef target, ulong address)
        {
            if (types.Kind(target) == TypeKind.Reference && e is Use { Width: 64 }
                && (nullPaths ??= new NullPathFacts(function)).IsNull(e, address))
                return new ConstantValue(0, target, 64);
            if (types.Kind(target) == TypeKind.Reference && e is Use { Width: 64 } referenceValue
                && TypeOfValue(e) is { } sourceType && types.Kind(sourceType) == TypeKind.Reference
                && !types.IsAssignable(sourceType, target) && CheckedReference(referenceValue, target, address))
                return Recover(e, sourceType).Map<ManagedValue>(value => new IsInstValue(value, target));
            return target is ByRefRef reference ? StructAddress(e, reference.Element) : Recover(e, target).Bind(value => Coerce(value, target, address));
        }

        /// <summary>把值调整为 target 类型的位宽：引用要求可赋值；整数截断或补零（局部变量高位为 0）；同宽的整数与浮点按位重解释。</summary>
        private RecoveryResult<ManagedValue> Coerce(ManagedValue value, TypeRef target, ulong address)
        {
            if (target is GenericParameterRef { NativeScalar: not null })
            {
                if (value.Type.Equals(target)) return value;
                if (value is ConstantValue { Bits: 0 }) return new ConstantValue(0, target, types.Bits(target));
                return Fail(address, $"泛型复制 {value.Type} 不能转换为 {target}");
            }
            if (value.Type is GenericParameterRef { NativeScalar: not null }) return Fail(address, $"泛型复制 不能将 {value.Type} 当作 {target}");
            // 窄于片的整数目标只取低位（如寄存器结构体的首叶子作为 int 实参；高位是填充）。
            if (value is Fragment fragment)
            {
                var projected = types.Kind(target) is TypeKind.Int && types.Bits(target) < fragment.Width ? Slice(fragment, 0, types.Bits(target)) : Pack(fragment);
                if (!projected.TryGet(out value, out var failure)) return failure;
            }
            if (value is Fragment remaining && !Pack(remaining).TryGet(out value, out var packFailure)) return packFailure;
            // 打包寄存器中的浮点叶子已经有托管类型；来回的同宽位重解释是恒等值。
            if (value is ConversionValue { Kind: ConvKind.Bitcast } bitcast && bitcast.Operand.Type.Equals(target)) return bitcast.Operand;
            // 已是目标类型的值（如寄存器结构体的 IntPtr 叶子 Playable.m_Handle.m_Handle）原样使用。
            if (value.Type.Equals(target) && types.Kind(target) == TypeKind.Pointer && target is DefinitionRef) return value;
            var kind = types.Kind(target);
            var width = kind is TypeKind.Bool ? 8 : types.Bits(target);
            switch (kind)
            {
                case TypeKind.Pointer when ManagedTypes.IsNativePointer(target):
                    if (value is ConstantValue { Bits: 0, Width: 64 }) return new ConstantValue(0, target, 64);
                    if (value.Width == 64 && ManagedTypes.IsNativePointer(value.Type))
                        return value.Type.Equals(target) ? value : new ConversionValue(ConvKind.Bitcast, value, target, 64);
                    return Fail(address, $"指针 {value.Type} 不能转换为 {target}");
                case TypeKind.Reference:
                    if (value is ConstantValue { Bits: 0 }) return new ConstantValue(0, target, 64);
                    if (value.Type is GenericParameterRef { IsReferenceConstrained: false } generic && !target.Equals(generic)
                        && types.IsAssignable(generic, target)) return new BoxValue(value, generic, target);
                    if (types.Kind(value.Type) == TypeKind.Reference && types.IsAssignable(value.Type, target)) return value;
                    return Fail(address, $"类型 {value.Type} 不能赋给 {target}");
                case TypeKind.Bool or TypeKind.Int:
                    if (value is ConstantValue c) return new ConstantValue(c.Bits & Expr.Mask(width), target, width);
                    switch (types.Kind(value.Type))
                    {
                        case TypeKind.Bool or TypeKind.Int:
                            if (value.Width == width) return value;
                            return new ConversionValue(value.Width > width ? ConvKind.Truncate : ConvKind.ZeroExtend, value, target, width);
                        case TypeKind.Float or TypeKind.Double when value.Width == width:
                            return new ConversionValue(ConvKind.Bitcast, value, target, width);
                    }
                    return Fail(address, $"类型 {value.Type} 不能作为整数 {target}");
                case TypeKind.Float or TypeKind.Double:
                    if (value is ConstantValue f && f.Width == width) return new ConstantValue(f.Bits, target, width);
                    if (types.Kind(value.Type) == kind && value.Width == width) return value;
                    if (types.Kind(value.Type) == TypeKind.Int && value.Width == width) return new ConversionValue(ConvKind.Bitcast, value, target, width);
                    return Fail(address, $"类型 {value.Type} 不能作为浮点 {target}");
                default:
                    return Fail(address, $"类型 目标类型 {target} 尚未支持");
            }
        }

        private DefinitionRef IntegerOf(int width, bool signed) => width == 1 ? types.Boolean : types.Integer(width, signed);

        /// <summary>恢复表达式；结果的位宽等于表达式的位宽。hint 只用于给常量定型。</summary>
        private RecoveryResult<ManagedValue> Recover(Expr e, TypeRef? hint)
        {
            RecoveryFailure failure;
            switch (e)
            {
                case Intrinsic { Name: "pinned_array_start", Arguments: [var array] }:
                    if (!Recover(array, null).TryGet(out var pinned, out failure)) return failure;
                    return pinned.Type is ArrayRef { IsVector: true } arrayType ? new PinnedArrayValue(pinned, arrayType)
                        : Fail(0, "固定地址 来源不是一维数组");
                case Intrinsic { Name: "managed_field_address" or "managed_generic_buffer" or "managed_generic_argument" } address: return SharedAddress(address);
                case TypedFrame f: return new AddressValue(f.Region.Local);
                case Const c:
                {
                    if (hint is GenericParameterRef { NativeScalar: not null } && c.Value != 0) return Fail(0, "泛型复制 只接受默认值常量");
                    if (hint is not null)
                    {
                        var kind = types.Kind(hint);
                        if (kind == TypeKind.Reference && c.Value == 0) return new ConstantValue(0, hint, 64);
                        if (ManagedTypes.IsNativePointer(hint) && c.Value == 0 && c.Width == 64) return new ConstantValue(0, hint, 64);
                        if (kind is TypeKind.Int or TypeKind.Float or TypeKind.Double && types.Bits(hint) == c.Width) return new ConstantValue(c.Value, hint, c.Width);
                        if (kind == TypeKind.Bool && c.Width is 1 or 8) return new ConstantValue(c.Value, hint, c.Width);
                    }
                    if (c.Width is not (1 or 8 or 16 or 32 or 64)) return Fail(0, $"常量 位宽 {c.Width}");
                    return new ConstantValue(c.Value, IntegerOf(c.Width, true), c.Width);
                }
                case Use u:
                    return Variable(u.Variable, u.Width);
                case Extract extract: return Recover(extract.Operand, null).Bind(value => Slice(value, extract.Low, extract.Width));
                case Insert insert: return InsertedFragment(insert);
                case Load load:
                    return Location(load.Address, load.Width);
                case Symbol { Kind: SymbolKind.String, Value: string text }:
                    return new StringValue(text, types.String);
                case Binary b:
                    return Binary(b);
                case Unary { Op: UnOp.Neg or UnOp.Not } u:
                {
                    if (!Recover(u.Operand, hint).TryGet(out var operand, out failure)) return failure;
                    if (operand is Fragment f && !Pack(f).TryGet(out operand, out failure)) return failure;
                    if (operand.Type is GenericParameterRef { NativeScalar: not null } || types.Kind(operand.Type) is not (TypeKind.Int or TypeKind.Bool)) return Fail(0, $"运算 {u.Op} 的操作数类型 {operand.Type}");
                    return new UnaryValue(u.Op, operand, IntegerOf(u.Width, ManagedTypes.IsSigned(operand.Type)), u.Width);
                }
                case Unary { Op: UnOp.FNeg or UnOp.FAbs or UnOp.FSqrt or UnOp.FFloor or UnOp.FCeil or UnOp.FTrunc or UnOp.FRoundEven } u:
                    return FloatingNegation(u);
                case Compare c:
                    return Comparison(c);
                case Convert c:
                    return Conversion(c, hint);
                // klass == Class<T>（T sealed）? obj : null 即 obj as T，结果类型是 T。
                case Ir.Select { Condition: Compare { Cond: Cond.Eq } test, False: Const { Value: 0 } } s
                    when SealedOperands(test) is var (klass, sealedType) && objectClasses.TryGetValue(klass, out var tested) && s.True == tested:
                    return Recover(tested, types.Object).Map<ManagedValue>(value => new IsInstValue(value, sealedType));
                case Ir.Select s:
                {
                    if (!Recover(s.Condition, types.Boolean).TryGet(out var condition, out failure)) return failure;
                    // 常量臂没有独立类型；先从另一臂取得引用或浮点类型，避免把 null 当成 long。
                    if (hint is null && s.True is Const && s.False is not Const) hint = TypeOfValue(s.False);
                    if (!Recover(s.True, hint).TryGet(out var whenTrue, out failure)) return failure;
                    if (whenTrue is Fragment f && !Pack(f).TryGet(out whenTrue, out failure)) return failure;
                    if (!Recover(s.False, whenTrue.Type).Bind(value => Coerce(value, whenTrue.Type, 0)).TryGet(out var whenFalse, out failure)) return failure;
                    if (whenTrue.Width != s.Width || whenFalse.Width != s.Width) return Fail(0, "选择 两侧位宽不一致");
                    return new ChoiceValue(condition, whenTrue, whenFalse, whenTrue.Type, s.Width);
                }
                case Logical l:
                    return Recover(l.Left, types.Boolean).Bind(Truth).Bind(left => Recover(l.Right, types.Boolean).Bind(Truth)
                        .Map<ManagedValue>(right => new BooleanValue(l.IsAnd, left, right, types.Boolean)));
                case Not n:
                    return Recover(n.Operand, types.Boolean).Bind(Truth).Map<ManagedValue>(value => new NegatedValue(value, types.Boolean));
                default:
                    return Fail(0, $"表达式 {e.GetType().Name} 尚未支持");
            }
        }

        private static RecoveryResult<ManagedValue> Truth(ManagedValue value) => value.Width == 1 ? value
            : Fail(0, "条件 不是一位的布尔值");

        private RecoveryResult<ManagedValue> Variable(Variable v, int width)
        {
            if (collectingExceptionDemand) exceptionDemand.Add(v);
            // SSA 的负版本是未定义/被调用破坏的值，不能因 phi 反向推断出类型就读零初始化局部。
            if (exceptionLayout is { Succeeded: true } && v.Version < 0) return Fail(0, $"异常区域 读取未定义 SSA 值 {v}");
            if (CheckPoison(v) is { } poison) return poison;
            if (arrayOffsets.TryGetValue(v, out var offset)) return Recover(Fold.Convert(ConvKind.Truncate, offset, width), null);
            if (exceptionValues.TryGetValue(v, out var exception)) return exception;
            if (width == 64 && v.Version == 0 && indirectRoots.TryGetValue(v.Storage, out var root)) return root;
            if (!RegisterPiece(v, width).TryGet(out var piece, out var failure)) return failure;
            if (piece is not null) return piece;
            if (!StructPhiPiece(v, width).TryGet(out var merged, out failure)) return failure;
            if (merged is not null) return merged;
            if (!FragmentVariable(v, width).TryGet(out var fragment, out failure)) return failure;
            if (fragment is not null) return fragment;
            ManagedValue value;
            bool signed;
            if (v.Version == 0)
            {
                if (!arguments.TryGetValue(v.Storage, out var argument)) return Fail(0, $"入口 读取了参数之外的入口寄存器 {v}");
                value = new ArgumentValue(argument.Index, argument.Type, argument.Width);
                signed = ManagedTypes.IsSigned(argument.Type);
            }
            else if (inlined.Contains(v))
            {
                var hint = known.GetValueOrDefault(v);
                if (!Recover(values[v], hint is not null && types.Kind(hint) is TypeKind.Float or TypeKind.Double ? hint : null).TryGet(out value, out failure)) return failure;
                signed = false;
            }
            else
            {
                if (!LocalOf(v).TryGet(out var local, out failure)) return failure;
                value = local;
                signed = false;
            }
            if (value is Fragment inlineFragment)
                return width < value.Width ? Slice(inlineFragment, 0, width) : ResizeFragment(inlineFragment, width);
            if (width == value.Width) return value;
            if (value.Type is GenericParameterRef { NativeScalar: not null } && width >= types.Bits(value.Type))
                return new ConversionValue(ConvKind.ZeroExtend, value, value.Type, width);
            if (types.Kind(value.Type) is not (TypeKind.Int or TypeKind.Bool)) return Fail(0, $"位宽 {value.Type} 以 {width} 位读取");
            if (width is not (1 or 8 or 16 or 32 or 64)) return Fail(0, $"位宽 {width} 的整数转换尚未支持");
            return new ConversionValue(width < value.Width ? ConvKind.Truncate : signed ? ConvKind.SignExtend : ConvKind.ZeroExtend, value,
                IntegerOf(width, ManagedTypes.IsSigned(value.Type)), width);
        }

        private RecoveryResult<ManagedValue> Binary(Binary b)
        {
            // C++ bool 传参取低一位；布局见证为 bool 的 T 在托管侧仍是同一个 T 值。
            RecoveryFailure failure;
            if (b is { Op: BinOp.And, Right: Const { Value: 1 } })
            {
                if (!Recover(b.Left, null).TryGet(out var boolean, out failure)) return failure;
                if (boolean.Type is GenericParameterRef { NativeScalar: { } scalar } && types.Kind(scalar) == TypeKind.Bool)
                    return new ConversionValue(ConvKind.ZeroExtend, boolean, boolean.Type, b.Width);
            }
            if (b is { Op: BinOp.Ror, Width: 32 or 64 })
            {
                var shift = new Binary(BinOp.And, b.Right, Expr.C((ulong)b.Width - 1, b.Right.Width), b.Right.Width);
                var opposite = new Binary(BinOp.And, new Unary(UnOp.Neg, shift, shift.Width), Expr.C((ulong)b.Width - 1, shift.Width), shift.Width);
                return Recover(new Binary(BinOp.Or, new Binary(BinOp.LShr, b.Left, shift, b.Width),
                    new Binary(BinOp.Shl, b.Left, opposite, b.Width), b.Width), null);
            }
            if (b.Op is BinOp.FAdd or BinOp.FSub or BinOp.FMul or BinOp.FDiv or BinOp.FMin or BinOp.FMax or BinOp.FMinNumber or BinOp.FMaxNumber)
            {
                if (b.Width is not (32 or 64)) return Fail(0, $"运算 {b.Op} 的浮点宽度 {b.Width} 尚未支持");
                var floating = b.Width == 32 ? types.Single : types.Double;
                if (!Recover(b.Left, floating).Bind(value => Coerce(value, floating, 0)).TryGet(out var fl, out failure)) return failure;
                if (!Recover(b.Right, floating).Bind(value => Coerce(value, floating, 0)).TryGet(out var fr, out failure)) return failure;
                return new BinaryValue(b.Op, fl, fr, floating, b.Width);
            }
            if (b.Op is not (BinOp.Add or BinOp.Sub or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor or BinOp.Shl or BinOp.LShr or BinOp.AShr or BinOp.SDiv or BinOp.UDiv))
                return Fail(0, $"运算 {b.Op} 尚未支持");
            ManagedValue left, right;
            if (b.Left is Const && b.Right is not Const)
            {
                if (!Recover(b.Right, null).TryGet(out right, out failure)) return failure;
                if (!Recover(b.Left, right.Type).TryGet(out left, out failure)) return failure;
            }
            else
            {
                if (!Recover(b.Left, null).TryGet(out left, out failure)) return failure;
                if (!Recover(b.Right, b.Op is BinOp.Shl or BinOp.LShr or BinOp.AShr ? null : left.Type).TryGet(out right, out failure)) return failure;
            }
            if (!FrameShift(b.Op, left, right, b.Width).TryGet(out var projected, out failure)) return failure;
            if (projected is not null) return projected;
            if (b.Op == BinOp.Add && b.Width == 64 && left.Type is PointerRef && types.Kind(right.Type) == TypeKind.Int)
                return new PointerOffsetValue(left, right);
            if (b.Op == BinOp.Add && b.Width == 64 && right.Type is PointerRef && types.Kind(left.Type) == TypeKind.Int)
                return new PointerOffsetValue(right, left);
            // 掩码清除的填充位来自指令语义；保留的位仍须来自已知叶子。
            if (b.Op == BinOp.And && left is Fragment masked && right is ConstantValue { Bits: var mask })
            {
                if (!MaskFragment(masked, mask, b.Width).TryGet(out var kept, out failure)) return failure;
                if (kept is not null) return kept;
            }
            if (left is Fragment lf && !Pack(lf).TryGet(out left, out failure)) return failure;
            if (right is Fragment rf && !Pack(rf).TryGet(out right, out failure)) return failure;
            if (left.Type is GenericParameterRef { NativeScalar: not null } || right.Type is GenericParameterRef { NativeScalar: not null })
                return Fail(0, "泛型复制 不支持原生数值比较");
            foreach (var operand in new[] { left, right })
                    if (operand.Type is GenericParameterRef { NativeScalar: not null } || types.Kind(operand.Type) is not (TypeKind.Int or TypeKind.Bool)) return Fail(0, $"运算 {b.Op} 的操作数类型 {operand.Type}");
            return new BinaryValue(b.Op, left, right, IntegerOf(b.Width, b.Op == BinOp.SDiv || b.Op != BinOp.UDiv && ManagedTypes.IsSigned(left.Type)), b.Width);
        }

        private RecoveryResult<Fragment?> MaskFragment(Fragment fragment, ulong mask, int width)
        {
            ulong Bits(int low, int bits) => mask & (Expr.Mask(bits) << low);
            var parts = new List<Part>();
            var cursor = 0;
            foreach (var part in fragment.Parts.OrderBy(p => p.Low).Append(new Part(width, new ConstantValue(0, types.Int32, 0))))
            {
                // 填充必须整段被清；逐字节表示可覆盖 bool 与 int 之间的三字节间隔。
                if (part.Low > cursor)
                {
                    var gap = part.Low - cursor;
                    if (Bits(cursor, gap) != 0 || gap % 8 != 0) return (Fragment?)null;
                    for (var low = cursor; low < part.Low; low += 8)
                        parts.Add(new Part(low, new ConstantValue(0, types.Byte, 8)));
                }
                if (part.Low >= width) break;
                var leafMask = Bits(part.Low, part.Value.Width) >> part.Low;
                if (leafMask == Expr.Mask(part.Value.Width)) parts.Add(part);
                else if (leafMask == 0) parts.Add(new Part(part.Low, new ConstantValue(0, types.Integer(part.Value.Width, false), part.Value.Width)));
                else
                {
                    if (types.Kind(part.Value.Type) is not (TypeKind.Int or TypeKind.Bool)) return (Fragment?)null;
                    var integer = types.Integer(part.Value.Width, false);
                    if (!Coerce(part.Value, integer, 0).TryGet(out var converted, out var failure)) return failure;
                    parts.Add(new Part(part.Low, new BinaryValue(BinOp.And, converted,
                        new ConstantValue(leafMask, integer, part.Value.Width), integer, part.Value.Width)));
                }
                cursor = part.Low + part.Value.Width;
            }
            return new Fragment(parts, fragment.Type, width);
        }

        private RecoveryResult<ManagedValue> Comparison(Compare c)
        {
            RecoveryFailure failure;
            if (c.Cond is Cond.Eq or Cond.Ne && SealedOperands(c) is var (klass, sealedType) && objectClasses.TryGetValue(klass, out var checkedObject))
                return Recover(checkedObject, types.Object).Map<ManagedValue>(value => new ComparisonValue(c.Cond == Cond.Eq ? Cond.Ne : Cond.Eq, new IsInstValue(value, sealedType),
                    new ConstantValue(0, sealedType, 64), types.Boolean));
            ManagedValue left, right;
            if (c.Left is Const && c.Right is not Const)
            {
                if (!Recover(c.Right, null).TryGet(out right, out failure)) return failure;
                if (!Recover(c.Left, right.Type).TryGet(out left, out failure)) return failure;
            }
            else
            {
                if (!Recover(c.Left, null).TryGet(out left, out failure)) return failure;
                if (!Recover(c.Right, left.Type).TryGet(out right, out failure)) return failure;
            }
            if (left is Fragment lf && !Pack(lf).TryGet(out left, out failure)) return failure;
            if (right is Fragment rf && !Pack(rf).TryGet(out right, out failure)) return failure;
            var reference = types.Kind(left.Type) == TypeKind.Reference || types.Kind(right.Type) == TypeKind.Reference;
            if (left.Type is GenericParameterRef { NativeScalar: not null } || right.Type is GenericParameterRef { NativeScalar: not null })
                return Fail(0, "泛型复制 不支持原生数值比较");
            if (reference)
            {
                if (c.Cond is not (Cond.Eq or Cond.Ne)) return Fail(0, $"比较 引用的 {c.Cond}");
                if (types.Kind(left.Type) != TypeKind.Reference && left is not ConstantValue { Bits: 0 } || types.Kind(right.Type) != TypeKind.Reference && right is not ConstantValue { Bits: 0 })
                    return Fail(0, "比较 引用与非引用");
            }
            else if (left.Width != right.Width) return Fail(0, "比较 位宽不一致");
            return new ComparisonValue(c.Cond, left, right, types.Boolean);
        }

        private RecoveryResult<ManagedValue> Conversion(Convert c, TypeRef? hint)
        {
            if (c.Kind == ConvKind.ZeroExtend && c.Operand is Use { Width: not (1 or 8 or 16 or 32 or 64) } narrow
                && Fold.ScalarExtract(new Extract(new Use(narrow.Variable, narrow.Variable.Width), 0, narrow.Width), c.Width) is { } extended)
                return Recover(extended, hint);
            if (c.Kind == ConvKind.ZeroExtend && c.Operand is Extract { Width: not (8 or 16 or 32 or 64) } extract
                && Fold.ScalarExtract(extract, c.Width) is { } scalar) return Recover(scalar, hint);
            if (!Recover(c.Operand, null).TryGet(out var operand, out var failure)) return failure;
            if (operand.Type is GenericParameterRef { NativeScalar: not null })
            {
                if (c.Kind is ConvKind.ZeroExtend or ConvKind.Truncate && c.Width >= types.Bits(operand.Type))
                    return new ConversionValue(c.Kind, operand, operand.Type, c.Width);
                return Fail(0, $"泛型复制 不支持 {c.Kind} 到 {c.Width} 位");
            }
            if (operand is Fragment f)
            {
                if (c.Kind == ConvKind.Truncate) return Slice(f, 0, c.Width);
                if (c.Kind == ConvKind.ZeroExtend) return ResizeFragment(f, c.Width);
                if (!Pack(f).TryGet(out operand, out failure)) return failure;
            }
            // 写入向量寄存器低位的值（S/D 读写清零高位）：只有低位是托管值，高位不属于任何叶子（如 HFA 实参的各片来自各自的 float 字段）。
            if (c.Kind == ConvKind.ZeroExtend && c.Width == 128 && (StructOrigin(c.Operand) || types.Kind(operand.Type) is TypeKind.Float or TypeKind.Double or TypeKind.Int or TypeKind.Bool))
                return ResizeFragment(new Fragment([new Part(0, operand)], types.UInt64, operand.Width), 128);
            switch (c.Kind)
            {
                case ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate:
                    if (operand.Width == c.Width) return operand;
                    // 栈溢出的浮点寄存器按位保存为整数，扩展/截断作用于位型，不能当作数值转换。
                    if (types.Kind(operand.Type) is TypeKind.Float or TypeKind.Double)
                        if (!Coerce(operand, types.Integer(operand.Width, false), 0).TryGet(out operand, out failure)) return failure;
                    if (types.Kind(operand.Type) is not (TypeKind.Int or TypeKind.Bool)) return Fail(0, $"转换 {c.Kind} 的操作数类型 {operand.Type}");
                    if (c.Width is not (8 or 16 or 32 or 64)) return Fail(0, $"转换 位宽 {c.Width}");
                    return operand.Width == c.Width ? operand
                        : new ConversionValue(c.Kind, operand, types.Integer(c.Width, c.Kind == ConvKind.SignExtend || c.Kind == ConvKind.Truncate && ManagedTypes.IsSigned(operand.Type)), c.Width);
                case ConvKind.SIntToFloat or ConvKind.UIntToFloat:
                    return new ConversionValue(c.Kind, operand, c.Width == 32 ? types.Single : types.Double, c.Width);
                case ConvKind.FloatToFloat:
                    return new ConversionValue(c.Kind, operand, c.Width == 32 ? types.Single : types.Double, c.Width);
                case ConvKind.FloatToSInt or ConvKind.FloatToUInt when c.Width is 32 or 64 && operand.Width is 32 or 64:
                    return new ConversionValue(c.Kind, operand, types.Integer(c.Width, c.Kind == ConvKind.FloatToSInt), c.Width);
                case ConvKind.Bitcast:
                    if (operand.Width != c.Width) return Fail(0, "转换 位重解释的宽度不一致");
                    var floatHint = hint is not null && types.Kind(hint) is TypeKind.Float or TypeKind.Double;
                    if (floatHint && operand.Type.Equals(hint)) return operand;
                    var toFloat = types.Kind(operand.Type) is TypeKind.Int or TypeKind.Bool ? true : false;
                    if (operand is ConstantValue k) return new ConstantValue(k.Bits, floatHint ? hint! : c.Width == 32 ? types.Single : types.Double, c.Width);
                    return new ConversionValue(c.Kind, operand, toFloat ? c.Width == 32 ? types.Single : types.Double : types.Integer(c.Width, false), c.Width);
                default:
                    return Fail(0, $"转换 {c.Kind} 尚未支持（浮点转整数的饱和语义）");
            }
        }

        // ---------- 方法体 ----------

        private RecoveryResult<ManagedBody> Build()
        {
            if (exceptionLayout is { Succeeded: true }) return BuildExceptionBody();
            var managedBlocks = new List<ManagedBlock>();
            foreach (var block in blocks)
            {
                var statements = new List<ManagedStatement>();
                RecoveryHole? terminatorHole = null;
                foreach (var statement in block.Statements)
                {
                    if (dropped.Contains(statement)) continue;
                    var failure = ledger.TryGetDiagnosis(statement, out var diagnosed) ? Derived(diagnosed, $"{diagnosed.Reason.Split(' ')[0]} 语句已诊断")
                        : Translate(block, statement, statements);
                    if (failure is { } e)
                    {
                        var cause = Record(e, statement.Address, statement);
                        var terminal = statement is Branch or Jump or Return or IndirectJump or Trap or Call { Kind: CallKind.Tail or CallKind.TailIndirect }
                            or Call { Op.Kind: OpKind.Throw or OpKind.ThrowNew or OpKind.Rethrow or OpKind.ResumeUnwind or OpKind.Terminate };
                        if (terminal) terminatorHole = cause;
                        // 部分方法体：洞留在原处，终结语句的洞结束本块。
                        statements.Add(new ManagedHole(statement.Address, e.Message, terminal));
                    }
                }
                if (statements.LastOrDefault() is not (ManagedReturn or ManagedJump or ManagedBranch or ManagedSwitch or ManagedThrow or ManagedCall { Tail: true } or ManagedHole { Terminal: true }))
                {
                    var successors = block.NormalSuccessors.ToArray();
                    if (successors.Length == 0 && statements.LastOrDefault() is ManagedCall { Result: null } noReturn
                        && ManagedTypes.IsVoid(noReturn.Invocation.Method.Method.ReturnType)
                        && block.Statements.LastOrDefault() is Call { Target: Const target } && owner.lifter.NoReturn.IsNoReturn(target.Value)
                        && ManagedTypes.IsVoid(returnType)) statements[^1] = noReturn with { Tail = true };
                    else if (successors.Length == 1)
                    {
                        if (Edge(block, 0, successors[0].Start).TryGet(out var edge, out var failure)) statements.Add(new ManagedJump(block.End, edge));
                        else { Record(failure, block.End); statements.Add(new ManagedHole(block.End, failure.Message, true)); }
                    }
                    else if (terminatorHole is { } cause) { Record(Derived(cause, "控制流 终结语句未恢复"), block.Start); statements.Add(new ManagedHole(block.End, "控制流 终结语句未恢复", true)); }
                    else { Hole(block.Start, "控制流 基本块没有唯一终结方式"); statements.Add(new ManagedHole(block.End, "控制流 基本块没有唯一终结方式", true)); }
                }
                // 循环入口前的空块没有原生指令；其标签必须与实际循环入口区分，回边仍指向原生地址。
                var label = block == function.EntryBlock && block.End == block.Start ? 0xf400000000000000UL : block.Start;
                managedBlocks.Add(new(label, statements));
            }
            return new ManagedBody(method, managedBlocks);
        }

        private RecoveryResult<LocalValue> Local(Variable v) => LocalOf(v);

        private RecoveryResult<ManagedEdge> Edge(Block from, int successor, ulong target)
        {
            var to = from.NormalSuccessors.ElementAtOrDefault(successor);
            if (to is null || to.Start != target) throw new InvalidOperationException($"CFG 中缺少第 {successor} 条边 {from.Start:x} → {target:x}");
            var incoming = MachineFunction.PredecessorIndex(from, successor);
            var copies = new List<ManagedCopy>();
            foreach (var group in structPhis.Where(g => g.Block == to)) copies.Add(new(group.Local, group.Incoming(incoming)));
            foreach (var phi in to.Statements.OfType<Phi>())
            {
                if (structPhiMembers.ContainsKey(phi.Target) || exceptionLayout is { Succeeded: true } && !exceptionDemand.Contains(phi.Target)
                    || runtime.Contains(phi.Target) || exceptionValues.ContainsKey(phi.Target)) continue;
                if (fragmentLocals.TryGetValue(phi.Target, out var fragmentTarget))
                {
                    if (!Variable(phi.Sources[incoming], fragmentTarget.Width).TryGet(out var fragmentSource, out var fragmentFailure)) return fragmentFailure;
                    foreach (var part in fragmentTarget.Parts)
                    {
                        if (!Slice(fragmentSource, part.Low, part.Value.Width).Bind(v => Coerce(v, part.Value.Type, phi.Address)).TryGet(out var value, out fragmentFailure)) return fragmentFailure;
                        copies.Add(new((LocalValue)part.Value, value));
                    }
                    continue;
                }
                if (!Local(phi.Target).TryGet(out var local, out var failure)) return failure;
                var source = phi.Sources[incoming];
                var attempt = Copy();
                if (attempt.TryGet(out var copied, out failure)) copies.Add(new(local, copied));
                else
                {
                    if (collectingExceptionDemand) return failure;
                    Record(failure, phi.Address);
                    copies.Add(new(local, new HoleValue(failure.Message, local.Type, local.Width)));
                }
                RecoveryResult<ManagedValue> Copy()
                {
                    if (CheckPoison(source) is { } poison) return poison;
                    if (source.Version == 0 && !arguments.ContainsKey(source.Storage)) return Fail(phi.Address, $"汇合 未定义的来源 {source}");
                    RecoveryResult<ManagedValue> read = values.TryGetValue(source, out var c) && c is Const constant
                        ? new ConstantValue(constant.Value & Expr.Mask(local.Width), local.Type, local.Width) : Variable(source, local.Width);
                    if (!read.TryGet(out var value, out var error)) return error;
                    if (value is Fragment fragment && !Pack(fragment).TryGet(out value, out error)) return error;
                    if (value.Width != local.Width) return Fail(phi.Address, $"汇合 来源 {source} 的位宽与 φ 不一致");
                    return types.Kind(local.Type) == TypeKind.Reference ? Coerce(value, local.Type, phi.Address) : value;
                }
            }
            return new ManagedEdge(target, copies);
        }

        private static RecoveryFailure? Rules(IEnumerable<RecoveryResult<bool>> candidates, out bool handled)
        {
            handled = false;
            foreach (var candidate in candidates)
            {
                if (!candidate.TryGet(out handled, out var failure)) return failure;
                if (handled) break;
            }
            return null;
        }

        private static RecoveryResult<T?> FirstValue<T>(IEnumerable<RecoveryResult<T?>> candidates) where T : class
        {
            foreach (var candidate in candidates)
            {
                if (!candidate.TryGet(out var value, out var failure)) return failure;
                if (value is not null) return value;
            }
            return (T?)null;
        }

        private static RecoveryFailure? Emit<T>(RecoveryResult<T> result, List<ManagedStatement> output) where T : ManagedStatement
        {
            if (!result.TryGet(out var statement, out var failure)) return failure;
            output.Add(statement);
            return null;
        }

        private RecoveryFailure? Assign(ulong address, Variable target, Func<RecoveryResult<ManagedValue>> value, List<ManagedStatement> output) =>
            Emit(Local(target).Bind(local => value().Map(v => new ManagedAssignment(address, local, v))), output);

        private RecoveryFailure? Translate(Block block, Stmt statement, List<ManagedStatement> output)
        {
            if (Rules(Registry.Statements.Select(rule => rule(this, block, statement, output)), out var handled) is { } ruleFailure) return ruleFailure;
            if (handled) return null;
            switch (statement)
            {
                case Define define:
                {
                    if (objectClasses.TryGetValue(define.Target, out var obj))
                        return Emit(Recover(obj, types.Object).Bind(value => Check(define.Address,
                            new ComparisonValue(Cond.Eq, value, new ConstantValue(0, types.Object, 64), types.Boolean), "System.NullReferenceException")), output);
                    if (runtime.Contains(define.Target) || inlined.Contains(define.Target)) return null;
                    if (Rules(Registry.Defines.Select(rule => rule(this, define, output)), out handled) is { } failed) return failed;
                    if (handled) return null;
                    if (!Local(define.Target).TryGet(out var local, out var failure)) return failure;
                    if (!Recover(define.Value, local.Type).TryGet(out var value, out failure)) return failure;
                    if ((value.Width != local.Width || value is Fragment) && !Coerce(value, local.Type, define.Address).TryGet(out value, out failure)) return failure;
                    output.Add(new ManagedAssignment(define.Address, local, value));
                    return null;
                }
                case Phi or Nop: return null;
                case Store store:
                {
                    if (Rules(Registry.Stores.Select(rule => rule(this, store, output)), out handled) is { } failed) return failed;
                    if (handled) return null;
                    if (!Location(store.Target, store.Value.Width).TryGet(out var target, out var failure)) return failure;
                    if (Rules(Registry.StoreTargets.Select(rule => rule(this, store, target, output)), out handled) is { } rejected) return rejected;
                    if (handled) return null;
                    return Emit(RecoverAs(store.Value, target.Type, store.Address).Map(value => new ManagedStore(store.Address, target, value)), output);
                }
                case Call call: return TranslateCall(call, output);
                case Branch branch:
                    return Emit(Recover(branch.Condition, types.Boolean).Bind(Truth).Bind(condition => Edge(block, 0, branch.Target)
                        .Bind(taken => Edge(block, 1, branch.Fallthrough).Map(fallthrough => new ManagedBranch(branch.Address, condition, taken, fallthrough)))), output);
                case Jump jump: return Emit(Edge(block, 0, jump.Target).Map(edge => new ManagedJump(jump.Address, edge)), output);
                case Return ret:
                    if (returnHole is { } cause) return Derived(cause, "返回 返回值类型尚未支持");
                    if (ManagedTypes.IsVoid(returnType)) { output.Add(new ManagedReturn(ret.Address, null)); return null; }
                    if (ownReturnBuffer is not null) { output.Add(new ManagedReturn(ret.Address, ownReturnBuffer)); return null; }
                    if (ret.Value is not { } returned) return Fail(ret.Address, "返回 非 void 方法缺少返回值");
                    return Emit((types.Kind(returnType) == TypeKind.Struct ? StructReturn(returned)
                        : RecoverAs(returned, returnType, ret.Address)).Map(value => new ManagedReturn(ret.Address, value)), output);
                default: return Fail(statement.Address, $"语句 {statement.GetType().Name} 尚未支持");
            }
        }

        private RecoveryFailure? TranslateCall(Call call, List<ManagedStatement> output)
        {
            if (Rules(Registry.Calls.Select(rule => rule(this, call, output)), out var handled) is { } ruleFailure) return ruleFailure;
            if (handled) return null;
            var address = call.Address;
            var ignored = IsWriteBarrier(call) || call.Op?.Kind is OpKind.InitClass or OpKind.InitMethodRgctx or OpKind.InterfaceInvokeData || genericResolvers.Contains(call);
            if (ignored)
            {
                if (call.Kind == CallKind.Tail)
                {
                    if (!ManagedTypes.IsVoid(returnType)) return Fail(address, "返回 尾调用写屏障的方法不是 void");
                    output.Add(new ManagedReturn(address, null));
                }
                return null;
            }
            switch (call.Op)
            {
                case { Kind: OpKind.CompareExchangeReference }: return CompareExchangeReference(call, output);
                case { Kind: OpKind.RunClassConstructor, Operand: TypeRef type }:
                    if (owner.runClassConstructor is not { } run) return Fail(address, "类初始化 核心库缺少 RuntimeHelpers.RunClassConstructor");
                    output.Add(new ManagedCall(address, new ManagedInvocation(run, null, [new TypeHandleValue(type, types.RuntimeTypeHandle, types.Size(types.RuntimeTypeHandle) * 8)], false), null, false));
                    return null;
                case { Kind: OpKind.MemoryBarrier }:
                    if (owner.memoryBarrier is not { } barrier) return Fail(address, "运行时操作 核心库缺少 Thread.MemoryBarrier");
                    output.Add(new ManagedCall(address, new ManagedInvocation(barrier, null, [], false), null, false));
                    return null;
                case { Kind: OpKind.NullCheck }:
                {
                    if (!Recover(call.Arguments[0], types.Object).TryGet(out var operand, out var failure)) return failure;
                    var zeroType = call.Arguments[0] is Use u && results.TryGetValue(u.Variable, out var checkedResult) && typeChecks.ContainsKey(checkedResult.Call) ? operand.Type : types.Object;
                    return Emit(Check(address, new ComparisonValue(Cond.Eq, operand, new ConstantValue(0, zeroType, 64), types.Boolean), "System.NullReferenceException"), output);
                }
                case { Kind: OpKind.BoundsCheck } when call.Arguments is [var index, var length]:
                    return Emit(Recover(index, types.Int32).Bind(i => Recover(length, i.Type).Bind(value => Coerce(value, i.Type, address))
                        .Bind(n => Check(address, new ComparisonValue(Cond.Uge, i, n, types.Boolean), "System.IndexOutOfRangeException"))), output);
                case { Kind: OpKind.ThrowIf, Operand: string exception }:
                    return Emit(Recover(call.Arguments[0], types.Boolean).Bind(Truth).Bind(condition => Check(address, condition, exception)), output);
                case { Kind: OpKind.ThrowNew, Operand: string exception }:
                    if (owner.ExceptionConstructor(exception) is not { } throwConstructor) return Fail(address, $"异常 {exception} 没有无参构造函数");
                    output.Add(new ManagedThrow(address, new NewObjectValue(throwConstructor, [])));
                    return null;
                case { Kind: OpKind.NewException, Operand: string exception } when call.Defines.FirstOrDefault() is { } created:
                    return Assign(address, created, () => owner.ExceptionConstructor(exception) is { } constructor
                        ? new NewObjectValue(constructor, []) : Fail(address, $"异常 {exception} 没有无参构造函数"), output);
                case { Kind: OpKind.Throw or OpKind.ThrowManaged or OpKind.Rethrow }:
                    return Emit(Recover(call.Arguments[0], null).Map(value => new ManagedThrow(address, value)), output);
                case { Kind: OpKind.NewObject } when inlineConstructors.TryGetValue(call, out var constructor):
                {
                    var arguments = new List<ManagedValue>();
                    foreach (var (argument, i) in constructor.Arguments.Select((v, i) => (v, i)))
                    {
                        if (!RecoverAs(argument, Concrete(constructor.Method, constructor.Method.Method.Parameters[i].Type), address).TryGet(out var value, out var failure)) return failure;
                        arguments.Add(value);
                    }
                    return Assign(address, call.Defines[0], () => new NewObjectValue(constructor.Method, arguments) { Transparent = true }, output);
                }
                case { Kind: OpKind.NewArray, Operand: ArrayRef array }:
                {
                    if (!Index(call.Arguments[1]).TryGet(out var length, out var failure)) return failure;
                    var value = new NewArrayValue(array, length);
                    if (call.Kind == CallKind.Tail) return Emit(Coerce(value, returnType, address).Map(result => new ManagedReturn(address, result)), output);
                    if (call.Defines.FirstOrDefault() is { } createdArray) return Assign(address, createdArray, () => value, output);
                    output.Add(new ManagedAssignment(address, StructLocal(array, 64), value));
                    return null;
                }
                case { Kind: OpKind.Box, Operand: TypeRef type } when call.Defines.FirstOrDefault() is { } created && boxed.TryGetValue(call, out var content):
                    if (types.Kind(type) is not (TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double) || type is DefinitionRef { Definition.FullName: "System.Nullable" })
                        return Fail(address, $"装箱 类型 {type} 尚未支持");
                    return Assign(address, created, () => RecoverAs(content, type, address).Map<ManagedValue>(value => new BoxValue(value, type, types.Object)), output);
                case { Kind: OpKind.TypeCheck, Operand: TypeRef type } when typeChecks.TryGetValue(call, out var obj) && call.Defines.FirstOrDefault() is { } checkedValue:
                    return Assign(address, checkedValue, () => RecoverAs(obj, types.Object, address).Bind(value => Coerce(new ComparisonValue(Cond.Ne,
                        new IsInstValue(value, type), new ConstantValue(0, type, 64), types.Boolean), types.UInt64, address)), output);
                case { Kind: OpKind.Unbox, Operand: TypeRef type } when (type is DefinitionRef { Definition.IsEnum: true } or GenericParameterRef { NativeScalar: not null }) && call.Defines.FirstOrDefault() is { } created:
                    return Assign(address, created, () => RecoverAs(call.Arguments[0], types.Object, address).Map<ManagedValue>(value => new UnboxAddressValue(value, type)), output);
                case { Kind: OpKind.IsInst, Operand: TypeRef type } when call.Kind == CallKind.Tail || call.Defines.FirstOrDefault() is not null:
                {
                    if (!Recover(call.Arguments[0], types.Object).Bind(value => Coerce(value, types.Object, address)).TryGet(out var value, out var failure)) return failure;
                    var instance = new IsInstValue(value, type, type is GenericParameterRef { NativeScalar: not null } ? types.Object : null);
                    return call.Kind == CallKind.Tail ? Emit(Coerce(instance, returnType, address).Map(v => new ManagedReturn(address, v)), output)
                        : Assign(address, call.Defines[0], () => instance, output);
                }
                case { Kind: OpKind.IsInstArrayElement } when call.Defines.FirstOrDefault() is { } created: return ArrayElementCheck(call, created, output);
                case null or { Kind: OpKind.CallVirtual or OpKind.CallInterface or OpKind.CallDelegate or OpKind.CallGenericVirtual or OpKind.CallMethodPointer }:
                    return Invocation(call, output);
                default: return Fail(address, $"运行时操作 {call.Op?.Kind.ToString() ?? call.Kind.ToString()} 尚未支持");
            }
        }

        private RecoveryResult<ManagedCheck> Check(ulong address, ManagedValue condition, string exception) => owner.ExceptionConstructor(exception) is { } constructor
            ? new ManagedCheck(address, condition, constructor) : Fail(address, $"异常 {exception} 没有无参构造函数");

        private RecoveryFailure? Invocation(Call call, List<ManagedStatement> output)
        {
            var address = call.Address;
            if (Rules(Registry.Invocations.Select(rule => rule(this, call, output)), out var handled) is { } ruleFailure) return ruleFailure;
            if (handled) return null;
            if (call.Op is null && call.Target is Const target && facts.Code.RegionOf(target.Value) != CodeRegion.Managed)
                return Fail(address, $"调用 运行时函数 0x{target.Value:x}（{facts.Helpers.At(target.Value)?.Kind.ToString() ?? "未识别"}）");
            if (call.Op is null && call.Kind is not (CallKind.Direct or CallKind.Tail)) return Fail(address, "调用 来源未知的间接调用");
            if (Resolve(call) is not { } callee) return Fail(address, CallResolutionFailure(call));
            if (owner.abi.Classify(callee, out var problem) is not { } signature) return Fail(address, $"调用 {callee} 的签名: {problem}");
            if (call.Op?.Kind == OpKind.CallDelegate && signature.Return is { } delegateReturn
                && (delegateReturn.Passing != Passing.Registers || delegateReturn.Pieces.Length != 1 || types.Kind(delegateReturn.Type) is TypeKind.Struct or null
                    || types.Kind(delegateReturn.Type) == TypeKind.Pointer && !ManagedTypes.IsNativePointer(delegateReturn.Type)))
                return Fail(address, $"委托 Invoke 返回值 {delegateReturn.Type} 的 ABI 尚未支持");
            var registers = ArgumentsOf(call);
            RecoveryResult<Expr> Argument(AbiValue value, string name)
            {
                if (value.Passing != Passing.Registers || value.Pieces.Length != 1) return Fail(address, $"调用 {callee} 的参数 {name} 的传递方式尚未支持");
                if (!registers.TryGetValue(value.Pieces[0].Register, out var e)) return Fail(address, $"调用 {callee} 缺少参数 {name}");
                return types.Kind(value.Type) is TypeKind.Float or TypeKind.Double ? ScalarVectorNarrowing.Low(e, value.Pieces[0].Width) : e;
            }
            var definition = callee.Method;
            ManagedValue? receiver = null;
            if (signature.This is { } self)
            {
                if (stackEnums.TryGetValue(call, out var stackEnum))
                {
                    if (!RecoverAs(stackEnum.Value, stackEnum.Type, address).TryGet(out var value, out var failure)) return failure;
                    receiver = new BoxValue(value, stackEnum.Type, self.Type);
                }
                else
                {
                    RecoveryResult<Expr> argument = call.DelegateReceiver is { } delegateReceiver ? delegateReceiver : Argument(self, "this");
                    if (!argument.TryGet(out var expression, out var failure)) return failure;
                    if (!UnusedReceiver(call, callee, self, expression).TryGet(out receiver, out failure)) return failure;
                    if (receiver is null && !RecoverAs(expression, self.Type, address).TryGet(out receiver, out failure)) return failure;
                }
            }
            var parameters = new List<ManagedValue>();
            for (var i = 0; i < signature.Parameters.Length; i++)
            {
                var parameter = signature.Parameters[i];
                var site = new ArgumentSite(call, callee, definition.Parameters[i].Name, registers, Argument) { Index = i, Output = output };
                if (!FirstValue(Registry.Arguments.Select(rule => rule(this, parameter, site))).TryGet(out var shaped, out var failure)) return failure;
                if (shaped is not null) { parameters.Add(shaped); continue; }
                if (types.Kind(parameter.Type) is TypeKind.Struct or null || types.Kind(parameter.Type) == TypeKind.Pointer && !ManagedTypes.IsNativePointer(parameter.Type)
                    && (parameter.Type is not ByRefRef parameterReference || types.Kind(parameterReference.Element) is not (TypeKind.Struct or TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Reference)))
                    return Fail(address, $"调用 {callee} 的参数类型 {parameter.Type} 尚未支持");
                if (!Argument(parameter, definition.Parameters[i].Name).Bind(e => RecoverAs(e, parameter.Type, address)).TryGet(out var recovered, out failure)) return failure;
                parameters.Add(recovered);
            }
            var calledReturn = Concrete(callee, definition.ReturnType);
            if (constructed.TryGetValue(call, out var created))
            {
                var value = forwardedConstructors.TryGetValue(call, out var own)
                    ? new NewObjectValue(own with { TypeArguments = ((DefinitionRef)known[created]).Arguments }, []) { Transparent = true }
                    : new NewObjectValue(callee with { TypeArguments = ((DefinitionRef)known[created]).Arguments }, parameters);
                return Assign(address, created, () => value, output);
            }
            var copied = call.Op is null && call.Target is Const copyTarget && facts.EntriesAt(copyTarget.Value).Length == 0 && facts.Unregistered.At(copyTarget.Value) is null;
            var isVirtual = call.Op is not null || virtualCalls.Contains(call)
                || definition.IsVirtual && (definition.Attributes & System.Reflection.MethodAttributes.Final) != 0 && receiver is not ArgumentValue { Index: -1 };
            var invocation = new ManagedInvocation(callee, receiver, parameters, isVirtual && receiver is not null && receiver.Type is not ByRefRef);
            if (Rules(Registry.InvocationOutputs.Select(rule => rule(this, call, signature, registers, invocation, output)), out handled) is { } rejected) return rejected;
            if (handled) return null;
            if (call.Kind is CallKind.Tail or CallKind.TailIndirect)
            {
                if (ManagedTypes.IsVoid(returnType) && signature.Return is { Passing: Passing.Registers } discarded
                    && (RegisterStruct(discarded) || discarded.Pieces.Length == 1 && types.Kind(calledReturn) is TypeKind.Bool or TypeKind.Int or TypeKind.Float or TypeKind.Double or TypeKind.Reference))
                {
                    output.Add(new ManagedCall(address, invocation, null, false) { Inlined = copied });
                    output.Add(new ManagedReturn(address, null));
                    return null;
                }
                if (ManagedTypes.IsVoid(returnType) != ManagedTypes.IsVoid(calledReturn) || !ManagedTypes.IsVoid(returnType) && !calledReturn.Equals(returnType)
                    && !types.IsAssignable(calledReturn, returnType)) return Fail(address, $"尾调用 返回类型 {calledReturn} 与 {returnType} 不符");
                output.Add(new ManagedCall(address, invocation, null, true) { Inlined = copied });
                return null;
            }
            LocalValue? result = null;
            if (signature.Return is { } returned)
            {
                if (!FirstValue(Registry.Results.Select(rule => rule(this, call, returned))).TryGet(out result, out var failure)) return failure;
                if (result is null)
                {
                    var index = Array.IndexOf(call.Results, returned.Pieces[0].Register);
                    if (index >= 0 && index < call.Defines.Length && call.Defines[index] is { } defined && !runtime.Contains(defined)
                        && !Local(defined).TryGet(out result, out failure)) return failure;
                }
            }
            output.Add(new ManagedCall(address, invocation, result, false) { Inlined = copied });
            return null;
        }
    }
}
