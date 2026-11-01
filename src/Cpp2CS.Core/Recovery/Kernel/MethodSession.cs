using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Recovery;

/// <summary>
/// 方法会话：一个方法恢复期间的全部状态（机器函数与 IR 视图、证据表、分析缓存、洞账本、追踪），只对内核可见。
/// 规则经 <see cref="Analysis"/>、<see cref="Rewrite"/>、<see cref="Binding"/>、<see cref="Proof"/> 等作用域访问它。
/// </summary>
internal sealed class MethodSession(MethodRecovery owner, MethodRef method, ulong entry)
{
    internal readonly MethodRecovery owner = owner;
    internal readonly MethodRef method = method;
    internal readonly ulong entry = entry;
    internal readonly MethodState State = new();
    private AnalysisScope? analysisScope;
    private RewriteScope? rewriteScope;
    private BindingScope? bindingScope;
    private ProofScope? proofScope;
    /// <summary>交给规则的作用域：分析（只读）、改写、参数绑定与证明。</summary>
    internal AnalysisScope Analysis => analysisScope ??= new(this);
    internal RewriteScope Rewrite => rewriteScope ??= new(this);
    internal BindingScope Binding => bindingScope ??= new(this);
    internal ProofScope Proof => proofScope ??= new(this);
    private LoweringScope? lowering;
    internal LoweringScope Lowering => lowering ??= new(Analysis);
    private ValueRecoveryService? valueService;
    internal ValueRecoveryService Values => valueService ??= new(Analysis);
    /// <summary>Prepare 步骤列表写入的 pass 记录；计划表在每步之后把它转入 <see cref="trace"/>。</summary>
    internal readonly List<PassStep> passSteps = [];
    private Cpp2CS.Machine.Algebra.PassList? passes;
    internal Cpp2CS.Machine.Algebra.PassList Passes => passes ??= new(function, passSteps, Rewriter, name => currentStep = name);
    /// <summary>方法的追踪（按完成先后）与当前步骤名（Prepare 条目、Analyze 步骤或子步骤），只用于诊断。</summary>
    internal readonly List<TraceEntry> trace = [];
    internal string currentStep = "prepare";
    /// <summary>记录一条规则追踪。</summary>
    internal void TraceRule(RuleTrace rule) => trace.Add(new(TraceKind.Rule, rule.Rule, currentStep) { Rule = rule });
    private Maintenance? maintenance;
    /// <summary>维护动作的内核接口。</summary>
    internal Maintenance Maintain => maintenance ??= new(this);
    private Editing? editing;
    /// <summary>IR 级维护动作的内核接口。</summary>
    internal Editing Edit => editing ??= new(this, Maintain);
    private StatementRewriter? statementRewriter;
    internal StatementRewriter Rewriter => statementRewriter ??= new(State.StatementTables, ledger.Replace);
    internal readonly ManagedTypes types = owner.types;
    internal readonly ProgramFacts facts = owner.facts;
    internal HoleLedger? ledgerStore;
    /// <summary>洞账本（<see cref = "HoleLedger"/>）：独立洞、毒化、依赖边与已诊断的语句。</summary>
    internal HoleLedger ledger => this.ledgerStore ??= new(Analysis.DefinedBy);

    /// <summary>定义索引（<see cref = "Definitions"/>）；帧改写之后重建。</summary>
    internal Definitions definitions = Definitions.Empty;
    internal readonly MethodAnalyses analyses = new();
    private readonly DominanceCache dominance = new();
    internal Dominators Dominators => dominance.Get(function);

    /// <summary>重建定义索引：一次快照刷新（快照变化时版本递增），返回当前的定义。</summary>
    internal Definitions IndexDefinitions()
    {
        analyses.Refresh(blocks, State.Exceptions.exceptionPhis);
        return analyses.Get(Definitions.Analysis);
    }
    internal IReadOnlyDictionary<Variable, Expr> values => this.definitions.Values;
    internal IReadOnlyDictionary<Variable, Phi> phis => this.definitions.Phis;
    internal IReadOnlyDictionary<Variable, (Call Call, int Index)> results => this.definitions.Results;
    internal IReadOnlyDictionary<Variable, IReadOnlyList<Phi>> phiUses => this.definitions.PhiUses;

    internal IReadOnlyList<Block> blocks = null!;
    internal MachineFunction function = null!;
    // ---------- 准备：签名、提升、L2 ----------
    /// <summary>允许具体实参或已有引用布局见证的泛型实例（RecoverInstance）。</summary>
    public bool ClosedInstance { get; init; }
    public bool SharedDefinition { get; init; }
    public bool ExpandThrowCalls { get; init; } = true;
}
