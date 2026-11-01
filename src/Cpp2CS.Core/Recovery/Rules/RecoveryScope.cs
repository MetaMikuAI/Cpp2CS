using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Recovery;

internal sealed class RecoveryScope(MethodRecovery owner, MethodRef method, ulong entry)
{
    internal readonly MethodRecovery owner = owner;
    internal readonly MethodRef method = method;
    internal readonly ulong entry = entry;
    internal readonly MethodState State = new();
    private LoweringScope? lowering;
    internal LoweringScope Lowering => lowering ??= new(this);
    private ValueRecoveryService? valueService;
    internal ValueRecoveryService Values => valueService ??= new(this);
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
    internal HoleLedger ledger => this.ledgerStore ??= new(this.DefinedBy);

    /// <summary>定义索引（<see cref = "Definitions"/>）；帧改写之后重建。</summary>
    internal Definitions definitions = Definitions.Empty;
    internal readonly MethodAnalyses analyses = new();
    private readonly DominanceCache dominance = new();
    internal Dominators Dominators => dominance.Get(function);
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
