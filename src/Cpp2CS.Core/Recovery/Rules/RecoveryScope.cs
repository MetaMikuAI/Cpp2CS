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
    internal readonly List<PassStep> passSteps = [];
    private Cpp2CS.Machine.Algebra.PassList? passes;
    internal Cpp2CS.Machine.Algebra.PassList Passes => passes ??= new(function, passSteps, Rewriter);
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
    internal readonly List<AnalysisStep> analysisSteps = [];
    internal readonly List<RuleTrace> ruleTraces = [];
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
