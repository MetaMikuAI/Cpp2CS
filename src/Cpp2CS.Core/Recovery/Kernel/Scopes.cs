using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Algebra;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Ssa;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

/// <summary>
/// 分析作用域：分析步骤、只读的辅助函数、下降的值服务与证明经它读取方法会话。提供方法身份、事实与类型服务、
/// IR 的只读视图（块视图、定义、支配树）、证据表（过渡访问器 <see cref="State"/>，证据归位到各族后取消）、
/// 值服务、维护请求与洞账本；不提供 IR 编辑。机器函数对象仍可读到，写入由写许可在运行时拦截。
/// </summary>
internal class AnalysisScope
{
    internal AnalysisScope(MethodSession session) => Session = session;

    /// <summary>方法会话，只供内核使用。</summary>
    internal MethodSession Session { get; }

    internal MethodRecovery owner => Session.owner;
    internal MethodRef method => Session.method;
    internal ulong entry => Session.entry;
    internal bool ClosedInstance => Session.ClosedInstance;
    internal bool SharedDefinition => Session.SharedDefinition;
    internal bool ExpandThrowCalls => Session.ExpandThrowCalls;
    internal ManagedTypes types => Session.types;
    internal ProgramFacts facts => Session.facts;
    /// <summary>证据表的过渡访问器：证据归位到各族之前经它访问。</summary>
    internal MethodState State => Session.State;
    internal ValueRecoveryService Values => Session.Values;
    internal LoweringScope Lowering => Session.Lowering;
    internal HoleLedger ledger => Session.ledger;
    /// <summary>内核的残余压制命令。</summary>
    internal ResidualSuppression Residuals => Session.Residuals;
    internal Maintenance Maintain => Session.Maintain;
    internal IReadOnlyList<Block> blocks => Session.blocks;
    internal MachineFunction function => Session.function;
    internal Dominators Dominators => Session.Dominators;
    internal IReadOnlyDictionary<Variable, Expr> values => Session.values;
    internal IReadOnlyDictionary<Variable, Phi> phis => Session.phis;
    internal IReadOnlyDictionary<Variable, (Call Call, int Index)> results => Session.results;
    internal IReadOnlyDictionary<Variable, IReadOnlyList<Phi>> phiUses => Session.phiUses;
    /// <summary>方法分析的版本（快照变化的刷新时递增），调用解析缓存以它为键。</summary>
    internal int AnalysisVersion => Session.analyses.Version;
    /// <summary>参数绑定规则的作用域（签名绑定调用参数绑定规则时取用）。</summary>
    internal BindingScope Binding => Session.Binding;
    internal void TraceRule(Cpp2CS.Diagnostics.RuleTrace rule) => Session.TraceRule(rule);
}

/// <summary>改写作用域：改写步骤、Prepare 步骤与它们的辅助函数使用；在分析作用域之外提供语句改写器与 IR 编辑。</summary>
internal class RewriteScope : AnalysisScope
{
    internal RewriteScope(MethodSession session) : base(session) { }

    internal MachineEditor Rewriter => Session.Rewriter;
    internal Editing Edit => Session.Edit;
}

/// <summary>参数绑定作用域：入口参数的绑定规则使用。</summary>
internal sealed class BindingScope : AnalysisScope
{
    internal BindingScope(MethodSession session) : base(session) { }
}

/// <summary>证明作用域：方法体证明使用。</summary>
internal sealed class ProofScope : AnalysisScope
{
    internal ProofScope(MethodSession session) : base(session) { }
}
