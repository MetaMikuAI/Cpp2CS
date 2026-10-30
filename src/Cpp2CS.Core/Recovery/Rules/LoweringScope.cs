using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Facts;

namespace Cpp2CS.Recovery;

/// <summary>下降规则只读分析证据，通过值服务生成托管值与语句。</summary>
internal sealed class LoweringScope
{
    public LoweringScope(RecoveryScope host) { State = new(host.State); Values = host.Values; this.host = host; }
    private readonly RecoveryScope host;
    public RecoveryEvidence State { get; }
    public ValueRecoveryService Values { get; }
    public ProgramFacts facts => host.facts;
    public ManagedTypes types => host.types;
    public bool ExpandThrowCalls => host.ExpandThrowCalls;
    public MethodRef method => host.method;
    public IReadOnlyDictionary<Variable, (Call Call, int Index)> results => host.results;
    public IReadOnlyDictionary<Variable, Expr> values => host.values;
    public IReadOnlyDictionary<Variable, Phi> phis => host.phis;
    public IReadOnlyList<Block> blocks => host.blocks;
}
