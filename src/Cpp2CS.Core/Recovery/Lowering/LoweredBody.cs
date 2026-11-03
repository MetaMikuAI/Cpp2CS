using Cpp2CS.Ir;
using Cpp2CS.Recovery.Inlining;

namespace Cpp2CS.Recovery.Lowering;

/// <summary>机器下降产物。待证构造和局部分配边界随方法体交给模板阶段。</summary>
internal sealed record LoweredBody(ManagedBody? Body, IReadOnlyList<RecoveryHole> Holes,
    IReadOnlyDictionary<Variable, PendingConstruction> Constructions, int NextLocal);
