using System.Collections.Immutable;

namespace Cpp2CS.Native;

// 数据流算法只依赖这些图关系，不把派生调用边伪装成原 MIR 后继。
public sealed record NativeAnalysisEdge(BlockId Target, ImmutableArray<NativeValue> Arguments);
public sealed record NativeAnalysisBlock(BlockId Id, ImmutableArray<BlockParameter> Parameters,
    ImmutableArray<NativeNode> Nodes, ImmutableArray<NativeAnalysisEdge> Edges);
