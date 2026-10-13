using System.Collections.Immutable;

namespace Cpp2CS.Recovery;

// 全入口分析共享合同身份及调用摘要，避免每个函数重复建立完整索引。
public sealed class FunctionContractIndex
{
    private readonly ImmutableDictionary<ulong, FunctionContract> contracts;
    private readonly Dictionary<ulong, string> dependencies = [];
    private readonly Dictionary<ulong, MachineCallSummary> summaries = [];
    public IEnumerable<FunctionContract> Contracts => contracts.Values;
    public int Count => contracts.Count;

    public FunctionContractIndex(IEnumerable<FunctionContract> input)
    {
        var entries = new Dictionary<ulong, FunctionContract>();
        var names = new Dictionary<string, ulong>(StringComparer.Ordinal);
        foreach (var contract in input)
        {
            var dependency = FunctionGraphBuilder.ContractDependency(contract);
            if (dependencies.TryGetValue(contract.EntryAddress, out var prior) && prior != dependency)
                throw new ArgumentException($"同一入口具有冲突的函数合同: 0x{contract.EntryAddress:X}", nameof(input));
            if (names.TryGetValue(contract.Name, out var address) && address != contract.EntryAddress)
                throw new ArgumentException($"函数合同名称重复: {contract.Name}", nameof(input));
            entries[contract.EntryAddress] = contract;
            names[contract.Name] = contract.EntryAddress;
            dependencies[contract.EntryAddress] = dependency;
        }
        contracts = entries.ToImmutableDictionary();
    }

    public bool TryGetValue(ulong address, out FunctionContract contract) => contracts.TryGetValue(address, out contract!);
    public string Dependency(FunctionContract contract)
    {
        if (!contracts.TryGetValue(contract.EntryAddress, out var indexed) ||
            !ReferenceEquals(indexed, contract) && dependencies[contract.EntryAddress] != FunctionGraphBuilder.ContractDependency(contract))
            throw new ArgumentException("函数不属于当前合同索引", nameof(contract));
        return dependencies[contract.EntryAddress];
    }
    public MachineCallSummary Summary(FunctionContract contract)
    {
        _ = Dependency(contract);
        if (summaries.TryGetValue(contract.EntryAddress, out var summary)) return summary;
        summary = MachineAbi.CreateSummary(contract);
        summaries.Add(contract.EntryAddress, summary);
        return summary;
    }
}
