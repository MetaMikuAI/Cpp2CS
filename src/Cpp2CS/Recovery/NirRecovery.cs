using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Cpp2CS.Native;
using Cpp2CS.Nir;

namespace Cpp2CS.Recovery;

public static class NirRecovery
{
    public static NirRecoveryResult Recover(ImageDocument image, IEnumerable<FunctionContract> contracts,
        NirRecoveryOptions? options = null) => Recover(new ImageSource(image), contracts, options);

    public static NirRecoveryResult Recover(IRegionInstructionSource source, IEnumerable<FunctionContract> contracts,
        NirRecoveryOptions? options = null)
    {
        options ??= new();
        if (options.MaxInstructions < 1 || options.MaxNormalizationRounds < 1)
            throw new ArgumentOutOfRangeException(nameof(options));
        var known = contracts.ToImmutableArray();
        if (known.Select(contract => contract.Name).Distinct(StringComparer.Ordinal).Count() != known.Length ||
            known.Select(contract => contract.EntryAddress).Distinct().Count() != known.Length)
            throw new ArgumentException("函数合同名称和入口必须唯一", nameof(contracts));
        var results = ImmutableArray.CreateBuilder<NirFunctionRecovery>();
        foreach (var contract in known)
        {
            var graph = FunctionGraphBuilder.Build(source, contract, known, options.GraphOptions ?? new(options.MaxInstructions));
            var diagnostics = graph.Gaps.Select(gap => new NirRecoveryDiagnostic(gap.Address, $"graph.{gap.Kind}", gap.Reason)).ToList();
            foreach (var block in graph.Blocks)
                if (block.Instruction?.Operations.Any(operation => operation.Code == OpCode.WriteSlot &&
                    operation.Slot is "fpcr" or "fpsr" or "mxcsr" or "tpidr_el0" or "fsbase" or "gsbase" or
                        "cs" or "es" or "ss" or "ds" or "fs" or "gs" or "apia_key" or "apib_key" or "pauth_ia_enabled" or "pauth_ib_enabled") == true)
                    diagnostics.Add(new(block.Address, "contract.unmodeled-environment",
                        "机器体修改了尚未投影的浮点或线程环境，不能按逻辑返回值不活跃而删除"));
            RecoveryMachineSsa? machine = null;
            NirEmitter? emitter = null;
            NirFunction? function = null;
            if (diagnostics.Count == 0)
            {
                machine = new(graph);
                if (!machine.Normalize(options.MaxNormalizationRounds))
                    diagnostics.Add(new(contract.EntryAddress, "budget.normalization", "机器 SSA 归约尚未达到固定点"));
                if (diagnostics.Count == 0)
                {
                    var frame = RecoveryFrameAnalysis.Run(machine, options);
                    diagnostics.AddRange(frame.Diagnostics);
                    if (diagnostics.Count == 0)
                    {
                        emitter = new(machine, frame, options);
                        function = emitter.Emit();
                        diagnostics.AddRange(emitter.Diagnostics);
                    }
                }
            }
            results.Add(new(graph, function, diagnostics.Distinct().ToImmutableArray(), machine?.Evidence.ToImmutableArray() ?? [],
                new(graph.Blocks.Length, machine?.ValueCount ?? 0, function?.Blocks.Length ?? 0,
                    function?.Blocks.Sum(block => block.Operations.Length) ?? 0, emitter?.EliminatedFrameAccesses ?? 0,
                    graph.Blocks.SelectMany(block => block.Edges).Count(edge => edge.Call is not null), machine?.Rounds ?? 0)));
        }
        var contradicted = results.Where(result => result.Diagnostics.Any(diagnostic => diagnostic.Code.StartsWith("contract.", StringComparison.Ordinal)))
            .Select(result => result.Graph.Contract.Name).ToHashSet(StringComparer.Ordinal);
        var changed = true;
        while (changed)
        {
            changed = false;
            for (var index = 0; index < results.Count; index++)
            {
                var result = results[index];
                var dependencies = result.Graph.Blocks.SelectMany(block => block.Edges).Where(edge => edge.Call is not null)
                    .Select(edge => edge.Call!.Callee.Name).Where(contradicted.Contains).Distinct().ToArray();
                if (dependencies.Length == 0 || contradicted.Contains(result.Graph.Contract.Name)) continue;
                contradicted.Add(result.Graph.Contract.Name);
                changed = true;
                results[index] = result with
                {
                    Function = null,
                    Diagnostics = result.Diagnostics.Add(new(result.Graph.Contract.EntryAddress, "contract.dependency",
                        "被调合同已被撤回，调用者不能继续使用其摘要: " + string.Join(", ", dependencies))),
                    Statistics = result.Statistics with { NirBlocks = 0, NirOperations = 0 }
                };
            }
        }
        var functions = results.Where(result => result.Complete).Select(result => result.Function!).ToImmutableArray();
        var emittedNames = functions.Select(function => function.Id).ToHashSet(StringComparer.Ordinal);
        var externals = known.Where(contract => !emittedNames.Contains(contract.Name) && !contradicted.Contains(contract.Name) && !contract.Effects.MayThrow &&
                MachineAbi.TryDescribe(contract, out _, out _)).Select(contract =>
                new NirExternalContract(contract.Name, Signature(contract.Signature), ExternalEffects(contract), Outcomes(contract))).ToImmutableArray();
        var module = new NirModule(functions, externals,
            [new("memory", 64, BigInteger.One << 48, BigInteger.One << 32)], []);
        var validation = NirValidator.Validate(module);
        if (!validation.IsValid) throw new InvalidDataException("恢复生成无效 NIR: " + string.Join("; ", validation.Diagnostics));
        return new(module, results.ToImmutable());
    }

    internal static NirType Type(RecoveryScalarType type) => type.Kind switch
    {
        RecoveryScalarKind.Integer => new NirBitsType(type.Width),
        RecoveryScalarKind.Address => new NirAddressType("memory", type.Width),
        _ => throw new ArgumentOutOfRangeException(nameof(type))
    };
    internal static NirSignature Signature(FunctionSignature signature) => new(
        signature.Arguments.Select(Type).ToImmutableArray(), signature.Result is { } result ? [Type(result)] : []);

    // 尚未证明终止性，且内存与被调函数可以失败；不从抽样执行删除这些出口。
    internal static NirOutcomes Outcomes(FunctionContract contract) => NirOutcomes.Fault | NirOutcomes.Diverge |
        (contract.Effects.MayReturn ? NirOutcomes.Return : NirOutcomes.None) |
        (contract.Effects.MayTerminate ? NirOutcomes.Terminate : NirOutcomes.None);
    private static NirExternalEffects ExternalEffects(FunctionContract contract) =>
        (contract.Effects.ReadsMemory ? NirExternalEffects.ReadMemory : NirExternalEffects.None) |
        (contract.Effects.WritesMemory ? NirExternalEffects.WriteMemory : NirExternalEffects.None) |
        (contract.Effects.ExternalEffects ? NirExternalEffects.Environment : NirExternalEffects.None);

    private sealed class ImageSource(ImageDocument image) : IRegionInstructionSource
    {
        private readonly InstructionDecoder decoder = new(image);
        public string ImageId => image.Sha256;
        public Architecture Architecture => image.Architecture;
        public InstructionDecodeResult Decode(ulong address) => decoder.Decode(address);
    }
}
