using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Cpp2CS.Native;

namespace Cpp2CS.Recovery;

public static class FunctionGraphBuilder
{
    public const string Version = "derived-function-graph/2";

    public static DerivedFunctionGraph Build(ImageDocument image, FunctionContract function,
        IEnumerable<FunctionContract> contracts, FunctionGraphOptions? options = null) =>
        Build(new ImageSource(image), function, contracts, options);

    public static DerivedFunctionGraph Build(IRegionInstructionSource source, FunctionContract function,
        IEnumerable<FunctionContract> contracts, FunctionGraphOptions? options = null) =>
        Build(source, function, new FunctionContractIndex(contracts.Append(function)), options);

    public static DerivedFunctionGraph Build(IRegionInstructionSource source, FunctionContract function,
        FunctionContractIndex known, FunctionGraphOptions? options = null)
    {
        options ??= new();
        if (options.MaxInstructions < 1) throw new ArgumentOutOfRangeException(nameof(options));
        if (!Enum.IsDefined(source.Architecture) || string.IsNullOrWhiteSpace(source.ImageId))
            throw new ArgumentException("函数图缺少机器来源", nameof(source));
        var dependencies = new HashSet<string>(StringComparer.Ordinal)
        {
            Version, MachineAbi.Version, MirJson.SemanticsVersion, known.Dependency(function)
        };
        var blocks = new List<DerivedFunctionBlock>();
        var gaps = ImmutableArray.CreateBuilder<RecoveryGap>();
        var addresses = new Dictionary<ulong, int>();
        var pending = new Queue<(int Id, ulong Address)>();
        var nextEdge = 0;
        var attempts = 0;
        int Schedule(ulong address)
        {
            if (addresses.TryGetValue(address, out var found)) return found;
            var id = addresses.Count;
            addresses.Add(address, id);
            pending.Enqueue((id, address));
            return id;
        }
        RecoveryGap Gap(ulong address, RecoveryGapKind kind, string reason)
        {
            var gap = new RecoveryGap(address, kind, reason);
            gaps.Add(gap);
            return gap;
        }
        Schedule(function.EntryAddress);
        if (!MachineAbi.TryDescribe(function, out _, out var interfaceReason) || MachineAbi.ArchitectureFor(function.Abi) != source.Architecture)
        {
            blocks.Add(new(0, function.EntryAddress, null, [], Gap(function.EntryAddress,
                RecoveryGapKind.UnsupportedInterface, interfaceReason ?? "函数 ABI 与机器来源不匹配")));
            pending.Clear();
        }
        while (pending.TryDequeue(out var item))
        {
            if (attempts == options.MaxInstructions)
            {
                blocks.Add(new(item.Id, item.Address, null, [], Gap(item.Address, RecoveryGapKind.Budget, "函数发现指令预算耗尽")));
                continue;
            }
            attempts++;
            var decoded = source.Decode(item.Address);
            if (decoded.Instruction is not { } instruction)
            {
                if (decoded.Failure is null || string.IsNullOrWhiteSpace(decoded.Reason))
                    throw new InvalidDataException("解码失败缺少原因");
                blocks.Add(new(item.Id, item.Address, null, [], Gap(item.Address, RecoveryGapKind.Decode,
                    $"{decoded.Failure}: {decoded.Reason}")));
                continue;
            }
            if (decoded.Failure is not null || decoded.Reason is not null || instruction.Architecture != source.Architecture ||
                instruction.Origin.ImageId != source.ImageId || instruction.Origin.Address != item.Address)
                throw new InvalidDataException("函数发现得到不一致的机器指令来源");
            var successors = MirInspection.Describe(instruction).Successors;
            var edges = ImmutableArray.CreateBuilder<DerivedFunctionEdge>();
            foreach (var successor in successors)
            {
                var edgeId = nextEdge++;
                var target = RegionBuilder.DirectAddress(instruction, successor);
                if (successor.TransferHint == TransferHint.Return)
                {
                    edges.Add(new(edgeId, item.Id, successor, DerivedEdgeKind.Return, null, target, null, null, null));
                    continue;
                }
                if (successor.TransferHint == TransferHint.Call)
                {
                    if (target is null && options.IndirectCallTargets?.TryGetValue(item.Address, out var boundTarget) == true)
                    {
                        target = boundTarget;
                        dependencies.Add($"adopted-call-target:0x{item.Address:X}:0x{boundTarget:X}");
                    }
                    if (target is null)
                    {
                        Missing(RecoveryGapKind.UnknownCallTarget, "间接调用目标尚无合同绑定");
                        continue;
                    }
                    if (!known.TryGetValue(target.Value, out var callee))
                    {
                        Missing(RecoveryGapKind.MissingCallContract, "被调入口没有已知逻辑签名与 ABI 合同");
                        continue;
                    }
                    if (!Compatible(callee, out var reason))
                    {
                        Missing(RecoveryGapKind.UnsupportedInterface, reason!);
                        continue;
                    }
                    dependencies.Add(known.Dependency(callee));
                    var continuation = callee.Effects.MayReturn
                        ? (ulong?)checked(instruction.Origin.Address + (ulong)instruction.Origin.Bytes.Length) : null;
                    edges.Add(new(edgeId, item.Id, successor, DerivedEdgeKind.Call,
                        continuation is { } next ? Schedule(next) : null, target,
                        known.Summary(callee), continuation, null));
                    continue;
                }
                if (successor.Kind == SuccessorKind.ExceptionBoundary)
                {
                    edges.Add(new(edgeId, item.Id, successor, DerivedEdgeKind.Exception, null, null, null, null,
                        Gap(item.Address, RecoveryGapKind.UnmodeledException, "机器异常边界尚无逻辑异常合同")));
                    continue;
                }
                if (target is null)
                {
                    Missing(RecoveryGapKind.UnknownJumpTarget, "间接转移尚未恢复为分派、返回或尾调用");
                    continue;
                }
                string? tailEvidence = null;
                var hasTailEvidence = options.TailCallEvidence?.TryGetValue(item.Address, out tailEvidence) == true &&
                    !string.IsNullOrWhiteSpace(tailEvidence);
                if (known.TryGetValue(target.Value, out var tailCallee) &&
                    (target != function.EntryAddress || hasTailEvidence))
                {
                    var candidate = !hasTailEvidence && options.InferTailCallCandidates && target != function.EntryAddress;
                    if ((!hasTailEvidence && !candidate) || successor.Kind != SuccessorKind.Jump)
                    {
                        Missing(RecoveryGapKind.UnclassifiedTailCall, "转移进入另一函数合同入口；缺少栈、保存状态和返回协议的尾调用证据");
                        continue;
                    }
                    if (!Compatible(tailCallee, out var reason) || tailCallee.Signature.Result != function.Signature.Result)
                    {
                        Missing(RecoveryGapKind.UnsupportedInterface, reason ?? "尾调用结果接口与当前函数不一致");
                        continue;
                    }
                    dependencies.Add(known.Dependency(tailCallee));
                    dependencies.Add(candidate ? $"tail-call-candidate:0x{item.Address:X}:0x{target:X}"
                        : $"adopted-tail-call:0x{item.Address:X}:{tailEvidence}");
                    edges.Add(new(edgeId, item.Id, successor, DerivedEdgeKind.TailCall, null, target,
                        known.Summary(tailCallee), null, null, candidate));
                    continue;
                }
                edges.Add(new(edgeId, item.Id, successor, DerivedEdgeKind.Direct, Schedule(target.Value), target, null, null, null));

                void Missing(RecoveryGapKind kind, string reason) => edges.Add(new(edgeId, item.Id, successor,
                    DerivedEdgeKind.Gap, null, target, null, null, Gap(item.Address, kind, reason)));
            }
            blocks.Add(new(item.Id, item.Address, instruction, edges.ToImmutable(), null));
        }
        var graph = new DerivedFunctionGraph(Guid.NewGuid().ToString("N"), source.ImageId, source.Architecture,
            function, blocks.OrderBy(block => block.Id).ToImmutableArray(), gaps.ToImmutable(),
            dependencies.Order(StringComparer.Ordinal).ToImmutableArray());
        var errors = DerivedGraphValidator.Validate(graph);
        if (errors.Count != 0) throw new InvalidDataException(string.Join("; ", errors));
        return graph;

        bool Compatible(FunctionContract contract, out string? reason)
        {
            if (!MachineAbi.TryDescribe(contract, out _, out reason)) return false;
            if (contract.Abi == function.Abi) return true;
            reason = "跨 ABI 调用需要显式适配合同";
            return false;
        }
    }

    public static string ContractDependency(FunctionContract contract) =>
        $"contract:0x{contract.EntryAddress:X}:" + Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(JsonSerializer.Serialize(contract))));

    private sealed class ImageSource(ImageDocument image) : IRegionInstructionSource
    {
        private readonly InstructionDecoder decoder = new(image);
        public string ImageId => image.Sha256;
        public Architecture Architecture => image.Architecture;
        public InstructionDecodeResult Decode(ulong address) => decoder.Decode(address);
    }
}
