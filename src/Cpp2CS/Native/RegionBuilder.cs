using System.Collections.Immutable;
using Cpp2CS.Images;
using Cpp2CS.Ir;

namespace Cpp2CS.Native;

public static class RegionBuilder
{
    public static RegionRevision Build(ImageDocument image, IEnumerable<EntrySeed> seeds, int maxInstructions = 10_000) =>
        Build(new ImageSource(image), seeds, maxInstructions);

    public static RegionRevision FromInstructions(Architecture architecture, string imageId,
        IEnumerable<MirInstruction> instructions, IEnumerable<EntrySeed> seeds, int maxInstructions = 10_000) =>
        Build(new InstructionSource(architecture, imageId, instructions), seeds, maxInstructions);

    public static RegionRevision Build(IRegionInstructionSource source, IEnumerable<EntrySeed> seeds, int maxInstructions = 10_000)
    {
        if (maxInstructions < 0) throw new ArgumentOutOfRangeException(nameof(maxInstructions));
        if (!Enum.IsDefined(source.Architecture) || string.IsNullOrWhiteSpace(source.ImageId))
            throw new ArgumentException("Region 来源缺少架构或映像身份", nameof(source));
        var addresses = new Dictionary<ulong, BlockId>();
        var pending = new Queue<(BlockId Id, ulong Address)>();
        var blocks = new List<RegionBlock>();
        BlockId Schedule(ulong address)
        {
            if (addresses.TryGetValue(address, out var existing)) return existing;
            var id = new BlockId(addresses.Count);
            addresses.Add(address, id);
            pending.Enqueue((id, address));
            return id;
        }
        var entries = seeds.Select(seed =>
        {
            if (seed is null || string.IsNullOrWhiteSpace(seed.Evidence)) throw new ArgumentException("入口必须保留证据", nameof(seeds));
            return new RegionEntry(seed, Schedule(seed.Address));
        }).ToImmutableArray();
        if (entries.Length == 0) throw new ArgumentException("Region 至少需要一个明确入口", nameof(seeds));
        var attempts = 0;
        var nextEdge = 0;
        while (pending.TryDequeue(out var item))
        {
            if (attempts == maxInstructions)
            {
                blocks.Add(new(item.Id, item.Address, null, new(RegionBoundaryKind.Budget, "指令解码预算已耗尽"), []));
                continue;
            }
            attempts++;
            var decoded = source.Decode(item.Address);
            if (decoded.Instruction is not { } ir)
            {
                if (decoded.Failure is not { } failure || !Enum.IsDefined(failure) || string.IsNullOrWhiteSpace(decoded.Reason))
                    throw new InvalidDataException("解码失败缺少明确的边界原因");
                blocks.Add(new(item.Id, item.Address, null, new(DecodeBoundary(failure), decoded.Reason), []));
                continue;
            }
            if (decoded.Failure is not null || decoded.Reason is not null || ir.Architecture != source.Architecture ||
                ir.Origin.ImageId != source.ImageId || ir.Origin.Address != item.Address)
                throw new InvalidDataException("已提升指令与 Region 来源不一致");
            var successors = MirInspection.Describe(ir).Successors;
            var edges = ImmutableArray.CreateBuilder<RegionEdge>(successors.Length);
            foreach (var successor in successors)
            {
                var boundary = TransferBoundary(successor);
                BlockId? target = null;
                if (boundary is null)
                {
                    if (DirectAddress(ir, successor) is { } address) target = Schedule(address);
                    else boundary = new(RegionBoundaryKind.IndirectTarget, "目标表达式尚未解析，保留原 MIR 转移");
                }
                edges.Add(new(new(nextEdge++), item.Id, target, successor, boundary));
            }
            blocks.Add(new(item.Id, item.Address, ir, null, edges.ToImmutable()));
        }
        var region = new RegionRevision(Guid.NewGuid().ToString("N"), source.ImageId, source.Architecture,
            MachineProfile.For(source.Architecture).Id, MirJson.SemanticsVersion, entries, blocks.ToImmutableArray());
        var errors = RegionValidator.Validate(region);
        if (errors.Count != 0) throw new InvalidDataException(string.Join("; ", errors));
        return region;
    }

    public static ulong? DirectAddress(MirInstruction instruction, MirSuccessor successor)
    {
        if (successor.Destination is AddressDestination address) return address.Address;
        if (successor.Destination is not ValueDestination value) return null;
        // 只读取 MIR 常量定义，不猜测地址，也不重解释机器指令。
        var definition = instruction.Operations.FirstOrDefault(op => op.Result == value.Target);
        return definition is { Code: OpCode.Constant } && value.Target.Width == 64 ? (ulong)definition.Immediate : null;
    }

    internal static RegionBoundary? TransferBoundary(MirSuccessor successor) => successor.TransferHint switch
    {
        TransferHint.Call => new(RegionBoundaryKind.Call, "机器调用转移；尚未采用调用摘要与返回协议"),
        TransferHint.Return => new(RegionBoundaryKind.Return, "机器返回转移；保留计算目标与完整出口状态"),
        _ => successor.Kind == SuccessorKind.ExceptionBoundary ?
            new(RegionBoundaryKind.ExceptionBoundary, "异常边界；异常分派尚未建模") : null
    };

    private static RegionBoundaryKind DecodeBoundary(InstructionDecodeFailure failure) => failure switch
    {
        InstructionDecodeFailure.Unmapped => RegionBoundaryKind.Unmapped,
        InstructionDecodeFailure.NotExecutable => RegionBoundaryKind.NotExecutable,
        InstructionDecodeFailure.NotFileBacked => RegionBoundaryKind.NotFileBacked,
        InstructionDecodeFailure.Truncated => RegionBoundaryKind.Truncated,
        InstructionDecodeFailure.Unaligned => RegionBoundaryKind.Unaligned,
        InstructionDecodeFailure.InvalidEncoding => RegionBoundaryKind.InvalidEncoding,
        InstructionDecodeFailure.Unsupported => RegionBoundaryKind.Unsupported,
        InstructionDecodeFailure.CodeRelocation => RegionBoundaryKind.CodeRelocation,
        _ => throw new ArgumentOutOfRangeException(nameof(failure))
    };

    private sealed class ImageSource(ImageDocument image) : IRegionInstructionSource
    {
        private readonly InstructionDecoder decoder = new(image);
        public string ImageId => image.Sha256;
        public Architecture Architecture => image.Architecture;
        public InstructionDecodeResult Decode(ulong address) => decoder.Decode(address);
    }

    private sealed class InstructionSource : IRegionInstructionSource
    {
        private readonly Dictionary<ulong, MirInstruction> instructions;
        public string ImageId { get; }
        public Architecture Architecture { get; }
        public InstructionSource(Architecture architecture, string imageId, IEnumerable<MirInstruction> instructions)
        {
            Architecture = architecture;
            ImageId = imageId;
            this.instructions = instructions.ToDictionary(ir => ir.Origin.Address);
            foreach (var ir in this.instructions.Values)
                if (ir.Architecture != architecture || ir.Origin.ImageId != imageId)
                    throw new ArgumentException("fixture 指令来源不一致", nameof(instructions));
        }
        public InstructionDecodeResult Decode(ulong address) => instructions.TryGetValue(address, out var ir) ?
            InstructionDecodeResult.Supported(ir) : InstructionDecodeResult.Stopped(InstructionDecodeFailure.Unmapped, "fixture 未提供此入口");
    }
}
