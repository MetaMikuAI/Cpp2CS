using System.Buffers.Binary;
using System.Collections.Immutable;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Cpp2CS.Native;

namespace Cpp2CS.Validation;

public static class RegionChecks
{
    public static int Run()
    {
        var checks = 0;
        void Check(bool condition, string message) { CoreChecks.Require(condition, message); checks++; }
        static RegionRevision Build(Architecture architecture, string bytes, ulong[]? seeds = null, int budget = 100) =>
            RegionBuilder.Build(new ByteSource(architecture, Convert.FromHexString(bytes)),
                (seeds ?? [0x1000]).Select(address => new EntrySeed(address, "explicit test entry")), budget);

        var loop = Build(Architecture.Arm64, "000400F1E1FFFF54C0035FD6", [0x1000, 0x1004]);
        Check(loop.Blocks.Length == 3 && loop.Entries.Length == 2, "ARM multiple entries share decoded instruction identities");
        var branch = loop.Blocks.Single(block => block.Address == 0x1004);
        Check(branch.Edges[0].Target == loop.Entries[0].Block && branch.Edges[0].Successor.Condition!.RequiredValue,
            "ARM conditional backward edge retains taken predicate");
        Check(branch.Edges[1].Target == loop.Blocks.Single(block => block.Address == 0x1008).Id &&
            !branch.Edges[1].Successor.Condition!.RequiredValue, "ARM fallthrough retains opposite predicate");
        Check(loop.Blocks.Single(block => block.Address == 0x1008).Edges.Single().Boundary!.Kind == RegionBoundaryKind.Return,
            "ARM RET has a typed open return boundary");
        Check(RegionValidator.Validate(loop).Count == 0, "ARM source and graph invariants validate");

        var overlap = Build(Architecture.X64, "B890909090C3", [0x1000, 0x1001]);
        Check(overlap.Blocks.Length == 6 && overlap.Blocks[0].Instruction!.Origin.Bytes.Length == 5,
            "x64 secondary entry is decoded even inside another instruction");
        Check(overlap.Blocks.Single(block => block.Address == 0x1001).Instruction!.Origin.Bytes.Length == 1,
            "x64 overlapping entry keeps its own byte extent");
        Check(overlap.Blocks.Count(block => block.Address == 0x1005) == 1, "overlap paths join by exact instruction entry");
        Check(RegionValidator.Validate(overlap).Count == 0, "overlapping evidence agrees on image bytes and offsets");

        var parallel = Build(Architecture.X64, "7400C3");
        var parallelEdges = parallel.Blocks[0].Edges;
        Check(parallelEdges.Length == 2 && parallelEdges[0].Target == parallelEdges[1].Target,
            "parallel same-target edges are not merged");
        Check(parallelEdges[0].Id != parallelEdges[1].Id && parallelEdges[0].Successor.Condition != parallelEdges[1].Successor.Condition,
            "parallel edges preserve independent identity and condition");

        foreach (var (architecture, bytes) in new[]
        {
            (Architecture.Arm64, "01000094C0035FD6"),
            (Architecture.Arm64, "00003FD6"),
            (Architecture.X64, "E800000000C3"),
            (Architecture.X64, "FFD0")
        })
        {
            var call = Build(architecture, bytes);
            Check(call.Blocks.Length == 1 && call.Blocks[0].Edges is [{ Target: null, Boundary.Kind: RegionBoundaryKind.Call }],
                "machine call remains an open transfer without invented continuation");
            Check(call.Blocks[0].Instruction!.Exit.TransferHint == TransferHint.Call,
                "lifter records call category at the encoding boundary");
            var serialized = MirJson.Serialize(call.Blocks[0].Instruction!);
            Check(MirJson.Deserialize(serialized).Exit.TransferHint == TransferHint.Call, "call hint survives strict MIR JSON");
        }
        foreach (var (architecture, bytes) in new[]
        {
            (Architecture.Arm64, "C0035FD6"), (Architecture.X64, "C3"), (Architecture.X64, "C20800")
        })
        {
            var ret = Build(architecture, bytes);
            Check(ret.Blocks.Length == 1 && ret.Blocks[0].Edges.Single().Boundary!.Kind == RegionBoundaryKind.Return,
                "return has no fabricated static successor");
        }
        foreach (var (architecture, bytes) in new[] { (Architecture.Arm64, "00001FD6"), (Architecture.X64, "FFE0") })
        {
            var indirect = Build(architecture, bytes);
            Check(indirect.Blocks[0].Edges is [{ Target: null, Boundary.Kind: RegionBoundaryKind.IndirectTarget }],
                "unknown indirect target retains a residual edge");
            Check(indirect.Blocks[0].Edges[0].Successor.Destination is ValueDestination,
                "indirect residual retains its original target expression");
        }
        var trap = Build(Architecture.X64, "0F0B");
        Check(trap.Blocks[0].Edges is [{ Boundary.Kind: RegionBoundaryKind.ExceptionBoundary,
            Successor.Destination: ExceptionDestination }], "UD2 is an exception boundary, not an invalid input or fallthrough");
        var unmapped = Build(Architecture.X64, "EB05");
        Check(unmapped.Blocks is [_, { Address: 0x1007, Instruction: null, Stop.Kind: RegionBoundaryKind.Unmapped }],
            "direct unmapped target becomes an explicit stop block");
        Check(Build(Architecture.X64, "D9E8").Blocks[0].Stop!.Kind == RegionBoundaryKind.Unsupported,
            "decoded but unsupported x87 input remains a semantic gap");
        Check(Build(Architecture.X64, "069090909090909090909090909090").Blocks[0].Stop!.Kind == RegionBoundaryKind.InvalidEncoding,
            "x64 invalid encoding is distinct from missing semantics");
        Check(Build(Architecture.X64, "0F").Blocks[0].Stop!.Kind == RegionBoundaryKind.Truncated,
            "x64 incomplete encoding is a truncated byte boundary");
        Check(Build(Architecture.Arm64, "1F2003").Blocks[0].Stop!.Kind == RegionBoundaryKind.Truncated,
            "ARM incomplete word is a truncated byte boundary");
        Check(Build(Architecture.Arm64, "1F2003D5C0035FD6", [0x1001]).Blocks[0].Stop!.Kind == RegionBoundaryKind.Unaligned,
            "unaligned ARM entry remains visible");
        var budget = Build(Architecture.X64, "7400C3", budget: 1);
        Check(budget.Blocks is [_, { Instruction: null, Stop.Kind: RegionBoundaryKind.Budget }] && budget.Blocks[0].Edges.Length == 2,
            "budget keeps both known predecessor edges and the unexplored target");
        Check(Build(Architecture.X64, "90", budget: 0).Blocks is [{ Stop.Kind: RegionBoundaryKind.Budget }],
            "zero decode budget preserves the explicit entry as an open stop");
        Check(InstructionDecoder.DecodeBytes(Architecture.X64, "fixture", 0x1000, 0, new byte[] { 0x90 }, (_, _) => true).Failure ==
            InstructionDecodeFailure.CodeRelocation, "relocated instruction bytes are not lifted as runtime code");

        var image = ImageDocument.Parse(PeFixture());
        var decoder = new InstructionDecoder(image);
        Check(decoder.Decode(0x180000000).Failure == InstructionDecodeFailure.NotExecutable, "PE header is mapped but non-executable");
        Check(decoder.Decode(0x180001200).Failure == InstructionDecodeFailure.NotFileBacked, "PE executable zero-fill lacks code bytes");
        Check(decoder.Decode(0x180001300).Failure == InstructionDecodeFailure.Unmapped, "PE out-of-range target stays unmapped");
        var imageRegion = RegionBuilder.Build(image, [new(0x180001000, "fixture executable entry")]);
        Check(imageRegion.ImageId == image.Sha256 && imageRegion.Blocks[0].Instruction!.Origin.FileOffset == 0x200,
            "region entry decodes actual mapped image bytes with provenance");

        var original = parallel.Blocks[0];
        RegionRevision Replace(RegionBlock block) => parallel with { Blocks = parallel.Blocks.SetItem(0, block) };
        Check(RegionValidator.Validate(Replace(original with { Edges = [] })).Count != 0, "validator rejects omitted MIR successors");
        Check(RegionValidator.Validate(Replace(original with { Edges = original.Edges.SetItem(0,
            original.Edges[0] with { Target = new(999) }) })).Count != 0, "validator rejects dangling closed targets");
        Check(RegionValidator.Validate(Replace(original with { Edges = original.Edges.SetItem(0,
            original.Edges[0] with { Target = null, Boundary = null }) })).Count != 0, "validator rejects silent loss of an open boundary");
        Check(RegionValidator.Validate(Replace(original with { Edges = original.Edges.SetItem(1,
            original.Edges[1] with { Id = original.Edges[0].Id }) })).Count != 0, "validator rejects coalesced parallel edge identity");
        Check(RegionValidator.Validate(Replace(original with { Edges = original.Edges.SetItem(0,
            original.Edges[0] with { Successor = original.Edges[0].Successor with { State = new(999) } }) })).Count != 0,
            "validator rejects changed exit state");
        Check(RegionValidator.Validate(parallel with { ProfileId = "other-profile" }).Count != 0, "validator rejects profile mixing");
        Check(RegionValidator.Validate(parallel with { Blocks = parallel.Blocks.Add(new(new(parallel.Blocks.Length), 0x9999,
            null, new(RegionBoundaryKind.Unmapped, "unreachable"), [])) }).Count != 0, "validator rejects unseeded unreachable blocks");
        var overlappingBlock = overlap.Blocks.Single(block => block.Address == 0x1001);
        var changedOrigin = new InstructionOrigin(overlap.ImageId, 0x1001, 1, new byte[] { 0x91 });
        Check(RegionValidator.Validate(overlap with { Blocks = overlap.Blocks.SetItem(overlappingBlock.Id.Id,
            overlappingBlock with { Instruction = overlappingBlock.Instruction! with { Origin = changedOrigin } }) }).Count != 0,
            "validator rejects conflicting overlapping byte evidence");
        var nop = Build(Architecture.X64, "90", budget: 1).Blocks[0].Instruction!;
        Check(MirValidator.Validate(nop with { Exit = nop.Exit with { TransferHint = TransferHint.Call } }).Count != 0,
            "non-jump exits cannot carry call hints");
        var jump = Build(Architecture.X64, "EBFE").Blocks[0].Instruction!;
        Check(MirValidator.Validate(jump with { Exit = jump.Exit with { TransferHint = (TransferHint)99 } }).Count != 0,
            "unknown transfer categories are rejected");
        var mislabeled = jump with { Rule = "fixture.only.display.call" };
        var ruleIndependent = RegionBuilder.FromInstructions(Architecture.X64, jump.Origin.ImageId, [mislabeled],
            [new(0x1000, "fixture entry")]);
        Check(ruleIndependent.Blocks[0].Edges.Single().Target == ruleIndependent.Blocks[0].Id,
            "region graph depends on MIR semantics rather than the rule name");
        return checks;
    }

    private sealed class ByteSource(Architecture architecture, byte[] bytes) : IRegionInstructionSource
    {
        public string ImageId => "fixture:region-bytes";
        public Architecture Architecture => architecture;
        public InstructionDecodeResult Decode(ulong address) => address < 0x1000 || address - 0x1000 >= (ulong)bytes.Length ?
            InstructionDecodeResult.Stopped(InstructionDecodeFailure.Unmapped, "fixture address is unmapped") :
            InstructionDecoder.DecodeBytes(architecture, ImageId, address, checked((long)(address - 0x1000)),
                bytes.AsMemory(checked((int)(address - 0x1000))));
    }

    private static byte[] PeFixture()
    {
        var bytes = new byte[0x400];
        void U16(int offset, ushort value) => BinaryPrimitives.WriteUInt16LittleEndian(bytes.AsSpan(offset, 2), value);
        void U32(int offset, uint value) => BinaryPrimitives.WriteUInt32LittleEndian(bytes.AsSpan(offset, 4), value);
        void U64(int offset, ulong value) => BinaryPrimitives.WriteUInt64LittleEndian(bytes.AsSpan(offset, 8), value);
        U16(0, 0x5a4d); U32(60, 0x80); U32(0x80, 0x4550);
        U16(0x84, 0x8664); U16(0x86, 1); U16(0x94, 112);
        const int optional = 0x98;
        U16(optional, 0x20b); U64(optional + 24, 0x180000000);
        U32(optional + 32, 0x1000); U32(optional + 36, 0x200);
        U32(optional + 56, 0x2000); U32(optional + 60, 0x200);
        const int section = optional + 112;
        ".text"u8.CopyTo(bytes.AsSpan(section));
        U32(section + 8, 0x300); U32(section + 12, 0x1000);
        U32(section + 16, 0x200); U32(section + 20, 0x200); U32(section + 36, 0x60000020);
        bytes[0x200] = 0xc3;
        return bytes;
    }
}
