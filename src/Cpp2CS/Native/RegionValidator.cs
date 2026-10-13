using Cpp2CS.Ir;

namespace Cpp2CS.Native;

public static class RegionValidator
{
    public static IReadOnlyList<string> Validate(RegionRevision region)
    {
        List<string> errors = [];
        if (string.IsNullOrWhiteSpace(region.Revision) || string.IsNullOrWhiteSpace(region.ImageId))
            errors.Add("missing region revision or image identity");
        if (!Enum.IsDefined(region.Architecture)) return ["unknown region architecture"];
        if (region.ProfileId != MachineProfile.For(region.Architecture).Id || region.SemanticsVersion != MirJson.SemanticsVersion)
            errors.Add("region profile or semantics version mismatch");
        if (region.Blocks.IsDefaultOrEmpty || region.Entries.IsDefaultOrEmpty)
            return [.. errors, "region requires explicit entries and blocks"];
        var blocks = new Dictionary<BlockId, RegionBlock>();
        var addresses = new HashSet<ulong>();
        var byteEvidence = new Dictionary<ulong, (long Offset, byte Byte)>();
        foreach (var block in region.Blocks)
        {
            if (block is null) { errors.Add("null region block"); continue; }
            if (block.Id.Id != blocks.Count || !blocks.TryAdd(block.Id, block)) errors.Add("invalid or duplicate block identity");
            if (!addresses.Add(block.Address)) errors.Add("duplicate block address");
        }
        var nextEdge = 0;
        foreach (var block in region.Blocks)
        {
            if (block is null) continue;
            if (block.Edges.IsDefault) { errors.Add("missing block edges"); continue; }
            if (block.Instruction is not { } instruction)
            {
                if (!ValidBoundary(block.Stop) || block.Stop!.Kind is RegionBoundaryKind.Call or RegionBoundaryKind.Return or
                    RegionBoundaryKind.ExceptionBoundary or RegionBoundaryKind.IndirectTarget || block.Edges.Length != 0)
                    errors.Add("invalid decode stop block");
                continue;
            }
            if (block.Stop is not null) errors.Add("lifted block also declares decode stop");
            if (instruction.Architecture != region.Architecture || instruction.ProfileId != region.ProfileId ||
                instruction.Origin is null || instruction.Origin.ImageId != region.ImageId || instruction.Origin.Address != block.Address)
                errors.Add("block MIR origin or profile mismatch");
            var mirErrors = MirValidator.Validate(instruction);
            if (mirErrors.Count != 0) { errors.AddRange(mirErrors.Select(error => $"block {block.Id.Id}: {error}")); continue; }
            var origin = instruction.Origin!;
            for (var index = 0; index < origin.Bytes.Length; index++)
            {
                if ((ulong)index > ulong.MaxValue - origin.Address || index > long.MaxValue - origin.FileOffset)
                { errors.Add("instruction origin range overflows"); break; }
                var address = origin.Address + (ulong)index;
                var evidence = (origin.FileOffset + index, origin.Bytes.Span[index]);
                if (byteEvidence.TryGetValue(address, out var existing) && existing != evidence)
                    errors.Add("overlapping decode paths disagree on source bytes");
                else byteEvidence[address] = evidence;
            }
            var successors = MirInspection.Describe(instruction).Successors;
            if (block.Edges.Length != successors.Length) errors.Add("MIR successor omitted or invented");
            for (var index = 0; index < block.Edges.Length; index++)
            {
                var edge = block.Edges[index];
                if (edge is null) { errors.Add("null region edge"); continue; }
                if (edge.Id.Id != nextEdge++) errors.Add("invalid or duplicate edge identity");
                if (edge.Source != block.Id) errors.Add("edge source mismatch");
                if (index >= successors.Length || edge.Successor != successors[index])
                { errors.Add("edge does not preserve MIR successor semantics"); continue; }
                var requiredBoundary = RegionBuilder.TransferBoundary(edge.Successor);
                var directAddress = RegionBuilder.DirectAddress(instruction, edge.Successor);
                if (edge.Target is { } target)
                {
                    if (edge.Boundary is not null || requiredBoundary is not null || directAddress is null)
                        errors.Add("open machine transfer represented as internal closed edge");
                    if (!blocks.TryGetValue(target, out var destination)) errors.Add("edge target block missing");
                    else if (destination.Address != directAddress) errors.Add("edge target address disagrees with MIR");
                }
                else
                {
                    if (!ValidBoundary(edge.Boundary)) { errors.Add("open edge lost boundary reason"); continue; }
                    if (requiredBoundary is not null)
                    {
                        if (edge.Boundary!.Kind != requiredBoundary.Kind) errors.Add("transfer boundary category changed");
                    }
                    else if (directAddress is not null || edge.Boundary!.Kind != RegionBoundaryKind.IndirectTarget)
                        errors.Add("direct successor lost its target block or indirect residual misclassified");
                }
            }
        }
        var reached = new HashSet<BlockId>();
        var pending = new Queue<BlockId>();
        foreach (var entry in region.Entries)
        {
            if (entry?.Seed is null || string.IsNullOrWhiteSpace(entry.Seed.Evidence))
            { errors.Add("entry evidence missing"); continue; }
            if (!blocks.TryGetValue(entry.Block, out var block) || block.Address != entry.Seed.Address)
            { errors.Add("entry block does not match its seed"); continue; }
            if (reached.Add(entry.Block)) pending.Enqueue(entry.Block);
        }
        while (pending.TryDequeue(out var id))
        {
            var block = blocks[id];
            if (block.Edges.IsDefault) continue;
            foreach (var edge in block.Edges)
                if (edge?.Target is { } target && blocks.ContainsKey(target) && reached.Add(target)) pending.Enqueue(target);
        }
        if (reached.Count != blocks.Count) errors.Add("region contains blocks not discovered from any explicit seed");
        return errors;
    }

    private static bool ValidBoundary(RegionBoundary? boundary) => boundary is not null &&
        Enum.IsDefined(boundary.Kind) && !string.IsNullOrWhiteSpace(boundary.Reason);
}
