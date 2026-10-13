using Cpp2CS.Ir;
using Cpp2CS.Native;

namespace Cpp2CS.Recovery;

// 原 Region/N1 验证器不接受摘要边；本验证器只检查带采用合同的派生函数图。
public static class DerivedGraphValidator
{
    public static IReadOnlyList<string> Validate(DerivedFunctionGraph graph)
    {
        List<string> errors = [];
        if (string.IsNullOrWhiteSpace(graph.Revision) || string.IsNullOrWhiteSpace(graph.ImageId) ||
            !Enum.IsDefined(graph.Architecture) || graph.Blocks.IsDefaultOrEmpty || graph.Gaps.IsDefault || graph.Dependencies.IsDefault)
            return ["derived graph lacks identity, architecture or collections"];
        var interfaceValid = MachineAbi.TryDescribe(graph.Contract, out _, out _);
        if (interfaceValid && MachineAbi.ArchitectureFor(graph.Contract.Abi) != graph.Architecture)
            interfaceValid = false;
        if (!interfaceValid && !(graph.Blocks.Length == 1 && graph.Blocks[0].Gap?.Kind == RecoveryGapKind.UnsupportedInterface))
            errors.Add("unsupported function interface is not a recovery gap");
        if (!graph.Dependencies.Contains(FunctionGraphBuilder.ContractDependency(graph.Contract)))
            errors.Add("function contract dependency is missing");
        var blocks = new Dictionary<int, DerivedFunctionBlock>();
        var addresses = new HashSet<ulong>();
        var observedGaps = new List<RecoveryGap>();
        var edgeIds = new HashSet<int>();
        var byteEvidence = new Dictionary<ulong, (long Offset, byte Byte)>();
        foreach (var block in graph.Blocks)
        {
            if (block.Id != blocks.Count || !blocks.TryAdd(block.Id, block) || !addresses.Add(block.Address))
                errors.Add("duplicate or invalid derived block identity");
        }
        if (!graph.Blocks.Any(block => block.Address == graph.Contract.EntryAddress)) errors.Add("function entry is missing");
        foreach (var block in graph.Blocks)
        {
            if (block.Edges.IsDefault) { errors.Add("missing derived block edges"); continue; }
            if (block.Instruction is not { } instruction)
            {
                if (block.Gap is not { } gap || block.Edges.Length != 0 ||
                    gap.Kind is not (RecoveryGapKind.Decode or RecoveryGapKind.Budget or RecoveryGapKind.UnsupportedInterface))
                    errors.Add("non-instruction block is not a discovery gap");
                if (block.Gap is { } missing) observedGaps.Add(missing);
                continue;
            }
            if (block.Gap is not null) errors.Add("machine block also has a discovery gap");
            if (instruction.Architecture != graph.Architecture || instruction.Origin.ImageId != graph.ImageId ||
                instruction.Origin.Address != block.Address)
                errors.Add("derived instruction source mismatch");
            var mirErrors = MirValidator.Validate(instruction);
            if (mirErrors.Count != 0) { errors.AddRange(mirErrors); continue; }
            for (var index = 0; index < instruction.Origin.Bytes.Length; index++)
            {
                if ((ulong)index > ulong.MaxValue - block.Address || index > long.MaxValue - instruction.Origin.FileOffset)
                { errors.Add("derived instruction byte range overflows"); break; }
                var address = block.Address + (ulong)index;
                var evidence = (instruction.Origin.FileOffset + index, instruction.Origin.Bytes.Span[index]);
                if (byteEvidence.TryGetValue(address, out var prior) && prior != evidence)
                    errors.Add("derived overlapping instructions disagree on source bytes");
                else byteEvidence[address] = evidence;
            }
            var original = MirInspection.Describe(instruction).Successors;
            if (block.Edges.Length != original.Length) errors.Add("original MIR successor omitted or duplicated");
            for (var index = 0; index < block.Edges.Length; index++)
            {
                var edge = block.Edges[index];
                if (edge.Id < 0 || !edgeIds.Add(edge.Id) || edge.SourceBlock != block.Id) errors.Add("derived edge identity mismatch");
                if (index >= original.Length || edge.Source != original[index])
                { errors.Add("derived edge altered the original MIR successor"); continue; }
                if (!Enum.IsDefined(edge.Kind)) { errors.Add("unknown derived edge kind"); continue; }
                if (edge.TargetBlock is { } target && !blocks.ContainsKey(target)) errors.Add("derived target block is absent");
                if (edge.Gap is { } gap)
                {
                    observedGaps.Add(gap);
                    if (gap.Address != block.Address || string.IsNullOrWhiteSpace(gap.Reason)) errors.Add("edge gap lacks source or reason");
                }
                var direct = RegionBuilder.DirectAddress(instruction, edge.Source);
                if (direct is not null && edge.MachineTarget != direct) errors.Add("original machine target changed");
                if (edge.Kind is not (DerivedEdgeKind.Call or DerivedEdgeKind.TailCall) &&
                    (edge.Call is not null || edge.Continuation is not null)) errors.Add("non-call edge contains a summary");
                if (edge.IsTailCandidate && edge.Kind != DerivedEdgeKind.TailCall)
                    errors.Add("tail candidate is attached to a non-tail edge");
                switch (edge.Kind)
                {
                    case DerivedEdgeKind.Direct:
                        if (edge.Source.TransferHint != TransferHint.None || edge.Gap is not null || direct is null ||
                            edge.TargetBlock is not { } directId || !blocks.TryGetValue(directId, out var next) || next.Address != direct)
                            errors.Add("direct machine successor is not preserved");
                        break;
                    case DerivedEdgeKind.Return:
                        if (edge.Source.TransferHint != TransferHint.Return || edge.TargetBlock is not null || edge.Gap is not null)
                            errors.Add("return boundary invented a continuation");
                        break;
                    case DerivedEdgeKind.Call:
                    case DerivedEdgeKind.TailCall:
                        ValidateCall(edge, instruction);
                        break;
                    case DerivedEdgeKind.Gap:
                        if (edge.Gap is null || edge.TargetBlock is not null) errors.Add("gap masquerades as a closed edge");
                        break;
                    case DerivedEdgeKind.Exception:
                        if (edge.Source.Kind != SuccessorKind.ExceptionBoundary || edge.TargetBlock is not null || edge.Gap is null)
                            errors.Add("machine exception boundary is not retained");
                        break;
                }
            }
        }
        if (observedGaps.Count != graph.Gaps.Length || !observedGaps.OrderBy(GapKey).SequenceEqual(graph.Gaps.OrderBy(GapKey)))
            errors.Add("derived graph recovery gaps do not match its boundaries");
        var visited = new HashSet<int>();
        var pending = new Queue<int>();
        foreach (var entry in graph.Blocks.Where(block => block.Address == graph.Contract.EntryAddress)) pending.Enqueue(entry.Id);
        while (pending.TryDequeue(out var id))
        {
            if (!visited.Add(id) || !blocks.TryGetValue(id, out var block)) continue;
            foreach (var edge in block.Edges)
                if (edge.TargetBlock is { } target && blocks.ContainsKey(target)) pending.Enqueue(target);
        }
        if (visited.Count != blocks.Count) errors.Add("derived graph contains undiscovered blocks");
        return errors;

        void ValidateCall(DerivedFunctionEdge edge, MirInstruction instruction)
        {
            if (edge.Call is not { } summary || edge.MachineTarget != summary.Callee.EntryAddress || edge.Gap is not null)
            { errors.Add("derived call lacks a target-bound summary"); return; }
            if (summary.Callee.Abi != graph.Contract.Abi) errors.Add("call summary ABI does not match caller");
            if (!graph.Dependencies.Contains(FunctionGraphBuilder.ContractDependency(summary.Callee)))
                errors.Add("call summary contract dependency is absent");
            errors.AddRange(ValidateSummary(summary));
            if (edge.Kind == DerivedEdgeKind.TailCall)
            {
                var evidence = edge.IsTailCandidate
                    ? DirectTailCandidate()
                    : graph.Dependencies.Any(value => value.StartsWith($"adopted-tail-call:0x{instruction.Origin.Address:X}:", StringComparison.Ordinal));
                if (edge.Source.TransferHint != TransferHint.None || edge.Source.Kind != SuccessorKind.Jump ||
                    edge.TargetBlock is not null || edge.Continuation is not null ||
                    summary.Callee.Signature.Result != graph.Contract.Signature.Result || !evidence)
                    errors.Add("tail call lacks a compatible adopted relation or a direct candidate awaiting protocol proof");
                return;

                bool DirectTailCandidate() => summary.Callee.EntryAddress != graph.Contract.EntryAddress &&
                    RegionBuilder.DirectAddress(instruction, edge.Source) == summary.Callee.EntryAddress &&
                    graph.Dependencies.Contains($"tail-call-candidate:0x{instruction.Origin.Address:X}:0x{summary.Callee.EntryAddress:X}");
            }
            if (edge.Source.TransferHint != TransferHint.Call) errors.Add("call summary is not attached to a machine call");
            if (RegionBuilder.DirectAddress(instruction, edge.Source) is null &&
                !graph.Dependencies.Contains($"adopted-call-target:0x{instruction.Origin.Address:X}:0x{summary.Callee.EntryAddress:X}"))
                errors.Add("indirect call target binding has no adopted evidence");
            if (summary.Callee.Effects.MayReturn)
            {
                if ((ulong)instruction.Origin.Bytes.Length > ulong.MaxValue - instruction.Origin.Address ||
                    edge.Continuation != instruction.Origin.Address + (ulong)instruction.Origin.Bytes.Length ||
                    edge.TargetBlock is not { } target || !blocks.TryGetValue(target, out var continuation) ||
                    continuation.Address != edge.Continuation)
                    errors.Add("normal call result is not connected to its continuation");
            }
            else if (edge.TargetBlock is not null || edge.Continuation is not null)
                errors.Add("nonreturning call has a normal continuation");
        }
    }

    public static IReadOnlyList<string> ValidateSummary(MachineCallSummary summary)
    {
        List<string> errors = [];
        if (!MachineAbi.TryDescribe(summary.Callee, out var mapping, out var reason)) return [reason!];
        if (summary.Interface.Result != mapping!.Result || summary.Interface.StackPointer != mapping.StackPointer ||
            summary.Interface.StackAlignment != mapping.StackAlignment || summary.Interface.NormalReturnSpAdjustment != mapping.NormalReturnSpAdjustment ||
            summary.Interface.Arguments.IsDefault || !summary.Interface.Arguments.SequenceEqual(mapping.Arguments))
            errors.Add("call interface differs from the adopted scalar ABI");
        var layout = StateLayout.For(MachineAbi.ArchitectureFor(summary.Callee.Abi));
        if (summary.Reads.IsDefault || summary.Reads.Length != layout.Count ||
            summary.Reads.Select(read => read.Slot).Distinct(StringComparer.Ordinal).Count() != layout.Count ||
            summary.Reads.Any(read => !layout.TryGetValue(read.Slot, out var width) || read.Offset != 0 || read.Width != width))
            errors.Add("unknown callee body read dependencies do not cover the machine state");
        if (!summary.World.ReadsWorld || !summary.World.MayWritePrivateStack ||
            summary.World.WritesProgramMemory != summary.Callee.Effects.WritesMemory ||
            summary.World.ExternalEffects != summary.Callee.Effects.ExternalEffects)
            errors.Add("call world relation loses a declared effect or private-stack mutation");
        if (summary.Callee.Effects.MayReturn) CheckOutputs(summary.NormalOutputs, false);
        else if (!summary.NormalOutputs.IsEmpty) errors.Add("nonreturning call has normal machine outputs");
        if (summary.Prerequisites.IsDefaultOrEmpty || summary.Prerequisites.Any(string.IsNullOrWhiteSpace))
            errors.Add("summary prerequisites are absent");
        if (summary.OtherOutcomes.IsDefault) errors.Add("summary outcomes are absent");
        else
        {
            var kinds = summary.OtherOutcomes.Select(outcome => outcome.Kind).ToArray();
            if (kinds.Distinct().Count() != kinds.Length ||
                kinds.Contains(MachineCallOutcomeKind.Unwind) != summary.Callee.Effects.MayThrow ||
                kinds.Contains(MachineCallOutcomeKind.Terminate) != summary.Callee.Effects.MayTerminate ||
                kinds.Contains(MachineCallOutcomeKind.Diverge) != summary.Callee.Effects.MayDiverge)
                errors.Add("summary outcomes differ from logical contract");
            foreach (var outcome in summary.OtherOutcomes)
            {
                if (!Enum.IsDefined(outcome.Kind) || outcome.World != summary.World) errors.Add("invalid summary outcome");
                if (outcome.Kind == MachineCallOutcomeKind.Unwind) CheckOutputs(outcome.Outputs, true);
                else if (!outcome.Outputs.IsEmpty) errors.Add("terminal behavior invents an available output state");
            }
        }
        var expected = MachineAbi.CreateSummary(summary.Callee);
        if (!SameOutputs(summary.NormalOutputs, expected.NormalOutputs)) errors.Add("normal slot relations differ from adopted ABI rules");
        if (summary.Prerequisites.IsDefault || !summary.Prerequisites.SequenceEqual(expected.Prerequisites)) errors.Add("summary prerequisites differ from adopted contract");
        return errors;

        void CheckOutputs(System.Collections.Immutable.ImmutableArray<MachineSlotRelation> outputs, bool allHavoc)
        {
            if (outputs.IsDefault || outputs.Length != layout.Count || outputs.Select(output => output.Slot).Distinct(StringComparer.Ordinal).Count() != layout.Count)
            { errors.Add("summary outputs do not cover every machine slot"); return; }
            foreach (var output in outputs)
            {
                if (!layout.TryGetValue(output.Slot, out var width) || width != output.Width || output.Segments.IsDefaultOrEmpty)
                { errors.Add("summary output slot shape mismatch"); continue; }
                var covered = 0;
                foreach (var segment in output.Segments)
                {
                    if (segment.Offset != covered || segment.Width < 1 || segment.Width > width - covered ||
                        !Enum.IsDefined(segment.Kind) || allHavoc && segment.Kind != SlotRelationKind.Havoc)
                        errors.Add("summary output bits overlap, are omitted, or have an invalid relation");
                    covered += segment.Width;
                    if (segment.Kind is SlotRelationKind.Preserve or SlotRelationKind.AddConstant)
                    {
                        if (segment.InputSlot is null || !layout.TryGetValue(segment.InputSlot, out var inputWidth) ||
                            segment.InputOffset < 0 || segment.Width > inputWidth - segment.InputOffset)
                            errors.Add("summary relation reads an invalid machine bit range");
                    }
                    else if (segment.InputSlot is not null) errors.Add("summary result or havoc invents a machine input");
                    if (segment.Kind == SlotRelationKind.Result && (mapping.Result is null || output.Slot != mapping.Result.Slot ||
                        segment.Offset != mapping.Result.Offset || segment.Width != mapping.Result.Width))
                        errors.Add("logical result is bound to the wrong machine bits");
                }
                if (covered != width) errors.Add("summary leaves machine output bits uncovered");
            }
        }
    }

    private static bool SameOutputs(System.Collections.Immutable.ImmutableArray<MachineSlotRelation> a,
        System.Collections.Immutable.ImmutableArray<MachineSlotRelation> b) => !a.IsDefault && a.Length == b.Length &&
        a.Zip(b).All(pair => pair.First.Slot == pair.Second.Slot && pair.First.Width == pair.Second.Width &&
            !pair.First.Segments.IsDefault && pair.First.Segments.SequenceEqual(pair.Second.Segments));

    private static string GapKey(RecoveryGap gap) => $"{gap.Address:X16}:{gap.Kind}:{gap.Reason}";
}
