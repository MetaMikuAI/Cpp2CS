using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Arm64;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Cpp2CS.Native;
using Cpp2CS.Recovery;
using Cpp2CS.X64;
using Iced.Intel;

namespace Cpp2CS.Validation;

public static class RecoveryGraphChecks
{
    private const string ImageId = "fixture:recovery-graph";

    public static int Run()
    {
        var checks = 0;
        void Check(bool value, string reason) { CoreChecks.Require(value, reason); checks++; }
        foreach (var abi in new[] { MachineAbiKind.Aapcs64, MachineAbiKind.WindowsX64 })
        {
            var arm = abi == MachineAbiKind.Aapcs64;
            var architecture = MachineAbi.ArchitectureFor(abi);
            var caller = Contract("caller", 0x1000, abi);
            var callee = Contract("callee", 0x2000, abi);
            var stackContract = callee with
            {
                Signature = new(Enumerable.Range(0, 10).Select(index => new RecoveryScalarType(index % 2 == 0 ? 32 : 64)).ToImmutableArray(), new(32))
            };
            var mapping = MachineAbi.Describe(stackContract);
            var registerCount = arm ? 8 : 4;
            Check(mapping.Arguments.Take(registerCount).All(argument => argument is SlotArgumentLocation), "scalar ABI register arguments precede stack arguments");
            Check(mapping.Arguments[registerCount] == new StackArgumentLocation(arm ? 0 : 40, 32), "first stack argument uses callee-entry SP including x64 return address and shadow space");
            Check(mapping.Arguments[registerCount + 1] == new StackArgumentLocation(arm ? 8 : 48, 64), "scalar stack argument slots advance by eight bytes");
            Check(mapping.NormalReturnSpAdjustment == (arm ? 0 : 8), "summary normal result applies only the return SP adjustment");
            var summary = MachineAbi.CreateSummary(stackContract);
            Check(DerivedGraphValidator.ValidateSummary(summary).Count == 0, "complete scalar machine summary validates");
            Check(summary.NormalOutputs.Length == StateLayout.For(architecture).Count && summary.Reads.Length == summary.NormalOutputs.Length,
                "summary covers every machine slot and conservative input dependency");
            var result = summary.NormalOutputs.Single(output => output.Slot == mapping.Result!.Slot);
            Check(result.Segments is [{ Offset: 0, Width: 32, Kind: SlotRelationKind.Result },
                { Offset: 32, Width: 32, Kind: SlotRelationKind.Havoc }], "unused high return bits are not assumed zero or preserved");
            var vector = summary.NormalOutputs.Single(output => output.Slot == (arm ? "v8" : "xmm6"));
            Check(arm ? vector.Segments is [{ Width: 64, Kind: SlotRelationKind.Preserve }, { Width: 64, Kind: SlotRelationKind.Havoc }]
                : vector.Segments is [{ Width: 128, Kind: SlotRelationKind.Preserve }], "ABI vector preservation uses the correct bit ranges");
            if (!arm)
            {
                Check(summary.NormalOutputs.Single(output => output.Slot == "ymm6_hi").Segments is [{ Kind: SlotRelationKind.Havoc }],
                    "x64 YMM high half remains volatile when XMM low half is preserved");
                Check(summary.NormalOutputs.Single(output => output.Slot == "mxcsr").Segments is
                    [{ Offset: 0, Width: 6, Kind: SlotRelationKind.Havoc }, { Offset: 6, Width: 10, Kind: SlotRelationKind.Preserve }, { Offset: 16, Width: 16, Kind: SlotRelationKind.Havoc }],
                    "MXCSR status and control fields have distinct preservation contracts");
            }
            Check(summary.World.ReadsWorld && summary.World.MayWritePrivateStack && !summary.World.WritesProgramMemory,
                "a logically pure callee may still mutate its machine stack");
            var badResult = result with { Segments = [new(0, 32, SlotRelationKind.Result), new(32, 32, SlotRelationKind.Preserve, result.Slot, 32)] };
            Check(DerivedGraphValidator.ValidateSummary(summary with { NormalOutputs = summary.NormalOutputs.Replace(result, badResult) }).Count > 0,
                "summary validator rejects invented preservation of high result bits");
            Check(DerivedGraphValidator.ValidateSummary(summary with { NormalOutputs = summary.NormalOutputs.RemoveAt(0) }).Count > 0,
                "summary validator rejects incomplete state coverage");

            var call = Decode(architecture, 0x1000, arm ? "00040094" : "E8FB0F0000");
            var nextAddress = 0x1000UL + (ulong)call.Origin.Bytes.Length;
            var ret = Decode(architecture, nextAddress, arm ? "C0035FD6" : "C3");
            var source = new FixtureSource(architecture, [call, ret]);
            var raw = RegionBuilder.Build(source, [new EntrySeed(0x1000, "raw call boundary fixture")]);
            Check(raw.Blocks.Length == 1 && raw.Blocks[0].Edges[0].Boundary?.Kind == RegionBoundaryKind.Call,
                "original region builder retains its call boundary");
            var graph = FunctionGraphBuilder.Build(source, caller, [callee]);
            var edge = graph.Entry.Edges.Single();
            Check(graph.IsClosed && graph.Blocks.Length == 2 && edge.Kind == DerivedEdgeKind.Call,
                "derived function graph discovers the caller continuation without decoding the callee body");
            Check(edge.MachineTarget == 0x2000 && edge.Continuation == nextAddress && edge.TargetBlock == 1,
                "derived summary continuation does not replace the original machine call target");
            Check(edge.Source == MirInspection.Describe(call).Successors.Single() && graph.Blocks[1].Edges.Single().Kind == DerivedEdgeKind.Return,
                "derived graph preserves the original call and return successors");
            var changed = graph with { Blocks = graph.Blocks.SetItem(0, graph.Entry with { Edges = [edge with { MachineTarget = nextAddress }] }) };
            Check(DerivedGraphValidator.Validate(changed).Count > 0, "derived graph validator rejects replacing callee target with continuation");

            var missing = FunctionGraphBuilder.Build(source, caller, []);
            Check(!missing.IsClosed && missing.Gaps.Single().Kind == RecoveryGapKind.MissingCallContract && missing.Blocks.Length == 1,
                "missing signature remains a gap instead of becoming a zero-argument call");
            var stopped = callee with { Effects = callee.Effects with { MayReturn = false, MayDiverge = true } };
            var noReturn = FunctionGraphBuilder.Build(source, caller, [stopped]);
            Check(noReturn.IsClosed && noReturn.Blocks.Length == 1 && noReturn.Entry.Edges[0].Continuation is null &&
                noReturn.Entry.Edges[0].Call!.NormalOutputs.IsEmpty, "nonreturning call does not discover a normal continuation");
            Check(noReturn.Entry.Edges[0].Call!.Reads.Length == StateLayout.For(architecture).Count,
                "nonreturning call still retains its input dependencies");
            var budget = FunctionGraphBuilder.Build(source, caller, [callee], new(MaxInstructions: 1));
            Check(!budget.IsClosed && budget.Gaps.Single().Kind == RecoveryGapKind.Budget, "continuation budget exhaustion remains a recovery gap");

            var indirect = Decode(architecture, 0x1000, arm ? "00003FD6" : "FFD0");
            var indirectReturn = Decode(architecture, 0x1000UL + (ulong)indirect.Origin.Bytes.Length, arm ? "C0035FD6" : "C3");
            var indirectSource = new FixtureSource(architecture, [indirect, indirectReturn]);
            var unbound = FunctionGraphBuilder.Build(indirectSource, caller, [callee]);
            Check(unbound.Gaps.Single().Kind == RecoveryGapKind.UnknownCallTarget, "unbound indirect call target remains unknown");
            var bound = FunctionGraphBuilder.Build(indirectSource, caller, [callee],
                new(IndirectCallTargets: ImmutableDictionary<ulong, ulong>.Empty.Add(0x1000, 0x2000)));
            Check(bound.IsClosed && bound.Entry.Edges.Single().Call!.Callee == callee,
                "explicit indirect target binding supplies a typed callee contract");
            Check(DerivedGraphValidator.Validate(bound with { Dependencies = bound.Dependencies.Where(value => !value.StartsWith("adopted-call-target:", StringComparison.Ordinal)).ToImmutableArray() }).Count > 0,
                "indirect target assumption is a required graph dependency");

            var jump = Decode(architecture, 0x1000, arm ? "00040014" : "E9FB0F0000");
            var jumpSource = new FixtureSource(architecture, [jump]);
            var unclassified = FunctionGraphBuilder.Build(jumpSource, caller, [callee]);
            Check(unclassified.Gaps.Single().Kind == RecoveryGapKind.UnclassifiedTailCall, "jumping to a function entry alone does not prove a tail call");
            var tail = FunctionGraphBuilder.Build(jumpSource, caller, [callee], new(TailCallEvidence:
                ImmutableDictionary<ulong, string>.Empty.Add(0x1000, "fixture declares restored caller state and compatible return protocol")));
            Check(tail.IsClosed && tail.Entry.Edges.Single().Kind == DerivedEdgeKind.TailCall && tail.Entry.Edges[0].Continuation is null,
                "adopted tail-call relation has no invented local continuation");
            Check(FunctionGraphBuilder.ContractDependency(callee) != FunctionGraphBuilder.ContractDependency(stopped),
                "call outcome changes invalidate the contract dependency identity");

            var unsupported = caller with { Signature = new([new(32, RecoveryScalarKind.Address)], null) };
            Check(!MachineAbi.TryDescribe(unsupported, out _, out _), "32-bit pointer is not silently accepted in a 64-bit ABI");
            var badGraph = FunctionGraphBuilder.Build(source, unsupported, []);
            Check(badGraph.Gaps.Single().Kind == RecoveryGapKind.UnsupportedInterface, "unsupported entry interface is an explicit recovery gap");
        }
        return checks + RunFrameChecks();
    }

    private static int RunFrameChecks()
    {
        var checks = 0;
        void Check(bool value, string reason) { CoreChecks.Require(value, reason); checks++; }
        foreach (var architecture in new[] { Architecture.Arm64, Architecture.X64 })
        {
            var arm = architecture == Architecture.Arm64;
            var abi = arm ? MachineAbiKind.Aapcs64 : MachineAbiKind.WindowsX64;
            var stack = arm ? "sp" : "rsp";
            var argument = arm ? "x0" : "rcx";
            var result = arm ? "x0" : "rax";
            var contract = Contract("frame", 0x1000, abi) with { Signature = new([new(64)], new(64)) };

            var conditional = Analyze((builder, local) =>
            {
                builder.StoreIf(builder.Extract(builder.Read(argument, 64), 0, 1), local, builder.Const(64, 7UL));
                builder.Write(result, builder.Load(local, 64));
            });
            Check(!IsInitialized(conditional.Frame), "conditional store does not initialize bytes on the untaken path");

            var atomic = Analyze((builder, local) =>
            {
                builder.Store(local, builder.Const(64, 7UL));
                if (arm) builder.StoreExclusive(local, builder.Const(64, 9UL), new(MemoryOrder.Relaxed, 64, 64));
                else builder.AtomicRmw(local, builder.Const(64, 9UL), builder.Const(64, 0UL), AtomicKind.Exchange);
                builder.Write(result, builder.Load(local, 64));
            });
            Check(!IsInitialized(atomic.Frame), "unmodeled atomic frame write cannot leave an old spill value available");
            Check(!atomic.Frame.FrameAccesses.Where(access => access.Load && access.Offset == -16)
                .Any(access => atomic.Frame.ForwardedLoads.Contains(access.Result!.Value)), "atomic frame mutation blocks stale forwarding");

            var overlap = Analyze((builder, local) =>
            {
                builder.Store(local, builder.Const(64, 0x1122334455667788UL));
                builder.Store(builder.Add(local, builder.Const(64, 2UL)), builder.Const(8, 0xAAUL));
                builder.Write(result, builder.Load(local, 64));
            });
            var returnValue = overlap.Ssa.Blocks.Single(block => block.Source is not null).ReturnValue!.Value;
            Check(overlap.Ssa.Definitions()[overlap.Ssa.Resolve(returnValue).Id].Payload is ImmediatePayload { Value: var bits } &&
                bits == new BigInteger(0x1122334455AA7788UL), "overlapping frame stores forward the correct byte composition");
            Check(overlap.Frame.Diagnostics.Count == 0, "valid local frame roundtrip restores the actual return protocol");

            var indirectFrame = Analyze((builder, local) =>
            {
                builder.Store(local, builder.Const(64, 1UL));
                var pointerSlot = builder.Add(local, builder.Const(64, 8UL));
                builder.Store(pointerSlot, local);
                var pointer = builder.Load(pointerSlot, 64);
                builder.Store(pointer, builder.Const(64, 2UL));
                builder.Write(result, builder.Load(local, 64));
            });
            var indirectReturn = indirectFrame.Ssa.Blocks.Single(block => block.Source is not null).ReturnValue!.Value;
            Check(indirectFrame.Ssa.Definitions()[indirectFrame.Ssa.Resolve(indirectReturn).Id].Payload is ImmediatePayload { Value: var indirectBits } &&
                indirectBits == 2, "loaded frame pointer is resolved before forwarding loads after its indirect write");

            var clobber = Analyze((builder, _) => builder.Write(arm ? "x19" : "rbx", builder.Const(64, 0UL)));
            Check(clobber.Frame.Diagnostics.Any(diagnostic => diagnostic.Code == "contract.return-preserved"),
                "constant nonvolatile-register clobber is an explicit contract contradiction");
            var wrongStack = Analyze((_, _) => { }, adjustment: 8);
            Check(wrongStack.Frame.Diagnostics.Any(diagnostic => diagnostic.Code == "contract.return-stack"),
                "known wrong return stack adjustment contradicts the adopted ABI");

            var escape = Analyze((builder, local) => builder.Write(result, local));
            Check(escape.Frame.Diagnostics.Any(diagnostic => diagnostic.Code == "frame.escape-return"),
                "returning a frame-derived address is an explicit recovery gap");

            var callee = contract with { Name = "callee", EntryAddress = 0x2000 };
            var callScratch = AnalyzeCallScratch(arm ? 32 : 40);
            const int scratchOffset = -40;
            Check(callScratch.Frame.FrameAccesses.Where(access => access.Load && access.Offset == scratchOffset)
                .All(access => !callScratch.Frame.InitializedLoads.Contains(access.Result!.Value) &&
                    !callScratch.Frame.ForwardedLoads.Contains(access.Result.Value)),
                "even a logically pure call invalidates callee scratch bytes without inventing a LocalAlloc write");
            Check(callScratch.Frame.Diagnostics.All(diagnostic => diagnostic.Code != "contract.call-stack"),
                "proper call preparation aligns callee-entry SP in both ABIs");
            var misaligned = AnalyzeCallScratch(arm ? 24 : 32);
            Check(misaligned.Frame.Diagnostics.Any(diagnostic => diagnostic.Code == "contract.call-stack"),
                "known misaligned callee-entry SP contradicts summary preconditions");

            var tailBuilder = Builder(architecture, 0x1000);
            var tail = AnalyzeInstructions([tailBuilder.Finish(MirExit.Jump(tailBuilder.Const(64, 0x2000UL)))], contract,
                [callee], new(TailCallEvidence: ImmutableDictionary<ulong, string>.Empty.Add(0x1000, "fixture adopts compatible tail transfer")));
            Check(tail.Frame.Diagnostics.Count == 0, "tail-call return protocol is checked before callee scratch invalidation");

            var narrowContract = contract with { Signature = new(Enumerable.Repeat(new RecoveryScalarType(1), arm ? 9 : 5).ToImmutableArray(), new(64)) };
            var narrow = Builder(architecture, 0x1000);
            var argumentOffset = arm ? 0UL : 40UL;
            var narrowLoad = narrow.Load(narrow.Add(narrow.Read(stack, 64), narrow.Const(64, argumentOffset)), 8);
            narrow.Write(result, narrow.Zext(narrowLoad, 64));
            var narrowResult = AnalyzeInstructions([FinishReturn(narrow, architecture)], narrowContract);
            Check(narrowResult.Frame.FrameAccesses.Where(access => access.Load && access.Offset == (long)argumentOffset)
                .All(access => !narrowResult.Frame.InitializedLoads.Contains(access.Result!.Value)),
                "narrow stack argument does not initialize unspecified upper padding bits");

            if (!arm)
            {
                var volatileStatus = Analyze((builder, _) => builder.Write("mxcsr", builder.Or(builder.Read("mxcsr", 32),
                    builder.Shl(builder.Zext(builder.Extract(builder.Read(argument, 64), 0, 1), 32), builder.Const(32, 5UL)))));
                Check(volatileStatus.Frame.Diagnostics.All(diagnostic => diagnostic.Code is not ("return.preserved" or "contract.return-preserved")),
                    "bitwise OR of a shifted low status bit preserves all higher ABI control bits");
                var changedControl = Analyze((builder, _) => builder.Write("mxcsr", builder.Or(builder.Read("mxcsr", 32),
                    builder.Shl(builder.Zext(builder.Extract(builder.Read(argument, 64), 0, 1), 32), builder.Const(32, 6UL)))));
                Check(changedControl.Frame.Diagnostics.Any(diagnostic => diagnostic.Code == "return.preserved"),
                    "bitwise proof does not assume an unknown written control bit is preserved");
                var direction = Analyze((builder, _) => builder.Write("df", builder.Const(1, 1UL)));
                Check(direction.Frame.Diagnostics.Any(diagnostic => diagnostic.Code == "contract.return-constant"),
                    "STD before return contradicts the ABI direction-flag protocol");
            }

            (RecoveryMachineSsa Ssa, RecoveryFrameAnalysis Frame) Analyze(Action<MirBuilder, Value> body, int adjustment = 0)
            {
                var builder = Builder(architecture, 0x1000);
                var entrySp = builder.Read(stack, 64);
                var local = builder.Sub(entrySp, builder.Const(64, 16UL));
                builder.Write(stack, local);
                body(builder, local);
                builder.Write(stack, builder.Add(local, builder.Const(64, (ulong)(16 + adjustment))));
                return AnalyzeInstructions([FinishReturn(builder, architecture)], contract);
            }

            (RecoveryMachineSsa Ssa, RecoveryFrameAnalysis Frame) AnalyzeCallScratch(int allocation)
            {
                var prepare = Builder(architecture, 0x1000);
                var local = prepare.Sub(prepare.Read(stack, 64), prepare.Const(64, (ulong)allocation));
                prepare.Write(stack, local);
                if (arm)
                {
                    prepare.Store(prepare.Add(local, prepare.Const(64, 16UL)), prepare.Read("x30", 64));
                    prepare.Store(prepare.Sub(local, prepare.Const(64, 8UL)), prepare.Const(64, 77UL));
                    prepare.Write("x30", prepare.Const(64, 0x1004UL));
                }
                else
                {
                    prepare.Store(local, prepare.Const(64, 77UL));
                    var callSp = prepare.Sub(local, prepare.Const(64, 8UL));
                    prepare.Store(callSp, prepare.Const(64, 0x1004UL));
                    prepare.Write(stack, callSp);
                }
                var callInstruction = prepare.Finish(MirExit.Jump(prepare.Const(64, 0x2000UL), TransferHint.Call));
                var continuation = Builder(architecture, 0x1004);
                var current = continuation.Read(stack, 64);
                continuation.Write(result, continuation.Load(arm ? continuation.Sub(current, continuation.Const(64, 8UL)) : current, 64));
                if (arm) continuation.Write("x30", continuation.Load(continuation.Add(current, continuation.Const(64, 16UL)), 64));
                continuation.Write(stack, continuation.Add(current, continuation.Const(64, (ulong)allocation)));
                return AnalyzeInstructions([callInstruction, FinishReturn(continuation, architecture)], contract, [callee]);
            }
        }
        return checks;

        static bool IsInitialized(RecoveryFrameAnalysis analysis) => analysis.FrameAccesses
            .Where(access => access.Load && access.Offset == -16).Any(access => analysis.InitializedLoads.Contains(access.Result!.Value));
    }

    private static (RecoveryMachineSsa Ssa, RecoveryFrameAnalysis Frame) AnalyzeInstructions(
        IEnumerable<MirInstruction> instructions, FunctionContract contract, FunctionContract[]? callees = null, FunctionGraphOptions? options = null)
    {
        var graph = FunctionGraphBuilder.Build(new FixtureSource(MachineAbi.ArchitectureFor(contract.Abi), instructions),
            contract, callees ?? [], options);
        CoreChecks.Require(graph.IsClosed, "frame analysis fixture has a closed derived graph");
        var ssa = new RecoveryMachineSsa(graph);
        CoreChecks.Require(ssa.Normalize(64), "frame analysis fixture normalizes its machine SSA");
        return (ssa, RecoveryFrameAnalysis.Run(ssa, new(AssumeNormalExecution: true, AssumePrivateValidFrames: true)));
    }

    private static MirBuilder Builder(Architecture architecture, ulong address) => new(architecture,
        new(ImageId, address, (long)address, new byte[4]), "fixture.frame");

    private static MirInstruction FinishReturn(MirBuilder builder, Architecture architecture)
    {
        if (architecture == Architecture.Arm64) return builder.Finish(MirExit.Jump(builder.Read("x30", 64), TransferHint.Return));
        var stack = builder.Read("rsp", 64);
        var target = builder.Load(stack, 64);
        builder.Write("rsp", builder.Add(stack, builder.Const(64, 8UL)));
        return builder.Finish(MirExit.Jump(target, TransferHint.Return));
    }

    private static FunctionContract Contract(string name, ulong entry, MachineAbiKind abi) => new(name, entry,
        new([new(32), new(32)], new(32)), abi,
        new(false, false, false, false, true, false, false),
        ["fixture adopts the stated scalar ABI"], new(true, true));

    internal static MirInstruction Decode(Architecture architecture, ulong address, string hex)
    {
        var bytes = Convert.FromHexString(hex);
        var origin = new InstructionOrigin(ImageId, address, checked((long)address), bytes);
        LiftResult lifted;
        if (architecture == Architecture.Arm64) lifted = Arm64Lifter.Lift(origin);
        else
        {
            var decoder = Decoder.Create(64, new ByteArrayCodeReader(bytes));
            decoder.IP = address;
            lifted = X64Lifter.Lift(origin, decoder.Decode());
        }
        return lifted.Ir ?? throw new InvalidDataException(lifted.Reason);
    }

    private sealed class FixtureSource(Architecture architecture, IEnumerable<MirInstruction> instructions) : IRegionInstructionSource
    {
        private readonly Dictionary<ulong, MirInstruction> byAddress = instructions.ToDictionary(instruction => instruction.Origin.Address);
        public string ImageId => RecoveryGraphChecks.ImageId;
        public Architecture Architecture => architecture;
        public InstructionDecodeResult Decode(ulong address) => byAddress.TryGetValue(address, out var instruction)
            ? InstructionDecodeResult.Supported(instruction) : InstructionDecodeResult.Stopped(InstructionDecodeFailure.Unmapped, "fixture has no bytes at this address");
    }
}
