using System.Collections.Immutable;
using Cpp2CS.Ir;
using Cpp2CS.Native;

namespace Cpp2CS.Validation;

public static class StateSsaChecks
{
    public static int Run()
    {
        var checks = 0;
        void Check(bool condition, string reason) { CoreChecks.Require(condition, reason); checks++; }
        foreach (var architecture in Enum.GetValues<Architecture>())
        {
            var source = Fixture(architecture);
            var native = StateSsaConverter.Convert(source);
            var layout = StateLayout.For(architecture);
            var block = native.Blocks[0];
            var counter = architecture == Architecture.Arm64 ? "x9" : "rax";
            var stack = architecture == Architecture.Arm64 ? "sp" : "rsp";
            Check(NativeValidator.Validate(native).Count == 0, "full state SSA validates a multi-entry irreducible graph");
            Check(native.Blocks.All(item => item.Parameters.Length == layout.Count + 1), "every block has all canonical slots and World");
            Check(native.Blocks.All(item => item.Nodes.All(node => node.Code is not (OpCode.ReadSlot or OpCode.WriteSlot))),
                "state SSA eliminates all slot read and write nodes");
            Check(block.Steps.Length == block.Source.Instruction!.Operations.Length, "all original operation phases remain queryable");
            var reads = block.Source.Instruction.Operations.Select((operation, index) => (operation, index))
                .Where(item => item.operation.Code == OpCode.ReadSlot && item.operation.Slot == counter).ToArray();
            Check(block.Steps[reads[0].index].Result == block.InitialState.Slots[counter] &&
                block.Steps[reads[1].index].Result == block.FinalState.Slots[counter] &&
                block.FinalState.Slots[counter] != block.InitialState.Slots[counter], "read after write uses the new reaching definition");
            var choices = block.Nodes.Where(node => node.Code == OpCode.Undefined).ToArray();
            Check(choices.Length == 2 && choices[0].Result != choices[1].Result && choices[0].Source != choices[1].Source,
                "equal choice descriptions retain distinct producing identities");
            Check(choices[1].Flow!.Input == choices[0].Flow!.Output, "unused choices remain ordered by World");
            Check(block.Nodes.Single(node => node.Code == OpCode.LoadIf).Flow!.Input == choices[1].Flow!.Output,
                "conditional memory remains after the original choices");
            Check(block.Capabilities!.Obligations.Any(item => item.Kind == ObligationKind.FaultDelivery), "fault obligations survive conversion");
            Check(!block.Capabilities.FaultDeliveryModeled && !block.Capabilities.ConcurrentExecutionsVerified,
                "valid SSA does not upgrade semantic capabilities");
            Check(native.Blocks[3].Edges.Length == 2 && native.Blocks[3].Edges[0].Target == native.Blocks[3].Edges[1].Target &&
                native.Blocks[3].Edges[0].Id != native.Blocks[3].Edges[1].Id, "parallel successors retain independent edge identity");
            Check(native.Blocks[3].Edges.Select(edge => edge.Condition!.RequiredValue).SequenceEqual(new[] { true, false }),
                "parallel edge predicates remain distinct");
            Check(native.Blocks[4].Source.Stop is not null && native.Blocks[4].Nodes.IsEmpty &&
                native.Blocks[4].FinalState == native.Blocks[4].InitialState, "unsupported block preserves an explicit unchanged analysis boundary");
            Check(native.Blocks[5].Edges[0] is { Target: null, Destination: NativeValueDestination } &&
                native.Blocks[5].Edges[0].Arguments.Length == layout.Count + 1, "indirect transfer retains target and full output state");
            Check(native.Blocks[6].Edges[0].Destination is NativeExceptionDestination &&
                native.Blocks[6].Capabilities!.Support == SupportClass.ExceptionBoundaryOnly, "exception boundary is not a normal successor");
            Check(native.Blocks.SelectMany(item => item.Parameters.Select(parameter => parameter.Value.Id))
                .Distinct().Count() == native.Blocks.Length * (layout.Count + 1), "parameter IDs are unique across region blocks");
            var partial = native.Blocks[1];
            Check(partial.Nodes.Any(node => node.Code == OpCode.Concat) && partial.Nodes.Any(node => node.Code == OpCode.Extract),
                "partial vector writes preserve bit operations");
            Check(block.FinalState.Slots[stack] == block.InitialState.Slots[stack], "unused stack state is preserved at all exits");

            void Reject(NativeRegion candidate, string reason) => Check(NativeValidator.Validate(candidate).Count != 0, reason);
            void RejectBlock(NativeBlock candidate, string reason) => Reject(native with { Blocks = native.Blocks.SetItem(0, candidate) }, reason);
            void RejectNode(int index, NativeNode candidate, string reason) => RejectBlock(block with { Nodes = block.Nodes.SetItem(index, candidate) }, reason);
            void RejectStep(int index, NativeStep candidate, string reason) => RejectBlock(block with { Steps = block.Steps.SetItem(index, candidate) }, reason);
            void RejectEdge(NativeEdge candidate, string reason) => RejectBlock(block with { Edges = block.Edges.SetItem(0, candidate) }, reason);
            Reject(native with { Blocks = native.Blocks.RemoveAt(0) }, "missing block is rejected");
            Reject(native with { Blocks = native.Blocks.SetItem(1, block) }, "duplicate block is rejected");
            Reject(native with { Blocks = default }, "missing block collection is rejected");
            RejectBlock(block with { Parameters = block.Parameters.RemoveAt(0) }, "missing canonical parameter is rejected");
            RejectBlock(block with { Parameters = block.Parameters.SetItem(1, block.Parameters[1] with { Value = block.Parameters[0].Value }) },
                "duplicate parameter value is rejected");
            RejectBlock(block with { Parameters = block.Parameters.SetItem(0, block.Parameters[0] with { Value = native.Blocks[1].Parameters[0].Value }) },
                "duplicate value across blocks is rejected");
            RejectBlock(block with { Parameters = block.Parameters.SetItem(0, block.Parameters[0] with { Slot = "unknown-slot" }) },
                "unknown slot parameter is rejected");
            RejectBlock(block with { Parameters = block.Parameters.SetItem(0, block.Parameters[0] with
                { Value = block.Parameters[0].Value with { Type = new BitsType(4097) } }) }, "incorrect slot width is rejected");
            RejectBlock(block with { Parameters = block.Parameters.SetItem(block.Parameters.Length - 1,
                block.Parameters[^1] with { Value = block.Parameters[^1].Value with { Type = new BitsType(1) } }) }, "bits cannot substitute World");
            RejectBlock(block with { InitialState = block.InitialState with { Slots = block.InitialState.Slots.Remove(stack) } },
                "incomplete boundary state is rejected");
            RejectBlock(block with { FinalState = block.InitialState }, "lost final slot write is rejected");
            RejectBlock(block with { Nodes = block.Nodes.RemoveAt(0) }, "removed node is rejected");
            var addIndex = Array.FindIndex(block.Nodes.ToArray(), node => node.Code == OpCode.Add);
            var add = block.Nodes[addIndex];
            RejectNode(addIndex, add with { Code = OpCode.Sub }, "changed node semantics is rejected");
            RejectNode(addIndex, add with { Payload = new ImmediatePayload(1) }, "changed node payload is rejected");
            RejectNode(addIndex, add with { Inputs = [] }, "wrong node arity is rejected");
            RejectNode(addIndex, add with { Inputs = add.Inputs.SetItem(0, native.Blocks[1].InitialState.Slots[counter]) },
                "cross-block direct value reference is rejected");
            RejectNode(addIndex, add with { Inputs = add.Inputs.SetItem(0, add.Result!.Value) }, "self reference before definition is rejected");
            RejectNode(addIndex, add with { Inputs = add.Inputs.SetItem(0, block.InitialState.World) }, "World cannot substitute bit input");
            RejectNode(addIndex, add with { Result = add.Result!.Value with { Type = new BitsType(32) } }, "wrong result width is rejected");
            RejectNode(addIndex, add with { Flow = new(block.InitialState.World, new(new(999999), WorldType.Instance)) },
                "pure node cannot fabricate World order");
            var choiceIndex = Array.FindIndex(block.Nodes.ToArray(), node => node.Code == OpCode.Undefined);
            RejectNode(choiceIndex, block.Nodes[choiceIndex] with { Flow = null }, "choice cannot lose its World dependency");
            RejectNode(choiceIndex, block.Nodes[choiceIndex] with { Flow = new(block.InitialState.World, block.InitialState.World) },
                "effect must produce a fresh World value");
            RejectNode(choiceIndex + 1, block.Nodes[choiceIndex + 1] with { Flow = block.Nodes[choiceIndex].Flow },
                "choice order cannot be collapsed");
            RejectNode(addIndex, add with { Source = add.Source with { OperationIndex = add.Source.OperationIndex + 1 } },
                "false node provenance is rejected");
            RejectStep(reads[0].index, block.Steps[reads[0].index] with { NodeIndex = 0 }, "slot read cannot become a duplicate execution node");
            RejectStep(reads[1].index, block.Steps[reads[1].index] with { Result = block.InitialState.Slots[counter] },
                "stale read after write is rejected");
            RejectStep(0, block.Steps[0] with { OperationIndex = 1 }, "reordered MIR phases are rejected");
            RejectStep(0, block.Steps[0] with { Before = block.FinalState }, "future state at a stop prefix is rejected");
            var writeIndex = Array.FindIndex(block.Source.Instruction.Operations.ToArray(), operation => operation.Code == OpCode.WriteSlot);
            RejectStep(writeIndex, block.Steps[writeIndex] with { After = block.Steps[writeIndex].Before },
                "write phase must preserve its new slot definition");
            RejectEdge(block.Edges[0] with { Arguments = block.Edges[0].Arguments.RemoveAt(0) }, "wrong edge arity is rejected");
            RejectEdge(block.Edges[0] with { Arguments = block.Edges[0].Arguments.SetItem(0, block.InitialState.World) },
                "wrong edge argument type is rejected");
            RejectEdge(block.Edges[0] with { Arguments = block.Edges[0].Arguments.SetItem(layout.Count, block.InitialState.World) },
                "stale World at edge is rejected");
            RejectEdge(block.Edges[0] with { Condition = block.Edges[0].Condition! with { RequiredValue = false } },
                "changed branch polarity is rejected");
            RejectEdge(block.Edges[0] with { Destination = new NativeAddressDestination(0x9999) }, "changed edge target is rejected");
            RejectBlock(block with { Edges = block.Edges.RemoveAt(1) }, "dropped successor is rejected");
        }
        return checks;
    }

    private static RegionRevision Fixture(Architecture architecture)
    {
        const string image = "fixture:state-ssa";
        MirBuilder Builder(int index) => new(architecture, new(image, 0x1000UL + (ulong)index * 4,
            index * 4, architecture == Architecture.Arm64 ? new byte[4] : new byte[] { 0x90 }), "fixture.ssa");
        var counter = architecture == Architecture.Arm64 ? "x9" : "rax";
        var flag = architecture == Architecture.Arm64 ? "z" : "zf";
        var vector = architecture == Architecture.Arm64 ? "v8" : "xmm8";
        var builder = Builder(0);
        builder.Write(counter, builder.Add(builder.Read(counter, 64), builder.Const(64, 1)));
        builder.Read(counter, 64);
        builder.Undefined(1, "architectural choice");
        builder.Undefined(1, "architectural choice");
        builder.LoadIf(builder.Const(1, 0), builder.Const(64, 0x8000), 8);
        var first = builder.Finish(MirExit.Branch(builder.Read(flag, 1), builder.Const(64, 0x1004), builder.Const(64, 0x1008)));
        builder = Builder(1);
        builder.Write(vector, builder.Concat(builder.Extract(builder.Read(vector, 128), 64, 64), builder.Const(64, 7)));
        var second = builder.Finish(MirExit.Next(0x1008));
        builder = Builder(2);
        var third = builder.Finish(MirExit.Branch(builder.Read(flag, 1), builder.Const(64, 0x1004), builder.Const(64, 0x100c)));
        builder = Builder(3);
        var fourth = builder.Finish(MirExit.Branch(builder.Read(flag, 1), builder.Const(64, 0x1010), builder.Const(64, 0x1010)));
        builder = Builder(5);
        var indirect = builder.Finish(MirExit.Jump(builder.Read(counter, 64)));
        builder = Builder(6);
        var trap = builder.Finish(architecture == Architecture.Arm64
            ? MirExit.Trap(ExceptionKind.ArmBreakpoint, "fixture trap", 0x1018, 0)
            : MirExit.Trap(ExceptionKind.X64InvalidOpcode, "fixture trap", 0x1018));
        MirInstruction?[] instructions = [first, second, third, fourth, null, indirect, trap];
        int?[][] targets = [[1, 2], [2], [1, 3], [4, 4], [], [null], [null]];
        var edgeId = 0;
        var blocks = ImmutableArray.CreateBuilder<RegionBlock>();
        for (var index = 0; index < instructions.Length; index++)
        {
            var instruction = instructions[index];
            var edges = ImmutableArray.CreateBuilder<RegionEdge>();
            if (instruction is not null)
            {
                var successors = MirInspection.Describe(instruction).Successors;
                for (var successorIndex = 0; successorIndex < successors.Length; successorIndex++)
                {
                    var target = targets[index][successorIndex];
                    edges.Add(new(new(edgeId++), new(index), target is { } id ? new BlockId(id) : null, successors[successorIndex],
                        target is not null ? null : new(index == 6 ? RegionBoundaryKind.ExceptionBoundary : RegionBoundaryKind.IndirectTarget,
                            "explicit analysis boundary")));
                }
            }
            blocks.Add(new(new(index), 0x1000UL + (ulong)index * 4, instruction,
                instruction is null ? new(RegionBoundaryKind.Unsupported, "fixture unsupported") : null, edges.ToImmutable()));
        }
        return new("fixture-ssa-1", image, architecture, MachineProfile.For(architecture).Id, MirJson.SemanticsVersion,
            [new(new(0x1000, "synthetic irreducible graph"), new(0)), new(new(0x1014, "synthetic indirect entry"), new(5)),
                new(new(0x1018, "synthetic trap entry"), new(6))], blocks.ToImmutable());
    }
}
