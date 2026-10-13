using System.Collections.Immutable;
using Cpp2CS.Ir;

namespace Cpp2CS.Native;

public static class StateSsaConverter
{
    public static NativeRegion Convert(RegionRevision source)
    {
        var errors = RegionValidator.Validate(source);
        if (errors.Count != 0) throw new InvalidOperationException(string.Join("; ", errors));
        var layout = StateLayout.For(source.Architecture).OrderBy(pair => pair.Key, StringComparer.Ordinal).ToArray();
        var nextValue = 0;
        NativeValue Fresh(NativeType type) => new(new(nextValue++), type);
        var blocks = ImmutableArray.CreateBuilder<NativeBlock>();
        foreach (var block in source.Blocks)
        {
            var parameters = ImmutableArray.CreateBuilder<BlockParameter>();
            var slots = ImmutableDictionary.CreateBuilder<string, NativeValue>(StringComparer.Ordinal);
            foreach (var (name, width) in layout)
            {
                var value = Fresh(new BitsType(width));
                parameters.Add(new(value, name));
                slots.Add(name, value);
            }
            var world = Fresh(WorldType.Instance);
            parameters.Add(new(world, null));
            var current = new StateMap(slots.ToImmutable(), world);
            var initial = current;
            var nodes = ImmutableArray.CreateBuilder<NativeNode>();
            var steps = ImmutableArray.CreateBuilder<NativeStep>();
            var values = new Dictionary<int, NativeValue>();
            if (block.Instruction is { } instruction)
            {
                for (var index = 0; index < instruction.Operations.Length; index++)
                {
                    var operation = instruction.Operations[index];
                    var before = current;
                    NativeValue? result = null;
                    int? nodeIndex = null;
                    if (operation.Code == OpCode.ReadSlot)
                    {
                        result = current.Slots[operation.Slot!];
                        values.Add(operation.Result!.Value.Id, result.Value);
                    }
                    else if (operation.Code == OpCode.WriteSlot)
                    {
                        current = current with { Slots = current.Slots.SetItem(operation.Slot!, values[operation.Inputs[0].Id]) };
                    }
                    else
                    {
                        if (operation.Result is { } originalResult)
                        {
                            result = Fresh(new BitsType(originalResult.Width));
                            values.Add(originalResult.Id, result.Value);
                        }
                        WorldFlow? flow = null;
                        if (operation.Flow is not null)
                        {
                            var output = Fresh(WorldType.Instance);
                            flow = new(current.World, output);
                            current = current with { World = output };
                        }
                        nodeIndex = nodes.Count;
                        nodes.Add(new(operation.Code, result,
                            operation.Inputs.Select(value => values[value.Id]).ToImmutableArray(),
                            operation.Payload, flow, new(instruction.Origin, index)));
                    }
                    steps.Add(new(index, nodeIndex, result, before, current));
                }
            }
            NativeDestination Destination(SuccessorDestination destination) => destination switch
            {
                AddressDestination address => new NativeAddressDestination(address.Address),
                ValueDestination target => new NativeValueDestination(values[target.Target.Id]),
                ExceptionDestination trap => new NativeExceptionDestination(trap.Boundary),
                _ => throw new InvalidOperationException("Unknown MIR successor destination")
            };
            var arguments = layout.Select(pair => current.Slots[pair.Key]).Append(current.World).ToImmutableArray();
            var edges = block.Edges.Select(edge => new NativeEdge(edge, Destination(edge.Successor.Destination),
                edge.Successor.Condition is { } condition ? new NativeCondition(values[condition.Value.Id], condition.RequiredValue) : null,
                current, arguments)).ToImmutableArray();
            blocks.Add(new(block, parameters.ToImmutable(), nodes.ToImmutable(), steps.ToImmutable(), initial, current, edges));
        }
        var region = new NativeRegion(source, blocks.ToImmutable());
        var nativeErrors = NativeValidator.Validate(region);
        if (nativeErrors.Count != 0) throw new InvalidOperationException(string.Join("; ", nativeErrors));
        return region;
    }
}
