using Cpp2CS.Ir;

namespace Cpp2CS.Native;

// N1 验证机械转换及其来源映射；后续归约需另有变换合同。
public static class NativeValidator
{
    public static IReadOnlyList<string> Validate(NativeRegion region)
    {
        List<string> errors = [];
        if (region.Source is null) return ["missing source region"];
        errors.AddRange(RegionValidator.Validate(region.Source));
        if (errors.Count != 0) return errors;
        if (region.Blocks.IsDefault || region.Blocks.Length != region.Source.Blocks.Length)
            return ["native block set differs from source"];
        var layout = StateLayout.For(region.Source.Architecture).OrderBy(pair => pair.Key, StringComparer.Ordinal).ToArray();
        var sourceBlocks = region.Source.Blocks.ToDictionary(block => block.Id);
        var blockIds = new HashSet<BlockId>();
        var definitions = new HashSet<ValueId>();
        foreach (var block in region.Blocks)
        {
            if (block is null || block.Source is null || !sourceBlocks.TryGetValue(block.Id, out var source) ||
                source != block.Source || !blockIds.Add(block.Id))
            {
                errors.Add("native block source or identity mismatch");
                continue;
            }
            ValidateBlock(block);
        }
        return errors;

        void ValidateBlock(NativeBlock block)
        {
            bool Require(bool condition, string detail)
            {
                if (!condition) errors.Add($"block {block.Id.Id}: {detail}");
                return condition;
            }
            var locals = new Dictionary<ValueId, NativeType>();
            bool Define(NativeValue value, NativeType type) =>
                Require(value.Id.Id >= 0 && value.Type == type && definitions.Add(value.Id) && locals.TryAdd(value.Id, value.Type),
                    "duplicate definition or invalid result type");
            bool Use(NativeValue value) => Require(locals.TryGetValue(value.Id, out var type) && type == value.Type,
                "value is not locally defined before use");
            bool State(StateMap? state, StateMap expected)
            {
                if (state is null || state.Slots is null || state.Slots.Count != layout.Length)
                    return Require(false, "incomplete state map");
                if (!Require(state.World == expected.World, "state map world mismatch") || !Use(state.World)) return false;
                foreach (var pair in expected.Slots)
                    if (!Require(state.Slots.TryGetValue(pair.Key, out var value) && value == pair.Value,
                            $"state map slot mismatch: {pair.Key}") || !Use(state.Slots[pair.Key])) return false;
                return true;
            }
            if (!Require(!block.Parameters.IsDefault && block.Parameters.Length == layout.Length + 1 &&
                    !block.Nodes.IsDefault && !block.Steps.IsDefault && !block.Edges.IsDefault, "missing native collections")) return;
            var slotValues = System.Collections.Immutable.ImmutableDictionary.CreateBuilder<string, NativeValue>(StringComparer.Ordinal);
            for (var index = 0; index < layout.Length; index++)
            {
                var parameter = block.Parameters[index];
                if (!Require(parameter is not null && parameter.Slot == layout[index].Key, "canonical slot parameter order mismatch") ||
                    !Define(parameter!.Value, new BitsType(layout[index].Value))) return;
                slotValues.Add(layout[index].Key, parameter.Value);
            }
            var worldParameter = block.Parameters[^1];
            if (!Require(worldParameter is not null && worldParameter.Slot is null, "missing world parameter") ||
                !Define(worldParameter!.Value, WorldType.Instance)) return;
            var current = new StateMap(slotValues.ToImmutable(), worldParameter.Value);
            if (!State(block.InitialState, current)) return;
            var instruction = block.Source.Instruction;
            if (!Require(block.Steps.Length == (instruction?.Operations.Length ?? 0), "MIR phase count mismatch")) return;
            var values = new Dictionary<int, NativeValue>();
            var nextNode = 0;
            for (var index = 0; index < block.Steps.Length; index++)
            {
                var operation = instruction!.Operations[index];
                var step = block.Steps[index];
                if (!Require(step is not null && step.OperationIndex == index, "MIR phase identity mismatch") ||
                    !State(step!.Before, current)) return;
                NativeValue? result = null;
                if (operation.Code is OpCode.ReadSlot or OpCode.WriteSlot)
                {
                    if (!Require(step.NodeIndex is null, "slot operation cannot remain an execution node")) return;
                    if (operation.Code == OpCode.ReadSlot)
                    {
                        result = current.Slots[operation.Slot!];
                        values.Add(operation.Result!.Value.Id, result.Value);
                    }
                    else current = current with { Slots = current.Slots.SetItem(operation.Slot!, values[operation.Inputs[0].Id]) };
                }
                else
                {
                    if (!Require(step.NodeIndex == nextNode && nextNode < block.Nodes.Length, "missing or reordered native node")) return;
                    var node = block.Nodes[nextNode++];
                    if (!Require(node is not null && node.Code == operation.Code && node.Payload == operation.Payload &&
                            node.Source == new MirOperationLocation(instruction.Origin, index), "node semantics or provenance differs from MIR")) return;
                    if (!Require(!node!.Inputs.IsDefault && node.Inputs.Length == operation.Inputs.Length,
                            "node input arity mismatch")) return;
                    for (var inputIndex = 0; inputIndex < operation.Inputs.Length; inputIndex++)
                        if (!Use(node.Inputs[inputIndex]) || !Require(node.Inputs[inputIndex] == values[operation.Inputs[inputIndex].Id],
                                "node input differs from MIR reaching value")) return;
                    if (!Require(node.Result.HasValue == operation.Result.HasValue, "node result contract mismatch")) return;
                    if (operation.Result is { } mirResult)
                    {
                        result = node.Result!.Value;
                        if (!Define(result.Value, new BitsType(mirResult.Width))) return;
                        values.Add(mirResult.Id, result.Value);
                    }
                    if (operation.Flow is null)
                    {
                        if (!Require(node.Flow is null, "pure node has a world flow")) return;
                    }
                    else
                    {
                        if (!Require(node.Flow is not null && node.Flow.Input == current.World, "broken world order") ||
                            !Use(node.Flow!.Input) || !Define(node.Flow.Output, WorldType.Instance)) return;
                        current = current with { World = node.Flow.Output };
                    }
                }
                if (!Require(step.Result == result, "MIR phase result mismatch") || !State(step.After, current)) return;
            }
            if (!Require(nextNode == block.Nodes.Length, "extra native nodes") || !State(block.FinalState, current)) return;
            if (!Require(block.Edges.Length == block.Source.Edges.Length, "native successor count mismatch")) return;
            for (var index = 0; index < block.Edges.Length; index++)
            {
                var edge = block.Edges[index];
                var source = block.Source.Edges[index];
                if (!Require(edge is not null && edge.Source == source, "edge identity or boundary differs from source") ||
                    !State(edge!.State, current)) return;
                var condition = source.Successor.Condition is { } predicate
                    ? new NativeCondition(values[predicate.Value.Id], predicate.RequiredValue) : null;
                if (!Require(edge.Condition == condition, "edge predicate differs from MIR")) return;
                if (edge.Condition is { } nativeCondition && !Use(nativeCondition.Value)) return;
                NativeDestination destination = source.Successor.Destination switch
                {
                    AddressDestination address => new NativeAddressDestination(address.Address),
                    ValueDestination target => new NativeValueDestination(values[target.Target.Id]),
                    ExceptionDestination trap => new NativeExceptionDestination(trap.Boundary),
                    _ => throw new InvalidOperationException("Unknown MIR successor destination")
                };
                if (!Require(edge.Destination == destination, "edge destination differs from MIR")) return;
                if (edge.Destination is NativeValueDestination targetValue && !Use(targetValue.Target)) return;
                if (!Require(!edge.Arguments.IsDefault && edge.Arguments.Length == layout.Length + 1,
                        "edge argument arity mismatch")) return;
                for (var argumentIndex = 0; argumentIndex < layout.Length; argumentIndex++)
                    if (!Use(edge.Arguments[argumentIndex]) ||
                        !Require(edge.Arguments[argumentIndex] == current.Slots[layout[argumentIndex].Key], "edge slot argument mismatch")) return;
                if (!Require(edge.Arguments[^1] == current.World, "edge world argument mismatch") || !Use(edge.Arguments[^1])) return;
            }
        }
    }
}
