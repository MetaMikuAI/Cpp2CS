using System.Collections.Immutable;
using Cpp2CS.Ir;

namespace Cpp2CS.Native;

// 复核确定的变换记录，另查 use-def 与支配关系；规则等价由专项差分验证。
public static class NativeNormalizationValidator
{
    public static IReadOnlyList<string> Validate(NativeNormalizationResult result)
    {
        var errors = NativeValidator.Validate(result.Original).ToList();
        if (errors.Count != 0) return errors;
        if (result.RuleVersion != NativeNormalizer.RuleVersion || result.MaxRounds is < 1 or > 4096)
            return ["unknown normalization rules or invalid round budget"];
        var expected = NativeNormalizer.Run(result.Original, result.MaxRounds);
        if (result.Revision != expected.Revision || result.ReachedFixedPoint != expected.ReachedFixedPoint || result.Statistics != expected.Statistics)
            errors.Add("normalization revision, completion or statistics mismatch");
        if (result.Rewrites.IsDefault || result.Rewrites.Length != expected.Rewrites.Length ||
            !result.Rewrites.Zip(expected.Rewrites).All(pair => SameRewrite(pair.First, pair.Second)))
            errors.Add("normalization rewrite evidence mismatch");
        if (!SameRegion(result.Region, expected.Region)) errors.Add("normalized graph differs from checked rewrite replay");
        if (errors.Count == 0) errors.AddRange(ValidateGraph(result.Region));
        return errors;
    }

    internal static IReadOnlyList<string> ValidateGraph(NativeRegion region)
    {
        List<string> errors = [];
        var definitions = new Dictionary<ValueId, (NativeType Type, BlockId Block, int Stage)>();
        foreach (var block in region.Blocks)
        {
            foreach (var parameter in block.Parameters) Define(parameter.Value, block.Id, -1);
            foreach (var node in block.Nodes)
            {
                var operation = new Operation(node.Code,
                    node.Result is { Type: BitsType resultBits } value ? new Value(value.Id.Id, resultBits.Width) : null,
                    node.Inputs.Select(v => new Value(v.Id.Id, v.Type is BitsType bits ? bits.Width : 0)).ToImmutableArray(), node.Payload);
                errors.AddRange(MirValidator.ValidateOperation(region.Source.Architecture, operation));
                if (OperationSpecs.For(node.Code).HasStateFlow != (node.Flow is not null)) errors.Add("node effect-flow contract mismatch");
                if (node.Result is { } result) Define(result, block.Id, node.Source.OperationIndex);
                if (node.Flow is { } flow) Define(flow.Output, block.Id, node.Source.OperationIndex);
            }
        }
        var dominance = new NativeDominance(region);
        var layout = StateLayout.For(region.Source.Architecture);
        var blocks = region.Blocks.ToDictionary(b => b.Id);
        foreach (var block in region.Blocks)
        {
            State(block.InitialState, block.Id, -1);
            var currentWorld = block.InitialState.World;
            foreach (var step in block.Steps)
            {
                State(step.Before, block.Id, step.OperationIndex - 1);
                if (step.Before.World != currentWorld) errors.Add("disconnected stage world input");
                if (step.NodeIndex is { } index)
                {
                    var node = block.Nodes[index];
                    foreach (var input in node.Inputs) Use(input, block.Id, step.OperationIndex - 1);
                    if (node.Source.OperationIndex != step.OperationIndex) errors.Add("node moved across MIR stages");
                    if (node.Flow is { } flow)
                    {
                        Use(flow.Input, block.Id, step.OperationIndex - 1);
                        if (flow.Input != currentWorld) errors.Add("effect world order mismatch");
                        currentWorld = flow.Output;
                    }
                }
                if (step.Result is { } value) Use(value, block.Id, step.OperationIndex);
                State(step.After, block.Id, step.OperationIndex);
                if (step.After.World != currentWorld) errors.Add("disconnected stage world output");
            }
            State(block.FinalState, block.Id, int.MaxValue);
            if (block.FinalState.World != currentWorld) errors.Add("final world differs from last effect");
            foreach (var edge in block.Edges)
            {
                State(edge.State, block.Id, int.MaxValue);
                if (edge.Condition is { } condition) Use(condition.Value, block.Id, int.MaxValue);
                if (edge.Destination is NativeValueDestination destination) Use(destination.Target, block.Id, int.MaxValue);
                foreach (var argument in edge.Arguments) Use(argument, block.Id, int.MaxValue);
                if (edge.Target is { } target)
                {
                    var parameters = blocks[target].Parameters;
                    if (parameters.Length != edge.Arguments.Length) errors.Add("edge argument count differs from reduced parameters");
                    else if (parameters.Where((p, i) => p.Value.Type != edge.Arguments[i].Type).Any())
                        errors.Add("edge argument type differs from parameter");
                }
            }
        }
        return errors;

        void Define(NativeValue value, BlockId block, int stage)
        {
            if (value.Id.Id < 0 || value.Type is BitsType { Width: < 1 or > 4096 } ||
                !definitions.TryAdd(value.Id, (value.Type, block, stage))) errors.Add("invalid or duplicate normalized value definition");
        }
        void Use(NativeValue value, BlockId block, int stage)
        {
            if (!definitions.TryGetValue(value.Id, out var definition) || definition.Type != value.Type ||
                (definition.Block == block ? definition.Stage > stage : !dominance.Dominates(definition.Block, block)))
                errors.Add($"value {value.Id.Id} does not dominate block {block.Id} stage {stage}");
        }
        void State(StateMap state, BlockId block, int stage)
        {
            if (state.World.Type is not WorldType || state.Slots.Count != layout.Count) errors.Add("incomplete normalized state");
            Use(state.World, block, stage);
            foreach (var (name, width) in layout)
            {
                if (!state.Slots.TryGetValue(name, out var value) || value.Type != new BitsType(width)) errors.Add("normalized state slot type mismatch");
                else Use(value, block, stage);
            }
        }
    }

    private static bool SameRegion(NativeRegion actual, NativeRegion expected) => actual.Source == expected.Source &&
        !actual.Blocks.IsDefault && actual.Blocks.Length == expected.Blocks.Length &&
        actual.Blocks.Zip(expected.Blocks).All(pair => SameBlock(pair.First, pair.Second));

    private static bool SameBlock(NativeBlock a, NativeBlock b) => a.Source == b.Source &&
        !a.Parameters.IsDefault && a.Parameters.SequenceEqual(b.Parameters) &&
        !a.Nodes.IsDefault && a.Nodes.Length == b.Nodes.Length && a.Nodes.Zip(b.Nodes).All(p => SameNode(p.First, p.Second)) &&
        !a.Steps.IsDefault && a.Steps.Length == b.Steps.Length && a.Steps.Zip(b.Steps).All(p =>
            p.First.OperationIndex == p.Second.OperationIndex && p.First.NodeIndex == p.Second.NodeIndex && p.First.Result == p.Second.Result &&
            SameState(p.First.Before, p.Second.Before) && SameState(p.First.After, p.Second.After)) &&
        SameState(a.InitialState, b.InitialState) && SameState(a.FinalState, b.FinalState) &&
        !a.Edges.IsDefault && a.Edges.Length == b.Edges.Length && a.Edges.Zip(b.Edges).All(p =>
            p.First.Source == p.Second.Source && p.First.Destination == p.Second.Destination && p.First.Condition == p.Second.Condition &&
            !p.First.Arguments.IsDefault && p.First.Arguments.SequenceEqual(p.Second.Arguments) && SameState(p.First.State, p.Second.State));

    private static bool SameState(StateMap a, StateMap b) => a.World == b.World && a.Slots.Count == b.Slots.Count &&
        a.Slots.All(p => b.Slots.TryGetValue(p.Key, out var value) && value == p.Value);

    private static bool SameNode(NativeNode? a, NativeNode? b) => a is null || b is null ? a == b :
        a.Code == b.Code && a.Result == b.Result && a.Payload == b.Payload && a.Flow == b.Flow && a.Source == b.Source &&
        !a.Inputs.IsDefault && a.Inputs.SequenceEqual(b.Inputs);

    private static bool SameRewrite(NativeRewrite a, NativeRewrite b) => a.Round == b.Round && a.Block == b.Block &&
        a.Rule == b.Rule && a.Value == b.Value && a.Alias == b.Alias && SameNode(a.Before, b.Before) && SameNode(a.After, b.After);
}
