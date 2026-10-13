using System.Collections.Immutable;

namespace Cpp2CS.Native;

public sealed record NativeRewrite(int Round, BlockId Block, string Rule, NativeValue Value,
    NativeValue? Alias, NativeNode? Before, NativeNode? After);
public sealed record NativeNormalizationStatistics(int Rounds, int OriginalNodes, int Nodes,
    int OriginalParameters, int Parameters, int PureRewrites, int ParameterAliases);
public sealed record NativeNormalizationResult(NativeRegion Original, NativeRegion Region,
    string RuleVersion, string Revision, int MaxRounds, bool ReachedFixedPoint,
    ImmutableArray<NativeRewrite> Rewrites, NativeNormalizationStatistics Statistics);

public static class NativeNormalizer
{
    public const string RuleVersion = "native-n2-1:" + NativePurePass.Version;

    public static NativeNormalizationResult Normalize(NativeRegion source, int maxRounds = 64)
    {
        var errors = NativeValidator.Validate(source);
        if (errors.Count != 0) throw new InvalidDataException(string.Join("; ", errors));
        if (maxRounds is < 1 or > 4096) throw new ArgumentOutOfRangeException(nameof(maxRounds));
        var result = Run(source, maxRounds);
        var structural = NativeNormalizationValidator.ValidateGraph(result.Region);
        if (structural.Count != 0) throw new InvalidDataException(string.Join("; ", structural));
        return result;
    }

    internal static NativeNormalizationResult Run(NativeRegion source, int maxRounds)
    {
        var region = source;
        var rewrites = ImmutableArray.CreateBuilder<NativeRewrite>();
        var rounds = 0;
        var fixedPoint = false;
        for (; rounds < maxRounds; rounds++)
        {
            var start = rewrites.Count;
            var definitions = region.Blocks.SelectMany(b => b.Nodes).Where(n => n.Result is not null)
                .ToDictionary(n => n.Result!.Value.Id);
            var aliases = new Dictionary<ValueId, NativeValue>();
            var blocks = ImmutableArray.CreateBuilder<NativeBlock>();
            foreach (var block in region.Blocks)
            {
                var reduced = NativePurePass.Run(block.Nodes, definitions);
                foreach (var pair in reduced.Aliases) aliases.Add(pair.Key, pair.Value);
                foreach (var rewrite in reduced.Rewrites)
                    rewrites.Add(new(rounds, block.Id, rewrite.Rule, rewrite.Before.Result!.Value,
                        rewrite.Alias, rewrite.Before, rewrite.After));
                blocks.Add(block with { Nodes = reduced.Nodes });
            }
            if (rewrites.Count != start) region = Remap(region, blocks.ToImmutable(), aliases, false);
            var parameters = NativeParameterAnalysis.FindAliases(region);
            foreach (var block in region.Blocks)
                foreach (var parameter in block.Parameters)
                    if (parameters.TryGetValue(parameter.Value.Id, out var replacement))
                        rewrites.Add(new(rounds, block.Id, "single-external-parameter-scc", parameter.Value,
                            replacement, null, null));
            if (parameters.Count != 0) region = Remap(region, region.Blocks, parameters, true);
            if (rewrites.Count == start)
            {
                fixedPoint = true;
                rounds++;
                break;
            }
        }
        return new(source, region, RuleVersion, $"{source.Source.Revision}:{RuleVersion}:{maxRounds}", maxRounds,
            fixedPoint, rewrites.ToImmutable(), new(rounds, source.Blocks.Sum(b => b.Nodes.Length),
                region.Blocks.Sum(b => b.Nodes.Length), source.Blocks.Sum(b => b.Parameters.Length),
                region.Blocks.Sum(b => b.Parameters.Length), rewrites.Count(r => r.Before is not null),
                rewrites.Count(r => r.Before is null)));
    }

    private static NativeRegion Remap(NativeRegion original, ImmutableArray<NativeBlock> blocks,
        IReadOnlyDictionary<ValueId, NativeValue> aliases, bool removeParameters)
    {
        NativeValue Resolve(NativeValue value)
        {
            while (aliases.TryGetValue(value.Id, out var replacement)) value = replacement;
            return value;
        }
        var maps = new Dictionary<StateMap, StateMap>(ReferenceEqualityComparer.Instance);
        StateMap State(StateMap state)
        {
            if (maps.TryGetValue(state, out var existing)) return existing;
            var mapped = new StateMap(state.Slots.ToImmutableDictionary(p => p.Key, p => Resolve(p.Value), StringComparer.Ordinal), Resolve(state.World));
            maps.Add(state, mapped);
            return mapped;
        }
        var byId = original.Blocks.ToDictionary(b => b.Id);
        var rewritten = blocks.Select(block =>
        {
            var nodeIndices = block.Nodes.Select((n, i) => (n.Source.OperationIndex, Index: i)).ToDictionary(p => p.OperationIndex, p => p.Index);
            return block with
            {
                Parameters = block.Parameters.Where(p => !removeParameters || !aliases.ContainsKey(p.Value.Id)).ToImmutableArray(),
                Nodes = block.Nodes.Select(n => n with
                {
                    Inputs = n.Inputs.Select(Resolve).ToImmutableArray(),
                    Flow = n.Flow is { } flow ? new(Resolve(flow.Input), Resolve(flow.Output)) : null
                }).ToImmutableArray(),
                Steps = block.Steps.Select(s => s with
                {
                    NodeIndex = nodeIndices.TryGetValue(s.OperationIndex, out var index) ? index : null,
                    Result = s.Result is { } result ? Resolve(result) : null, Before = State(s.Before), After = State(s.After)
                }).ToImmutableArray(),
                InitialState = State(block.InitialState), FinalState = State(block.FinalState),
                Edges = block.Edges.Select(e => e with
                {
                    Destination = e.Destination is NativeValueDestination value ? new NativeValueDestination(Resolve(value.Target)) : e.Destination,
                    Condition = e.Condition is { } condition ? condition with { Value = Resolve(condition.Value) } : null,
                    State = State(e.State),
                    Arguments = e.Arguments.Where((_, i) => !removeParameters || e.Target is not { } target ||
                        !aliases.ContainsKey(byId[target].Parameters[i].Value.Id)).Select(Resolve).ToImmutableArray()
                }).ToImmutableArray()
            };
        }).ToImmutableArray();
        return new(original.Source, rewritten);
    }
}
