using System.Text.Json;
using Cpp2CS.Ir;

namespace Cpp2CS.Native;

// 面向复查的单向导出；不作为可重新导入的 NativeIR 持久化协议。
public static class NativeReport
{
    public const string Schema = "cpp2cs.native-inspection/0.1";
    public static object Summary(NativeRegion region) => new
    {
        schema = Schema, revision = region.Source.Revision, imageId = region.Source.ImageId,
        architecture = region.Source.Architecture.ToString(), profile = region.Source.ProfileId,
        mirSemantics = region.Source.SemanticsVersion,
        entries = region.Source.Entries.Length, blocks = region.Blocks.Length,
        instructions = region.Blocks.Count(b => b.Source.Instruction is not null),
        edges = region.Blocks.Sum(b => b.Edges.Length),
        openEdges = region.Blocks.Sum(b => b.Edges.Count(e => e.Target is null)),
        stopBlocks = region.Blocks.Count(b => b.Source.Stop is not null),
        parameters = region.Blocks.Sum(b => b.Parameters.Length),
        nodes = region.Blocks.Sum(b => b.Nodes.Length),
        stateStages = region.Blocks.Sum(b => b.Steps.Length),
        boundaries = region.Blocks.SelectMany(b => b.Edges.Select(e => e.Source.Boundary).Append(b.Source.Stop))
            .OfType<RegionBoundary>().GroupBy(b => b.Kind).ToDictionary(g => g.Key.ToString(), g => g.Count()),
        support = region.Blocks.Where(b => b.Capabilities is not null).GroupBy(b => b.Capabilities!.Support)
            .ToDictionary(g => g.Key.ToString(), g => g.Count()),
        meaning = "Validated open CFG and mechanical full-state SSA; no ABI summaries, native normalization, complete reachability or game-runtime proof"
    };

    public static void Write(NativeRegion region, string path)
    {
        var errors = NativeValidator.Validate(region);
        if (errors.Count != 0) throw new InvalidDataException(string.Join("; ", errors));
        object Value(NativeValue value) => new { id = value.Id.Id, type = value.Type is BitsType bits ? $"bits{bits.Width}" : "world" };
        object State(StateMap state) => new
        {
            slots = state.Slots.OrderBy(s => s.Key, StringComparer.Ordinal).ToDictionary(s => s.Key, s => s.Value.Id.Id), world = state.World.Id.Id
        };
        object Destination(NativeDestination destination) => destination switch
        {
            NativeAddressDestination address => new { kind = "address", address = $"0x{address.Address:X}" },
            NativeValueDestination value => new { kind = "value", value = value.Target.Id.Id },
            NativeExceptionDestination exception => new { kind = "exception", exception = exception.Boundary },
            _ => throw new InvalidOperationException("Unknown native destination")
        };
        var report = new
        {
            summary = Summary(region),
            entries = region.Source.Entries.Select(e => new { address = $"0x{e.Seed.Address:X}", e.Seed.Evidence, block = e.Block.Id }),
            blocks = region.Blocks.Select(block => new
            {
                id = block.Id.Id, address = $"0x{block.Source.Address:X}", stop = block.Source.Stop,
                origin = block.Source.Instruction?.Origin, rule = block.Source.Instruction?.Rule,
                capabilities = block.Capabilities,
                parameters = block.Parameters.Select(p => new { value = Value(p.Value), slot = p.Slot }),
                nodes = block.Nodes.Select(n => new
                {
                    code = n.Code, result = n.Result is { } result ? Value(result) : null,
                    inputs = n.Inputs.Select(v => v.Id.Id), payload = n.Payload,
                    worldIn = n.Flow?.Input.Id.Id, worldOut = n.Flow?.Output.Id.Id, sourceOperation = n.Source.OperationIndex
                }),
                stages = block.Steps.Select(s => new
                {
                    operation = s.OperationIndex, node = s.NodeIndex, result = s.Result?.Id.Id,
                    code = block.Source.Instruction!.Operations[s.OperationIndex].Code,
                    slot = block.Source.Instruction.Operations[s.OperationIndex].Slot,
                    worldBefore = s.Before.World.Id.Id, worldAfter = s.After.World.Id.Id,
                    slotUpdates = s.After.Slots.Where(p => p.Value != s.Before.Slots[p.Key])
                        .ToDictionary(p => p.Key, p => p.Value.Id.Id)
                }),
                initialState = State(block.InitialState), finalState = State(block.FinalState),
                edges = block.Edges.Select(e => new
                {
                    id = e.Id.Id, targetBlock = e.Target?.Id, kind = e.Source.Successor.Kind,
                    hint = e.Source.Successor.TransferHint, destination = Destination(e.Destination),
                    condition = e.Condition is { } condition ? new { value = condition.Value.Id.Id, required = condition.RequiredValue } : null,
                    state = State(e.State), arguments = e.Arguments.Select(v => v.Id.Id), boundary = e.Source.Boundary
                })
            })
        };
        var options = new JsonSerializerOptions(MirJson.Options) { WriteIndented = true };
        Directory.CreateDirectory(Path.GetDirectoryName(Path.GetFullPath(path))!);
        File.WriteAllText(path, JsonSerializer.Serialize(report, options) + Environment.NewLine);
    }
}
