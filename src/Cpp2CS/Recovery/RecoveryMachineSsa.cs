using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Ir;
using Cpp2CS.Native;

namespace Cpp2CS.Recovery;

internal enum RecoveryValueRole { Ordinary, UnboundInput, StackBase, ReturnAddress, CallResult, CallClobber }
internal sealed record RecoveryNodeInfo(RecoveryValueRole Role, string Detail, Operation? Operation = null);
internal sealed record RecoverySsaCall(MachineCallSummary Summary, ImmutableArray<NativeValue> Arguments,
    NativeValue? Result, NativeValue Stack, NativeValue Target, int OperationIndex, bool Tail);
internal sealed class RecoverySsaBlock(int id, DerivedFunctionBlock? source)
{
    public int Id { get; } = id;
    public DerivedFunctionBlock? Source { get; } = source;
    public List<BlockParameter> Parameters { get; } = [];
    public Dictionary<string, NativeValue> Inputs { get; } = [];
    public Dictionary<string, NativeValue> Outputs { get; set; } = [];
    public List<NativeNode> Nodes { get; set; } = [];
    public Dictionary<int, RecoveryNodeInfo> Information { get; } = [];
    public List<(int Target, DerivedFunctionEdge? Source)> Edges { get; } = [];
    public NativeValue? Condition { get; set; }
    public NativeValue? ReturnValue { get; set; }
    public NativeValue? TransferTarget { get; set; }
    public RecoverySsaCall? Call { get; set; }
    public NativeValue World { get; set; }
    public int SyntheticIndex { get; set; }
}

// 派生机器图的工作视图；只有最终投影结果进入 NirModule。
internal sealed class RecoveryMachineSsa
{
    public DerivedFunctionGraph Graph { get; }
    public MachineInterface Interface { get; }
    public List<RecoverySsaBlock> Blocks { get; } = [];
    public RecoverySsaBlock Entry { get; }
    public List<NativeValue> LogicalArguments { get; } = [];
    public Dictionary<ValueId, NativeValue> Aliases { get; } = [];
    public Dictionary<string, NativeValue> EntrySlots { get; } = [];
    public Dictionary<long, FrameByte> EntryBytes { get; } = [];
    public NativeValue StackBase { get; private set; }
    public NativeValue ReturnAddress { get; private set; }
    public int ValueCount => nextValue;
    public int Rounds { get; private set; }
    public List<NirRecoveryEvidence> Evidence { get; } = [];
    private readonly Dictionary<(int Width, BigInteger Value), NativeValue> constants = [];
    private int nextValue;
    private readonly InstructionOrigin origin;

    public RecoveryMachineSsa(DerivedFunctionGraph graph)
    {
        Graph = graph;
        Interface = MachineAbi.Describe(graph.Contract);
        origin = graph.Entry.Instruction!.Origin;
        Entry = new(graph.Blocks.Max(block => block.Id) + 1, null);
        Blocks.Add(Entry);
        Entry.World = FreshWorld();
        Entry.Parameters.Add(new(Entry.World, null));
        foreach (var (slot, width) in StateLayout.For(graph.Architecture).OrderBy(pair => pair.Key, StringComparer.Ordinal))
        {
            var role = slot == Interface.StackPointer ? RecoveryValueRole.StackBase :
                graph.Architecture == Architecture.Arm64 && slot == "x30" ? RecoveryValueRole.ReturnAddress : RecoveryValueRole.UnboundInput;
            var value = graph.Architecture == Architecture.X64 && slot == "df" ? Constant(width, 0) :
                Unknown(Entry, width, role, $"entry.{slot}");
            EntrySlots.Add(slot, value);
            if (role == RecoveryValueRole.StackBase) StackBase = value;
            if (role == RecoveryValueRole.ReturnAddress) ReturnAddress = value;
        }
        if (graph.Architecture == Architecture.X64)
        {
            ReturnAddress = Unknown(Entry, 64, RecoveryValueRole.ReturnAddress, "entry return address");
            for (var offset = 0; offset < 8; offset++) EntryBytes.Add(offset, new(ReturnAddress, offset));
        }
        Entry.Outputs = new(EntrySlots);
        for (var index = 0; index < graph.Contract.Signature.Arguments.Length; index++)
        {
            var type = graph.Contract.Signature.Arguments[index];
            var parameter = Fresh(type.Width);
            LogicalArguments.Add(parameter);
            Entry.Parameters.Insert(index, new(parameter, null));
            foreach (var part in MachineAbi.Pieces(Interface.Arguments[index]))
            {
                var value = Slice(Entry, parameter, part.ValueBitOffset, part.Location.Width);
                switch (part.Location)
                {
                case SlotArgumentLocation location:
                    Entry.Outputs[location.Slot] = Insert(Entry, Entry.Outputs[location.Slot], value, location.Offset);
                    break;
                case StackArgumentLocation location:
                    for (var offset = 0; offset < (location.Width + 7) / 8; offset++)
                        EntryBytes.Add(location.EntrySpOffset + offset, new(value, offset, Math.Min(8, location.Width - offset * 8)));
                    break;
                default: throw new InvalidOperationException("Unknown argument location");
                }
            }
        }
        Entry.Edges.Add((graph.Entry.Id, null));
        foreach (var source in graph.Blocks)
        {
            var block = new RecoverySsaBlock(source.Id, source) { SyntheticIndex = source.Instruction!.Operations.Length };
            foreach (var (slot, width) in StateLayout.For(graph.Architecture).OrderBy(pair => pair.Key, StringComparer.Ordinal))
            {
                var value = Fresh(width);
                block.Parameters.Add(new(value, slot));
                block.Inputs.Add(slot, value);
            }
            block.World = FreshWorld();
            block.Parameters.Add(new(block.World, null));
            Blocks.Add(block);
        }
        foreach (var block in Blocks.Where(block => block.Source is not null)) BuildBlock(block);
    }

    public NativeValue Fresh(int width) => new(new(nextValue++), new BitsType(width));
    private NativeValue FreshWorld() => new(new(nextValue++), WorldType.Instance);
    public NativeValue Resolve(NativeValue value)
    {
        while (Aliases.TryGetValue(value.Id, out var replacement)) value = replacement;
        return value;
    }
    public int Width(NativeValue value) => ((BitsType)value.Type).Width;
    public NativeValue Constant(int width, BigInteger bits)
    {
        bits &= MirOperationEvaluator.Mask(width);
        if (constants.TryGetValue((width, bits), out var previous)) return Resolve(previous);
        var value = Fresh(width);
        Entry.Nodes.Add(new(OpCode.Constant, value, [], new ImmediatePayload(bits), null, new(origin, Entry.SyntheticIndex++)));
        constants.Add((width, bits), value);
        return value;
    }
    public NativeValue Pure(RecoverySsaBlock block, OpCode code, int width, params NativeValue[] inputs) =>
        Pure(block, code, width, inputs.ToImmutableArray(), NoPayload.Instance);
    public NativeValue Pure(RecoverySsaBlock block, OpCode code, int width, ImmutableArray<NativeValue> inputs, OperationPayload payload)
    {
        var result = Fresh(width);
        block.Nodes.Add(new(code, result, inputs, payload, null, new(block.Source?.Instruction?.Origin ?? origin, block.SyntheticIndex++)));
        return result;
    }
    public NativeValue Slice(RecoverySsaBlock block, NativeValue value, int offset, int width) =>
        offset == 0 && Width(value) == width ? value : Pure(block, OpCode.Extract, width, [value], new ImmediatePayload(offset));
    private NativeValue Insert(RecoverySsaBlock block, NativeValue original, NativeValue value, int offset)
    {
        var result = value;
        if (offset != 0) result = Pure(block, OpCode.Concat, Width(result) + offset, result, Slice(block, original, 0, offset));
        var upper = Width(original) - Width(value) - offset;
        if (upper != 0) result = Pure(block, OpCode.Concat, Width(original), Slice(block, original, offset + Width(value), upper), result);
        return result;
    }
    private NativeValue Unknown(RecoverySsaBlock block, int width, RecoveryValueRole role, string detail)
    {
        var value = Fresh(width);
        var index = block.SyntheticIndex++;
        block.Information.Add(index, new(role, detail));
        block.Nodes.Add(new(OpCode.Undefined, value, [], new ChoicePayload(detail), null,
            new(block.Source?.Instruction?.Origin ?? origin, index)));
        return value;
    }

    private void BuildBlock(RecoverySsaBlock block)
    {
        var instruction = block.Source!.Instruction!;
        var state = new Dictionary<string, NativeValue>(block.Inputs);
        var values = new Dictionary<int, NativeValue>();
        for (var index = 0; index < instruction.Operations.Length; index++)
        {
            var operation = instruction.Operations[index];
            if (operation.Code == OpCode.ReadSlot) { values.Add(operation.Result!.Value.Id, state[operation.Slot!]); continue; }
            if (operation.Code == OpCode.WriteSlot) { state[operation.Slot!] = values[operation.Inputs[0].Id]; continue; }
            if (operation.Code == OpCode.Constant)
            {
                values.Add(operation.Result!.Value.Id, Constant(operation.Result.Value.Width, operation.Immediate));
                continue;
            }
            NativeValue? result = operation.Result is { } resultValue ? Fresh(resultValue.Width) : null;
            if (result is { } produced) values.Add(operation.Result!.Value.Id, produced);
            WorldFlow? flow = null;
            if (operation.Flow is not null)
            {
                var next = FreshWorld();
                flow = new(block.World, next);
                block.World = next;
            }
            block.Nodes.Add(new(operation.Code, result, operation.Inputs.Select(value => values[value.Id]).ToImmutableArray(),
                operation.Payload, flow, new(instruction.Origin, index)));
            block.Information.Add(index, new(RecoveryValueRole.Ordinary, instruction.Rule, operation));
        }
        if (instruction.Exit.Condition is { } condition) block.Condition = values[condition.Id];
        if (instruction.Exit.Target is { } target) block.TransferTarget = values[target.Id];
        block.Outputs = state;
        var callEdge = block.Source.Edges.SingleOrDefault(edge => edge.Kind is DerivedEdgeKind.Call or DerivedEdgeKind.TailCall);
        if (callEdge?.Call is { } summary) ApplySummary(block, summary, callEdge.Kind == DerivedEdgeKind.TailCall);
        if (block.Source.Edges.Any(edge => edge.Kind == DerivedEdgeKind.Return) && Interface.Result is { } resultLocation)
            block.ReturnValue = ReadLocation(block, state, resultLocation);
        foreach (var edge in block.Source.Edges)
            if (edge.TargetBlock is { } successor) block.Edges.Add((successor, edge));
    }

    private void ApplySummary(RecoverySsaBlock block, MachineCallSummary summary, bool tail)
    {
        var before = new Dictionary<string, NativeValue>(block.Outputs);
        var stack = before[summary.Interface.StackPointer];
        var arguments = ImmutableArray.CreateBuilder<NativeValue>();
        foreach (var location in summary.Interface.Arguments) arguments.Add(ReadLocation(block, before, location, stack));
        var callIndex = block.SyntheticIndex++;
        var result = summary.Callee.Signature.Result is { } type ? Fresh(type.Width) : (NativeValue?)null;
        var world = FreshWorld();
        block.Nodes.Add(new(OpCode.Undefined, result, arguments.ToImmutable(), new ChoicePayload("logical call result"),
            new(block.World, world), new(block.Source!.Instruction!.Origin, callIndex)));
        block.Information.Add(callIndex, new(RecoveryValueRole.CallResult, summary.Callee.Name));
        block.World = world;
        block.Call = new(summary, arguments.ToImmutable(), result, stack, block.TransferTarget!.Value, callIndex, tail);
        if (tail || !summary.Callee.Effects.MayReturn) return;
        foreach (var relation in summary.NormalOutputs)
        {
            NativeValue? assembled = null;
            foreach (var segment in relation.Segments.OrderBy(segment => segment.Offset))
            {
                var part = segment.Kind switch
                {
                    SlotRelationKind.Preserve => Slice(block, before[segment.InputSlot ?? relation.Slot], segment.InputOffset, segment.Width),
                    SlotRelationKind.Havoc => Unknown(block, segment.Width, RecoveryValueRole.CallClobber, $"call {summary.Callee.Name}: {relation.Slot}[{segment.Offset}:{segment.Width}]"),
                    SlotRelationKind.Result => Slice(block, result ?? throw new InvalidOperationException("Call result mapping lacks a result"), segment.ResultOffset, segment.Width),
                    SlotRelationKind.AddConstant => Pure(block, OpCode.Add, segment.Width,
                        Slice(block, before[segment.InputSlot ?? relation.Slot], segment.InputOffset, segment.Width), Constant(segment.Width, segment.Constant)),
                    SlotRelationKind.Constant => Constant(segment.Width, segment.Constant),
                    _ => throw new InvalidOperationException("Unknown slot relation")
                };
                assembled = assembled is { } low ? Pure(block, OpCode.Concat, Width(part) + Width(low), part, low) : part;
            }
            block.Outputs[relation.Slot] = assembled ?? throw new InvalidOperationException("Empty slot relation");
        }
        Evidence.Add(new("call.summary", block.Source.Address, null, string.Join("; ", summary.Prerequisites)));
    }

    private NativeValue ReadLocation(RecoverySsaBlock block, Dictionary<string, NativeValue> state,
        MachineArgumentLocation location, NativeValue? stack = null)
    {
        NativeValue? assembled = null;
        foreach (var part in MachineAbi.Pieces(location).OrderBy(part => part.ValueBitOffset))
        {
            NativeValue value;
            if (part.Location is SlotArgumentLocation slot) value = Slice(block, state[slot.Slot], slot.Offset, slot.Width);
            else if (part.Location is StackArgumentLocation saved && stack is { } baseAddress)
            {
                var address = saved.EntrySpOffset == 0 ? baseAddress : Pure(block, OpCode.Add, 64, baseAddress, Constant(64, saved.EntrySpOffset));
                var loadWidth = (saved.Width + 7) / 8 * 8;
                var loaded = Fresh(loadWidth);
                var next = FreshWorld();
                var index = block.SyntheticIndex++;
                var operation = new Operation(OpCode.Load, new(0, loadWidth), [new(0, 64)],
                    new MemoryPayload(new(MemoryOrder.Relaxed, 8, 0)));
                block.Nodes.Add(new(OpCode.Load, loaded, [address], operation.Payload, new(block.World, next), new(block.Source!.Instruction!.Origin, index)));
                block.Information.Add(index, new(RecoveryValueRole.Ordinary, "ABI stack argument", operation));
                block.World = next;
                value = Slice(block, loaded, 0, saved.Width);
            }
            else throw new InvalidOperationException("Unknown argument or result location");
            if (part.ValueBitOffset != (assembled is { } previous ? Width(previous) : 0))
                throw new InvalidOperationException("ABI location does not cover contiguous logical bits");
            assembled = assembled is { } low ? Pure(block, OpCode.Concat, Width(low) + Width(value), value, low) : value;
        }
        return assembled is { } result && Width(result) == location.Width ? result
            : throw new InvalidOperationException("ABI location does not cover the logical value");
    }

    public Dictionary<ValueId, NativeNode> Definitions() => Blocks.SelectMany(block => block.Nodes)
        .Where(node => node.Result is not null).ToDictionary(node => node.Result!.Value.Id);

    public bool Normalize(int maxRounds)
    {
        for (var round = 0; round < maxRounds; round++)
        {
            var changed = false;
            var definitions = Definitions();
            foreach (var block in Blocks)
            {
                var result = NativePurePass.Run(block.Nodes.ToImmutableArray(), definitions,
                    (source, value, width) => new(OpCode.Extract, Fresh(width), [value], new ImmediatePayload(0), null,
                        new(source.Source.Origin, block.SyntheticIndex++)));
                block.Nodes = result.Nodes.ToList();
                foreach (var (id, value) in result.Aliases) Aliases.Add(id, Resolve(value));
                changed |= !result.Rewrites.IsEmpty;
            }
            changed |= HoistConstants();
            Remap();
            var analysis = AnalysisGraph();
            foreach (var (id, value) in NativeParameterAnalysis.FindAliases(analysis, [new(Entry.Id)]))
            {
                Aliases.Add(id, Resolve(value));
                changed = true;
            }
            Remap();
            Rounds++;
            if (!changed) return true;
        }
        return false;
    }

    private bool HoistConstants()
    {
        var changed = false;
        foreach (var block in Blocks)
        {
            foreach (var node in block.Nodes.ToArray())
            {
                if (node is not { Code: OpCode.Constant, Result: { } result, Payload: ImmediatePayload immediate, Flow: null }) continue;
                var key = (Width(result), immediate.Value & MirOperationEvaluator.Mask(Width(result)));
                if (block == Entry && !constants.ContainsKey(key)) constants.Add(key, result);
                var canonical = Constant(key.Item1, key.Item2);
                if (Resolve(result) == canonical) continue;
                Aliases.Add(result.Id, canonical);
                changed = true;
            }
        }
        return changed;
    }

    public ImmutableArray<NativeAnalysisBlock> AnalysisGraph()
    {
        var byId = Blocks.ToDictionary(block => block.Id);
        return Blocks.Select(block => new NativeAnalysisBlock(new(block.Id),
            block.Parameters.Where(parameter => !Aliases.ContainsKey(parameter.Value.Id)).ToImmutableArray(), block.Nodes.ToImmutableArray(),
            block.Edges.Select(edge => new NativeAnalysisEdge(new(edge.Target), byId[edge.Target].Parameters
                .Where(parameter => !Aliases.ContainsKey(parameter.Value.Id))
                .Select(parameter => parameter.Slot is { } slot ? Resolve(block.Outputs[slot]) : Resolve(block.World)).ToImmutableArray())).ToImmutableArray())).ToImmutableArray();
    }

    public void Remap()
    {
        foreach (var block in Blocks)
        {
            block.Nodes = block.Nodes.Where(node => node.Result is not { } result || !Aliases.ContainsKey(result.Id) || node.Flow is not null)
                .Select(node => node with { Inputs = node.Inputs.Select(Resolve).ToImmutableArray(),
                    Flow = node.Flow is { } flow ? new(Resolve(flow.Input), Resolve(flow.Output)) : null }).ToList();
            block.Outputs = block.Outputs.ToDictionary(pair => pair.Key, pair => Resolve(pair.Value));
            if (block.Condition is { } condition) block.Condition = Resolve(condition);
            if (block.ReturnValue is { } returned) block.ReturnValue = Resolve(returned);
            if (block.TransferTarget is { } target) block.TransferTarget = Resolve(target);
            if (block.Call is { } call) block.Call = call with { Arguments = call.Arguments.Select(Resolve).ToImmutableArray(),
                Stack = Resolve(call.Stack), Target = Resolve(call.Target), Result = call.Result is { } result ? Resolve(result) : null };
        }
    }
}

internal sealed record FrameByte(NativeValue? Value, int ByteOffset, int ValidBits = 8);
