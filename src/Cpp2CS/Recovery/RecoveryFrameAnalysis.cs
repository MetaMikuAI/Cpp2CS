using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Ir;
using Cpp2CS.Native;

namespace Cpp2CS.Recovery;

internal sealed record RecoveryFrameAccess(int Block, int Operation, long Offset, int Bytes,
    bool Load, bool Store, ValueId? Result);

internal sealed class RecoveryFrameAnalysis
{
    private readonly RecoveryMachineSsa ssa;
    private readonly NirRecoveryOptions options;
    private readonly bool privateFrame;
    private Dictionary<ValueId, OffsetFact> offsets = [];
    private Dictionary<ValueId, NativeNode> definitions = [];
    private Dictionary<ValueId, (RecoverySsaBlock Block, string Slot)> parameterSources = [];
    private Dictionary<int, Dictionary<long, FrameByte>> beforeCalls = [];
    private bool returnedChecked;
    public List<NirRecoveryDiagnostic> Diagnostics { get; } = [];
    public HashSet<ValueId> ForwardedLoads { get; } = [];
    public HashSet<ValueId> InitializedLoads { get; } = [];
    public List<RecoveryFrameAccess> FrameAccesses { get; } = [];
    public bool HasEscapes { get; private set; }
    public bool ReachedFixedPoint { get; private set; }

    private RecoveryFrameAnalysis(RecoveryMachineSsa ssa, NirRecoveryOptions options)
    {
        this.ssa = ssa;
        this.options = options;
        privateFrame = options.AssumePrivateValidFrames || ssa.Graph.Contract.Domain?.ValidPrivateFrame == true;
    }

    public static RecoveryFrameAnalysis Run(RecoveryMachineSsa ssa, NirRecoveryOptions options)
    {
        var result = new RecoveryFrameAnalysis(ssa, options);
        for (var round = 0; round < options.MaxNormalizationRounds; round++)
        {
            if (!result.FindOffsets()) break;
            result.FindEscapes();
            var loads = result.FindMemoryFacts();
            if (!result.ReachedFixedPoint || result.HasEscapes || !result.privateFrame) break;
            var applied = result.Forward(loads);
            if (applied == 0) break;
            if (!ssa.Normalize(options.MaxNormalizationRounds))
            {
                result.Diagnostic(ssa.Graph.Contract.EntryAddress, "frame.normalize-budget", "栈转发后的纯值归约未收敛");
                result.ReachedFixedPoint = false;
                break;
            }
            if (round + 1 == options.MaxNormalizationRounds)
            {
                result.Diagnostic(ssa.Graph.Contract.EntryAddress, "frame.forward-budget", "栈字节转发迭代尚未收敛");
                result.ReachedFixedPoint = false;
            }
        }
        if (!result.privateFrame && result.FrameAccesses.Count != 0)
            result.Diagnostic(ssa.Graph.Contract.EntryAddress, "frame.validity", "栈存储归约需要明确采用有效私有帧前提");
        result.VerifyReturns();
        return result;
    }

    public bool TryOffset(NativeValue value, out long offset)
    {
        var found = offsets.GetValueOrDefault(ssa.Resolve(value).Id);
        offset = found.Offset;
        return found.Kind == OffsetKind.Known;
    }

    private bool FindOffsets()
    {
        definitions = ssa.Definitions();
        parameterSources = ssa.Blocks.SelectMany(block => block.Parameters.Where(parameter => parameter.Slot is not null &&
            ssa.Resolve(parameter.Value) == parameter.Value).Select(parameter => (parameter.Value.Id, Block: block, Slot: parameter.Slot!)))
            .ToDictionary(item => item.Id, item => (item.Block, item.Slot));
        offsets = [];
        offsets[ssa.Resolve(ssa.StackBase).Id] = new(OffsetKind.Known, 0);
        foreach (var argument in ssa.Entry.Parameters.Where(parameter => parameter.Value.Type is BitsType))
            offsets[ssa.Resolve(argument.Value).Id] = new(OffsetKind.Other, 0);
        var predecessors = Predecessors();
        for (var round = 0; round < options.MaxNormalizationRounds; round++)
        {
            var changed = false;
            foreach (var block in ssa.Blocks)
            {
                foreach (var parameter in block.Parameters.Where(parameter => parameter.Slot is not null))
                {
                    var value = ssa.Resolve(parameter.Value);
                    if (value != parameter.Value) continue;
                    var incoming = predecessors[block.Id].Select(parent => Fact(parent.Outputs[parameter.Slot!])).ToArray();
                    Update(value.Id, Meet(incoming));
                }
                foreach (var node in block.Nodes)
                {
                    if (node.Result is not { } result || result.Type is not BitsType) continue;
                    result = ssa.Resolve(result);
                    if (result != node.Result.Value || result == ssa.Resolve(ssa.StackBase)) continue;
                    Update(result.Id, Derive(node));
                }
            }
            if (!changed) return true;

            void Update(ValueId id, OffsetFact fact)
            {
                var before = offsets.GetValueOrDefault(id);
                var after = before.Kind == OffsetKind.Other ? before :
                    before.Kind == OffsetKind.Known && fact.Kind == OffsetKind.Known && before.Offset != fact.Offset
                        ? new OffsetFact(OffsetKind.Other, 0) : fact.Kind == OffsetKind.Pending ? before : fact;
                if (before == after) return;
                offsets[id] = after;
                changed = true;
            }
        }
        Diagnostic(ssa.Graph.Contract.EntryAddress, "frame.offset-budget", "栈地址关系尚未达到固定点");
        ReachedFixedPoint = false;
        return false;

        OffsetFact Fact(NativeValue value) => offsets.GetValueOrDefault(ssa.Resolve(value).Id);
        OffsetFact Derive(NativeNode node)
        {
            if (node.Result!.Value.Type is not BitsType { Width: >= 64 }) return new(OffsetKind.Other, 0);
            if (node.Code is OpCode.Add or OpCode.Sub)
            {
                var first = Fact(node.Inputs[0]);
                var second = Fact(node.Inputs[1]);
                if (Constant(node.Inputs[1], out var delta))
                    return first.Kind == OffsetKind.Known ? new(OffsetKind.Known,
                        unchecked(first.Offset + (node.Code == OpCode.Add ? Signed64(delta) : -Signed64(delta)))) : first;
                if (node.Code == OpCode.Add && Constant(node.Inputs[0], out delta))
                    return second.Kind == OffsetKind.Known ? new(OffsetKind.Known, unchecked(second.Offset + Signed64(delta))) : second;
                return first.Kind == OffsetKind.Pending || second.Kind == OffsetKind.Pending
                    ? default : new(OffsetKind.Other, 0);
            }
            if (node.Code == OpCode.Select) return Meet([Fact(node.Inputs[1]), Fact(node.Inputs[2])]);
            if (node.Code is OpCode.Zext or OpCode.Sext && node.Inputs[0].Type is BitsType { Width: >= 64 })
                return Fact(node.Inputs[0]);
            if (node.Code == OpCode.Extract && node.Payload is ImmediatePayload { Value: var immediate } && immediate.IsZero &&
                node.Inputs[0].Type is BitsType { Width: >= 64 }) return Fact(node.Inputs[0]);
            return new(OffsetKind.Other, 0);
        }
    }

    private void FindEscapes()
    {
        var dependent = StackDependencies();
        foreach (var block in ssa.Blocks)
        {
            var address = block.Source?.Address ?? ssa.Graph.Contract.EntryAddress;
            if (block.Call is { } call && call.Arguments.Any(value => dependent.Contains(ssa.Resolve(value).Id)))
                Escape(address, "frame.escape-call", "帧地址作为调用实参逃逸；当前转换不能消除其别名影响");
            if (block.ReturnValue is { } returned && dependent.Contains(ssa.Resolve(returned).Id))
                Escape(address, "frame.escape-return", "逻辑返回值依赖物理帧地址");
            foreach (var node in block.Nodes)
            {
                var dataIndex = node.Code == OpCode.Store ? 1 : node.Code == OpCode.StoreIf ? 2 : -1;
                var addressIndex = node.Code == OpCode.StoreIf ? 1 : 0;
                if (node.Code is OpCode.Load or OpCode.LoadIf or OpCode.Store or OpCode.StoreIf or OpCode.AtomicRmw or OpCode.LoadExclusive or OpCode.StoreExclusive)
                {
                    addressIndex = node.Code is OpCode.LoadIf or OpCode.StoreIf ? 1 : 0;
                    if (dependent.Contains(ssa.Resolve(node.Inputs[addressIndex]).Id) && !TryOffset(node.Inputs[addressIndex], out _))
                        Escape(address, "frame.address", "帧相关地址不是已知固定偏移，当前不能建立局部对象");
                }
                if (dataIndex >= 0 && dependent.Contains(ssa.Resolve(node.Inputs[dataIndex]).Id) &&
                    !TryOffset(node.Inputs[addressIndex], out _))
                    Escape(address, "frame.escape-store", "帧地址写入非私有存储；当前转换不能忽略后续间接访问");
            }
        }

        void Escape(ulong address, string code, string message)
        {
            HasEscapes = true;
            Diagnostic(address, code, message);
        }
    }

    private Dictionary<(int Block, int Operation), FrameByte[]> FindMemoryFacts()
    {
        FrameAccesses.Clear();
        InitializedLoads.Clear();
        var predecessors = Predecessors();
        var inputs = new Dictionary<int, Dictionary<long, FrameByte>?>();
        var outputs = new Dictionary<int, Dictionary<long, FrameByte>?>();
        foreach (var block in ssa.Blocks) { inputs.Add(block.Id, null); outputs.Add(block.Id, null); }
        var entry = ssa.EntryBytes.ToDictionary(pair => pair.Key, pair => NormalizeByte(pair.Value));
        ReachedFixedPoint = false;
        for (var round = 0; round < options.MaxNormalizationRounds; round++)
        {
            var changed = false;
            foreach (var block in ssa.Blocks)
            {
                var incoming = block == ssa.Entry ? new Dictionary<long, FrameByte>(entry) :
                    Intersect(predecessors[block.Id].Select(parent => outputs[parent.Id]).Where(state => state is not null).Select(state => state!).ToArray());
                if (incoming is null) continue;
                var outgoing = Transfer(block, incoming, null);
                if (!Same(inputs[block.Id], incoming) || !Same(outputs[block.Id], outgoing))
                {
                    inputs[block.Id] = incoming;
                    outputs[block.Id] = outgoing;
                    changed = true;
                }
            }
            if (!changed) { ReachedFixedPoint = true; break; }
        }
        if (!ReachedFixedPoint)
        {
            Diagnostic(ssa.Graph.Contract.EntryAddress, "frame.memory-budget", "栈字节到达值尚未达到固定点");
            return [];
        }
        beforeCalls.Clear();
        var loads = new Dictionary<(int Block, int Operation), FrameByte[]>();
        foreach (var block in ssa.Blocks)
            if (inputs[block.Id] is { } incoming) Transfer(block, incoming, loads);
        return loads;

        Dictionary<long, FrameByte> Transfer(RecoverySsaBlock block, Dictionary<long, FrameByte> incoming,
            Dictionary<(int Block, int Operation), FrameByte[]>? observations)
        {
            var state = new Dictionary<long, FrameByte>(incoming);
            foreach (var node in block.Nodes)
            {
                if (block.Call is { } call && node.Source.OperationIndex == call.OperationIndex)
                {
                    if (observations is not null) beforeCalls[block.Id] = new(state);
                    InvalidateCall(state, call);
                    continue;
                }
                var isLoad = node.Code is OpCode.Load or OpCode.LoadIf;
                var isStore = node.Code is OpCode.Store or OpCode.StoreIf;
                if (node.Code is OpCode.AtomicRmw or OpCode.StoreExclusive)
                {
                    if (!privateFrame || HasEscapes || !KnownNonFrame(node.Inputs[0])) InvalidateAll(state);
                    continue;
                }
                if (!isLoad && !isStore) continue;
                var conditional = node.Code is OpCode.LoadIf or OpCode.StoreIf;
                var addressIndex = conditional ? 1 : 0;
                var condition = BigInteger.Zero;
                var conditionKnown = conditional && Constant(node.Inputs[0], out condition);
                if (conditionKnown && condition.IsZero) continue;
                if (!TryOffset(node.Inputs[addressIndex], out var offset))
                {
                    if (isStore && (!privateFrame || HasEscapes || !KnownNonFrame(node.Inputs[addressIndex]))) InvalidateAll(state);
                    continue;
                }
                var width = isLoad ? ssa.Width(node.Result!.Value) : ssa.Width(node.Inputs[conditional ? 2 : 1]);
                var bytes = (width + 7) / 8;
                if (offset > long.MaxValue - bytes)
                {
                    if (observations is not null) Diagnostic(block.Source!.Address, "frame.range", "帧访问范围发生回绕，不能作为局部对象");
                    if (isStore) InvalidateAll(state);
                    continue;
                }
                if (observations is not null)
                    FrameAccesses.Add(new(block.Id, node.Source.OperationIndex, offset, bytes, isLoad, isStore, node.Result?.Id));
                var ordinary = node.Payload is MemoryPayload { Specification.Order: MemoryOrder.Relaxed, Specification.AtomicWidth: 0, Specification.NonTemporal: false };
                if (isLoad && observations is not null)
                {
                    var known = Enumerable.Range(0, bytes).All(index => state.TryGetValue(offset + index, out var piece) &&
                        piece.ValidBits >= Math.Min(8, width - index * 8));
                    if (known) InitializedLoads.Add(node.Result!.Value.Id);
                    if (known && ordinary && !conditional && !ForwardedLoads.Contains(node.Result!.Value.Id))
                        observations.Add((block.Id, node.Source.OperationIndex), Enumerable.Range(0, bytes).Select(index => state[offset + index]).ToArray());
                }
                if (!isStore) continue;
                var value = ssa.Resolve(node.Inputs[conditional ? 2 : 1]);
                for (var index = 0; index < bytes; index++)
                {
                    var validBits = Math.Min(8, width - index * 8);
                    if (conditional && !conditionKnown)
                    {
                        if (state.TryGetValue(offset + index, out var previous))
                            state[offset + index] = new(null, 0, Math.Min(previous.ValidBits, validBits));
                    }
                    else state[offset + index] = ordinary ? new(value, index, validBits) : new(null, 0, validBits);
                }
            }
            return state;
        }
    }

    private int Forward(Dictionary<(int Block, int Operation), FrameByte[]> loads)
    {
        var dominance = new NativeDominance(ssa.Blocks.Select(block => new BlockId(block.Id)),
            ssa.Blocks.SelectMany(block => block.Edges.Select(edge => (new BlockId(block.Id), new BlockId(edge.Target)))), [new(ssa.Entry.Id)]);
        var locations = new Dictionary<ValueId, (int Block, int Position)>();
        foreach (var block in ssa.Blocks)
        {
            foreach (var parameter in block.Parameters) locations[parameter.Value.Id] = (block.Id, -1);
            for (var index = 0; index < block.Nodes.Count; index++)
                if (block.Nodes[index].Result is { } value) locations[value.Id] = (block.Id, index);
        }
        var replacements = new List<(RecoverySsaBlock Block, NativeNode Node, FrameByte[] Bytes)>();
        foreach (var block in ssa.Blocks)
        {
            for (var position = 0; position < block.Nodes.Count; position++)
            {
                var node = block.Nodes[position];
                if (node.Result is not { } result || node.Code != OpCode.Load || ssa.Aliases.ContainsKey(result.Id) ||
                    !loads.TryGetValue((block.Id, node.Source.OperationIndex), out var bytes)) continue;
                var valid = true;
                for (var index = 0; index < bytes.Length; index++)
                {
                    var piece = bytes[index];
                    var required = Math.Min(8, ssa.Width(result) - index * 8);
                    if (piece.Value is not { } source || piece.ByteOffset < 0 ||
                        piece.ByteOffset * 8 + required > ssa.Width(source) ||
                        !locations.TryGetValue(ssa.Resolve(source).Id, out var location) ||
                        (location.Block == block.Id ? location.Position >= position : !dominance.Dominates(new(location.Block), new(block.Id))))
                    { valid = false; break; }
                }
                if (valid) replacements.Add((block, node, bytes));
            }
        }
        foreach (var (block, node, bytes) in replacements)
        {
            var result = node.Result!.Value;
            var first = ssa.Resolve(bytes[0].Value!.Value);
            var oldCount = block.Nodes.Count;
            NativeValue replacement;
            if (bytes.Select((piece, index) => ssa.Resolve(piece.Value!.Value) == first && piece.ByteOffset == bytes[0].ByteOffset + index).All(value => value))
                replacement = ssa.Slice(block, first, bytes[0].ByteOffset * 8, ssa.Width(result));
            else
            {
                replacement = ssa.Slice(block, first, bytes[0].ByteOffset * 8, Math.Min(8, ssa.Width(result)));
                for (var index = 1; index < bytes.Length; index++)
                {
                    var width = Math.Min(8, ssa.Width(result) - index * 8);
                    var part = ssa.Slice(block, ssa.Resolve(bytes[index].Value!.Value), bytes[index].ByteOffset * 8, width);
                    replacement = ssa.Pure(block, OpCode.Concat, ssa.Width(replacement) + width, part, replacement);
                }
            }
            var generated = block.Nodes.Skip(oldCount).ToArray();
            block.Nodes.RemoveRange(oldCount, generated.Length);
            block.Nodes.InsertRange(block.Nodes.IndexOf(node), generated);
            ssa.Aliases.Add(result.Id, ssa.Resolve(replacement));
            ForwardedLoads.Add(result.Id);
            ssa.Evidence.Add(new("frame.byte-forward", block.Source!.Address, node.Source.OperationIndex,
                "稳定的逐字节到达值一致，定义支配加载；采用有效私有帧前提"));
        }
        return replacements.Count;
    }

    public void VerifyReturns()
    {
        if (returnedChecked) return;
        returnedChecked = true;
        definitions = ssa.Definitions();
        var protocol = MachineAbi.CreateSummary(ssa.Graph.Contract with { Effects = ssa.Graph.Contract.Effects with { MayReturn = true } }).NormalOutputs
            .SelectMany(output => output.Segments.Where(segment => segment.Kind is SlotRelationKind.Preserve or SlotRelationKind.Constant)
                .Select(segment => (output.Slot, Segment: segment))).ToArray();
        foreach (var block in ssa.Blocks.Where(block => block.Source is not null))
        {
            var beforeDiagnostics = Diagnostics.Count;
            var candidate = block.Source!.Edges.Any(edge => edge.IsTailCandidate);
            if (block.Call is { } call)
            {
                if (!TryOffset(call.Stack, out var callOffset))
                    ExitDiagnostic("call.stack", "无法证明调用入口的栈对齐");
                else if (callOffset % call.Summary.Interface.StackAlignment != 0)
                    ExitDiagnostic("contract.call-stack", "调用入口 SP 不满足所采用 ABI 的栈对齐");
                if (call.Tail)
                {
                    var available = ssa.Interface.Arguments.OfType<StackArgumentLocation>()
                        .Select(argument => argument.EntrySpOffset + 8).DefaultIfEmpty(0).Max();
                    if (call.Summary.Interface.Arguments.OfType<StackArgumentLocation>()
                        .Any(argument => argument.EntrySpOffset + 8 > available))
                        Diagnostic(block.Source.Address, "tail.stack-capacity", "被调栈实参超出当前入口合同保证的参数存储空间");
                }
            }
            var returns = block.Source!.Edges.Any(edge => edge.Kind == DerivedEdgeKind.Return);
            var tail = block.Call?.Tail == true;
            if (!returns && !tail) continue;
            if (!ssa.Graph.Contract.Effects.MayReturn && returns)
                Diagnostic(block.Source.Address, "contract.unexpected-return", "声明不返回的函数具有正常返回出口");
            var expectedOffset = tail ? 0 : ssa.Interface.NormalReturnSpAdjustment;
            if (!TryOffset(block.Outputs[ssa.Interface.StackPointer], out var actualOffset))
                ExitDiagnostic("return.stack", "实际出口 SP 与所采用的返回协议不一致");
            else if (actualOffset != expectedOffset)
                ExitDiagnostic("contract.return-stack", "实际出口 SP 与所采用的返回协议不一致");
            if (returns)
            {
                if (block.TransferTarget is not { } target)
                    ExitDiagnostic("return.target", "实际 RET 目标未还原为本次调用的入口返回地址");
                else CheckBits(target, 0, ssa.ReturnAddress, 0, 64, "return.target", "实际 RET 目标未还原为本次调用的入口返回地址");
            }
            else if (ssa.Graph.Architecture == Architecture.Arm64)
            {
                CheckBits(block.Outputs["x30"], 0, ssa.ReturnAddress, 0, 64,
                    "tail.return-address", "尾调用没有恢复当前调用者的返回地址");
            }
            else if (!beforeCalls.TryGetValue(block.Id, out var memory) || !ReturnBytes(memory))
                ExitDiagnostic("tail.return-address", "尾调用入口栈顶不是当前调用者的返回地址");
            foreach (var (slot, segment) in protocol)
            {
                if (segment.Kind == SlotRelationKind.Preserve)
                    CheckBits(block.Outputs[slot], segment.Offset, ssa.EntrySlots[segment.InputSlot ?? slot], segment.InputOffset,
                        segment.Width, "return.preserved", $"出口未还原 ABI 保留位：{slot}[{segment.Offset}:{segment.Width}]");
                else
                    for (var bit = 0; bit < segment.Width; bit++)
                    {
                        var actual = Bit(block.Outputs[slot], segment.Offset + bit);
                        var expected = ((new BigInteger(segment.Constant) >> bit) & 1) != 0;
                        if (actual.Constant != expected)
                        {
                            ExitDiagnostic(actual.Constant is null ? "return.constant" : "contract.return-constant",
                                $"出口不满足 ABI 常量协议：{slot}[{segment.Offset}:{segment.Width}]");
                            break;
                        }
                    }
            }
            if (tail) VerifyTailArguments(block);
            if (tail && Diagnostics.Count == beforeDiagnostics && !HasEscapes && ReachedFixedPoint)
                ssa.Evidence.Add(new("tail.return-protocol", block.Source.Address, null,
                    "入口 SP、调用者返回地址、ABI 保留位、栈实参空间及实参来源已证明；本帧没有逃逸地址"));

            void ExitDiagnostic(string code, string message) => Diagnostic(block.Source.Address,
                candidate ? "tail.proof-" + code.Replace("contract.", "", StringComparison.Ordinal).Replace('.', '-') : code, message);

            void CheckBits(NativeValue actual, int actualStart, NativeValue expected, int expectedStart, int width,
                string code, string message)
            {
                if (SameBits(actual, actualStart, expected, expectedStart, width)) return;
                var contradicted = Enumerable.Range(0, width).Any(bit =>
                {
                    var left = Bit(actual, actualStart + bit);
                    var right = Bit(expected, expectedStart + bit);
                    return left.Constant is not null && left != right;
                });
                ExitDiagnostic(contradicted ? "contract." + code.Replace('.', '-') : code, message);
            }
        }
    }

    private void VerifyTailArguments(RecoverySsaBlock tail)
    {
        var visited = new HashSet<ValueId>();
        var arguments = ssa.LogicalArguments.Select(value => ssa.Resolve(value).Id).ToHashSet();
        var predecessors = Predecessors();
        var owners = ssa.Blocks.SelectMany(block => block.Nodes.Where(node => node.Result is not null)
            .Select(node => (node.Result!.Value.Id, Block: block))).ToDictionary(item => item.Id, item => item.Block);
        foreach (var argument in tail.Call!.Arguments) Visit(argument);

        void Visit(NativeValue value)
        {
            value = ssa.Resolve(value);
            if (arguments.Contains(value.Id) || !visited.Add(value.Id)) return;
            if (parameterSources.TryGetValue(value.Id, out var parameter))
            {
                foreach (var parent in predecessors[parameter.Block.Id]) Visit(parent.Outputs[parameter.Slot]);
                return;
            }
            if (!definitions.TryGetValue(value.Id, out var node))
                throw new InvalidOperationException("Tail argument has no machine SSA definition");
            var owner = owners[value.Id];
            var information = owner.Information.GetValueOrDefault(node.Source.OperationIndex);
            if (information?.Role is RecoveryValueRole.UnboundInput or RecoveryValueRole.CallClobber or
                RecoveryValueRole.StackBase or RecoveryValueRole.ReturnAddress)
            {
                Diagnostic(tail.Source!.Address, "tail.arguments", $"尾调用实参仍依赖未恢复的机器值：{information.Detail}");
                return;
            }
            if (node.Code == OpCode.Load && TryOffset(node.Inputs[0], out var loadedOffset))
            {
                if (!InitializedLoads.Contains(value.Id))
                {
                    Diagnostic(tail.Source!.Address, "tail.arguments", "尾调用栈实参没有所有路径上的初始化证据");
                    return;
                }
                var loadedEnd = loadedOffset + (ssa.Width(value) + 7) / 8;
                foreach (var initial in ssa.EntryBytes.Where(item => item.Key >= loadedOffset && item.Key < loadedEnd))
                    if (initial.Value.Value is { } stored) Visit(stored);
                foreach (var stored in ssa.Blocks.SelectMany(block => block.Nodes).Where(operation => operation.Code == OpCode.Store))
                    if (TryOffset(stored.Inputs[0], out var offset) && offset < loadedEnd &&
                        loadedOffset < offset + (ssa.Width(stored.Inputs[1]) + 7) / 8) Visit(stored.Inputs[1]);
            }
            for (var index = 0; index < node.Inputs.Length; index++)
            {
                if (RecoveryFloating.IsFloating(node.Code) && index == node.Inputs.Length - 1) continue;
                if (index == 0 && node.Code == OpCode.Load && TryOffset(node.Inputs[0], out _)) continue;
                Visit(node.Inputs[index]);
            }
        }
    }

    private void InvalidateCall(Dictionary<long, FrameByte> state, RecoverySsaCall call)
    {
        if (HasEscapes || call.Arguments.Any(argument => !KnownNonFrame(argument)) || !TryOffset(call.Stack, out var calleeSp))
        { InvalidateAll(state); return; }
        if (!call.Summary.World.MayWritePrivateStack) return;
        var windows = call.Summary.Callee.Abi == MachineAbiKind.WindowsX64;
        var stackArguments = call.Summary.Interface.Arguments.OfType<StackArgumentLocation>().ToArray();
        foreach (var offset in state.Keys.ToArray())
        {
            var relative = new BigInteger(offset) - calleeSp;
            if (relative < 0 || windows && relative < 40 ||
                stackArguments.Any(argument => relative >= argument.EntrySpOffset && relative < argument.EntrySpOffset + 8))
                state.Remove(offset);
        }
    }

    private HashSet<ValueId> StackDependencies()
    {
        var result = new HashSet<ValueId> { ssa.Resolve(ssa.StackBase).Id };
        var predecessors = Predecessors();
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var block in ssa.Blocks)
            {
                foreach (var parameter in block.Parameters.Where(parameter => parameter.Slot is not null))
                    if (predecessors[block.Id].Any(parent => result.Contains(ssa.Resolve(parent.Outputs[parameter.Slot!]).Id)))
                        changed |= result.Add(ssa.Resolve(parameter.Value).Id);
                foreach (var node in block.Nodes)
                    if (node.Result is { } value && node.Flow is null && node.Code != OpCode.Undefined &&
                        node.Inputs.Any(input => result.Contains(ssa.Resolve(input).Id)))
                        changed |= result.Add(ssa.Resolve(value).Id);
            }
        }
        return result;
    }

    private Dictionary<int, List<RecoverySsaBlock>> Predecessors()
    {
        var result = ssa.Blocks.ToDictionary(block => block.Id, _ => new List<RecoverySsaBlock>());
        foreach (var block in ssa.Blocks)
            foreach (var edge in block.Edges) result[edge.Target].Add(block);
        return result;
    }

    private bool Constant(NativeValue value, out BigInteger bits)
    {
        if (definitions.TryGetValue(ssa.Resolve(value).Id, out var node) && node.Code == OpCode.Constant && node.Payload is ImmediatePayload immediate)
        { bits = immediate.Value; return true; }
        bits = 0;
        return false;
    }

    private bool SameBits(NativeValue left, int leftOffset, NativeValue right, int rightOffset, int width)
    {
        var predecessors = Predecessors();
        var active = new HashSet<(BitOrigin, BitOrigin)>();
        for (var bit = 0; bit < width; bit++)
            if (!Match(Bit(left, leftOffset + bit), Bit(right, rightOffset + bit))) return false;
        return true;

        bool Match(BitOrigin actual, BitOrigin expected)
        {
            if (actual == expected) return true;
            if (actual.Constant is not null || !parameterSources.TryGetValue(actual.Value, out var parameter)) return false;
            var pair = (actual, expected);
            if (!active.Add(pair)) return true;
            var incoming = predecessors[parameter.Block.Id];
            var matched = incoming.Count != 0 && incoming.All(parent => Match(Bit(parent.Outputs[parameter.Slot], actual.Offset), expected));
            active.Remove(pair);
            return matched;
        }
    }

    private bool KnownNonFrame(NativeValue value)
    {
        var active = new HashSet<ValueId>();
        var arguments = ssa.LogicalArguments.Select(argument => ssa.Resolve(argument).Id).ToHashSet();
        var predecessors = Predecessors();
        var calls = ssa.Blocks.Where(block => block.Call?.Result is not null)
            .ToDictionary(block => ssa.Resolve(block.Call!.Result!.Value).Id, block => block.Call!);
        return Check(value);

        bool Check(NativeValue current)
        {
            current = ssa.Resolve(current);
            if (arguments.Contains(current.Id)) return true;
            if (!active.Add(current.Id)) return true;
            bool safe;
            if (parameterSources.TryGetValue(current.Id, out var parameter))
                safe = predecessors[parameter.Block.Id].Count != 0 && predecessors[parameter.Block.Id]
                    .All(parent => Check(parent.Outputs[parameter.Slot]));
            else if (calls.TryGetValue(current.Id, out var call)) safe = !HasEscapes && call.Arguments.All(Check);
            else safe = definitions.TryGetValue(current.Id, out var node) && node.Flow is null && node.Code != OpCode.Undefined &&
                node.Inputs.All(Check);
            active.Remove(current.Id);
            return safe;
        }
    }

    private BitOrigin Bit(NativeValue value, int offset)
    {
        for (var step = 0; step <= ssa.ValueCount; step++)
        {
            value = ssa.Resolve(value);
            if (!definitions.TryGetValue(value.Id, out var node)) return new(value.Id, offset, null);
            if (node.Code == OpCode.Constant && node.Payload is ImmediatePayload constant)
                return new(default, 0, ((constant.Value >> offset) & 1) != 0);
            if (node.Code == OpCode.Extract && node.Payload is ImmediatePayload start)
            { offset += (int)start.Value; value = node.Inputs[0]; continue; }
            if (node.Code == OpCode.Concat)
            {
                var lowWidth = ssa.Width(node.Inputs[1]);
                if (offset < lowWidth) value = node.Inputs[1];
                else { offset -= lowWidth; value = node.Inputs[0]; }
                continue;
            }
            if (node.Code is OpCode.Zext or OpCode.Sext)
            {
                var width = ssa.Width(node.Inputs[0]);
                if (offset >= width && node.Code == OpCode.Zext) return new(default, 0, false);
                offset = Math.Min(offset, width - 1);
                value = node.Inputs[0];
                continue;
            }
            if (node.Code is OpCode.Shl or OpCode.Shr or OpCode.Sar && Constant(node.Inputs[1], out var shiftBits))
            {
                var width = ssa.Width(node.Inputs[0]);
                var shift = (int)BigInteger.Min(shiftBits, width);
                if (node.Code == OpCode.Shl)
                {
                    if (offset < shift) return new(default, 0, false);
                    offset -= shift;
                }
                else
                {
                    offset += shift;
                    if (offset >= width)
                    {
                        if (node.Code == OpCode.Shr) return new(default, 0, false);
                        offset = width - 1;
                    }
                }
                value = node.Inputs[0];
                continue;
            }
            if (node.Code is OpCode.And or OpCode.Or or OpCode.Xor)
            {
                var left = Bit(node.Inputs[0], offset);
                var right = Bit(node.Inputs[1], offset);
                if (node.Code == OpCode.Or)
                {
                    if (left.Constant == true || right.Constant == true) return new(default, 0, true);
                    if (left.Constant == false || left == right) return right;
                    if (right.Constant == false) return left;
                }
                else if (node.Code == OpCode.And)
                {
                    if (left.Constant == false || right.Constant == false) return new(default, 0, false);
                    if (left.Constant == true || left == right) return right;
                    if (right.Constant == true) return left;
                }
                else
                {
                    if (left == right) return new(default, 0, false);
                    if (left.Constant == false) return right;
                    if (right.Constant == false) return left;
                    if (left.Constant is { } a && right.Constant is { } b) return new(default, 0, a ^ b);
                }
            }
            return new(value.Id, offset, null);
        }
        throw new InvalidOperationException("Cyclic bit projection in machine SSA");
    }

    private bool ReturnBytes(Dictionary<long, FrameByte> memory) => Enumerable.Range(0, 8).All(offset =>
        memory.TryGetValue(offset, out var piece) && piece.Value is { } value &&
        SameBits(value, piece.ByteOffset * 8, ssa.ReturnAddress, offset * 8, 8));

    private FrameByte NormalizeByte(FrameByte value) => value.Value is { } source ? value with { Value = ssa.Resolve(source) } : value;
    private static void InvalidateAll(Dictionary<long, FrameByte> state)
    {
        state.Clear();
    }

    private static Dictionary<long, FrameByte>? Intersect(Dictionary<long, FrameByte>[] states)
    {
        if (states.Length == 0) return null;
        var result = new Dictionary<long, FrameByte>(states[0]);
        foreach (var state in states.Skip(1))
            foreach (var offset in result.Keys.ToArray())
            {
                if (!state.TryGetValue(offset, out var incoming)) result.Remove(offset);
                else if (result[offset] != incoming) result[offset] = new(null, 0, Math.Min(result[offset].ValidBits, incoming.ValidBits));
            }
        return result;
    }

    private static bool Same(Dictionary<long, FrameByte>? left, Dictionary<long, FrameByte> right) => left is not null &&
        left.Count == right.Count && left.All(pair => right.TryGetValue(pair.Key, out var value) && value == pair.Value);

    private void Diagnostic(ulong address, string code, string message)
    {
        var diagnostic = new NirRecoveryDiagnostic(address, code, message);
        if (!Diagnostics.Contains(diagnostic)) Diagnostics.Add(diagnostic);
    }

    private static OffsetFact Meet(OffsetFact[] values)
    {
        var result = default(OffsetFact);
        foreach (var value in values)
        {
            if (value.Kind == OffsetKind.Other) return value;
            if (value.Kind == OffsetKind.Pending) continue;
            if (result.Kind == OffsetKind.Known && result.Offset != value.Offset) return new(OffsetKind.Other, 0);
            result = value;
        }
        return result;
    }

    private static long Signed64(BigInteger value)
    {
        value &= (BigInteger.One << 64) - 1;
        return (long)(value >= (BigInteger.One << 63) ? value - (BigInteger.One << 64) : value);
    }
    private enum OffsetKind { Pending, Known, Other }
    private readonly record struct OffsetFact(OffsetKind Kind, long Offset);
    private readonly record struct BitOrigin(ValueId Value, int Offset, bool? Constant);
}
