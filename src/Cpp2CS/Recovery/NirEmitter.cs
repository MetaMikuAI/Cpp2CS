using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Ir;
using Cpp2CS.Native;
using Cpp2CS.Nir;

namespace Cpp2CS.Recovery;

// 仅逻辑语义切片进入 NIR；机器状态、证明条件和来源留在 Recovery。
internal sealed class NirEmitter(RecoveryMachineSsa machine, RecoveryFrameAnalysis frame, NirRecoveryOptions options)
{
    private readonly HashSet<ValueId> live = [];
    private readonly HashSet<(int Block, int Operation)> retained = [];
    private readonly List<NirRecoveryDiagnostic> diagnostics = [];
    private readonly Dictionary<ValueId, (RecoverySsaBlock Block, NativeNode Node)> definitions = machine.Blocks
        .SelectMany(block => block.Nodes.Where(node => node.Result is not null).Select(node => (block, node)))
        .ToDictionary(pair => pair.node.Result!.Value.Id, pair => (pair.block, pair.node));
    private readonly Dictionary<ValueId, (RecoverySsaBlock Block, BlockParameter Parameter)> parameters = machine.Blocks
        .SelectMany(block => block.Parameters.Select(parameter => (block, parameter)))
        .ToDictionary(pair => pair.parameter.Value.Id, pair => (pair.block, pair.parameter));
    private readonly Queue<NativeValue> pending = new();
    private int nextValue = machine.ValueCount;
    private long frameStart;
    private long frameEnd;
    private NirValue? local;
    private readonly List<(long Offset, FrameByte Byte)> initialFrame = [];
    private bool NormalDomain => options.AssumeNormalExecution || machine.Graph.Contract.Domain?.NormalExecution == true;
    private bool PrivateFrame => options.AssumePrivateValidFrames || machine.Graph.Contract.Domain?.ValidPrivateFrame == true;
    public IReadOnlyList<NirRecoveryDiagnostic> Diagnostics => diagnostics;
    public int EliminatedFrameAccesses { get; private set; }

    public NirFunction? Emit()
    {
        SelectSlice();
        if (diagnostics.Count != 0) return null;
        var selectedParameters = machine.Blocks.ToDictionary(block => block.Id, block => block == machine.Entry
            ? Array.Empty<BlockParameter>() : block.Parameters.Where(parameter => parameter.Slot is not null && live.Contains(parameter.Value.Id) &&
                machine.Resolve(parameter.Value) == parameter.Value).ToArray());
        var effects = machine.Blocks.ToDictionary(block => block.Id, _ => Fresh(NirEffectType.Instance));
        var blocks = ImmutableArray.CreateBuilder<NirBlock>();
        var signature = NirRecovery.Signature(machine.Graph.Contract.Signature);
        if (frameEnd > frameStart) local = Fresh(new NirAddressType("memory", 64));
        foreach (var block in machine.Blocks)
        {
            var operations = new List<NirOperation>();
            var blockParameters = new List<NirValue>();
            var effect = effects[block.Id];
            if (block == machine.Entry)
            {
                for (var index = 0; index < machine.LogicalArguments.Count; index++)
                {
                    var bits = Bits(machine.LogicalArguments[index]);
                    if (signature.Parameters[index] is NirAddressType address)
                    {
                        var argument = Fresh(address);
                        blockParameters.Add(argument);
                        if (live.Contains(machine.LogicalArguments[index].Id))
                            operations.Add(new NirPure(bits, NirPureCode.AddressToBits, [argument]));
                    }
                    else blockParameters.Add(bits);
                }
                if (local is { } storage)
                {
                    var size = Fresh(new NirBitsType(64));
                    operations.Add(new NirConstant(size, frameEnd - frameStart));
                    operations.Add(new NirLocalAlloc(storage, size, 16, Flow()));
                    foreach (var initial in initialFrame)
                    {
                        var value = Fresh(new NirBitsType(8));
                        operations.Add(new NirPure(value, NirPureCode.Extract, [Bits(initial.Byte.Value!.Value)], initial.Byte.ByteOffset * 8));
                        operations.Add(new NirStore(LocalAddress(initial.Offset), value, NirByteOrder.Little, Flow()));
                    }
                }
            }
            else blockParameters.AddRange(selectedParameters[block.Id].Select(parameter => Bits(parameter.Value)));
            blockParameters.Add(effects[block.Id]);
            foreach (var node in block.Nodes)
            {
                if (!retained.Contains(Key(block, node))) continue;
                var inputs = node.Inputs.Select(Bits).ToImmutableArray();
                var result = node.Result is { } value ? Bits(value) : (NirValue?)null;
                if (block.Call is { } call && call.OperationIndex == node.Source.OperationIndex)
                {
                    if (call.Tail || !call.Summary.Callee.Effects.MayReturn) continue;
                    var args = CallArguments(call);
                    if (call.Summary.Callee.Signature.Result is { Kind: RecoveryScalarKind.Address } type)
                    {
                        var returned = Fresh(NirRecovery.Type(type));
                        operations.Add(new NirCall(new NirDirectTarget(call.Summary.Callee.Name), args, [returned], Flow()));
                        operations.Add(new NirPure(result!.Value, NirPureCode.AddressToBits, [returned]));
                    }
                    else operations.Add(new NirCall(new NirDirectTarget(call.Summary.Callee.Name), args,
                        result is { } returned ? [returned] : [], Flow()));
                    continue;
                }
                switch (node.Code)
                {
                    case OpCode.Constant:
                        operations.Add(new NirConstant(result!.Value, ((ImmediatePayload)node.Payload).Value));
                        break;
                    case OpCode.Load:
                        operations.Add(new NirLoad(result!.Value, Address(node.Inputs[0]), NirByteOrder.Little, Flow()));
                        break;
                    case OpCode.Store:
                        operations.Add(new NirStore(Address(node.Inputs[0]), inputs[1], NirByteOrder.Little, Flow()));
                        break;
                    case OpCode.Undefined:
                        operations.Add(new NirChoose(result!.Value, Flow()));
                        break;
                    default:
                        operations.Add(new NirPure(result!.Value, PureCode(node.Code)!.Value, inputs,
                            node.Code == OpCode.Extract ? checked((int)((ImmediatePayload)node.Payload).Value) : 0));
                        break;
                }
            }
            NirTerminator terminator;
            if (block.Call is { } transfer && (transfer.Tail || !transfer.Summary.Callee.Effects.MayReturn))
            {
                var args = CallArguments(transfer);
                var target = new NirDirectTarget(transfer.Summary.Callee.Name);
                terminator = transfer.Tail ? new NirTailCall(target, args, effect) : new NirNoReturnCall(target, args, effect);
            }
            else if (block.Source?.Edges.Any(edge => edge.Kind == DerivedEdgeKind.Return) == true)
                terminator = new NirReturn(block.ReturnValue is { } returned
                    ? [Logical(returned, machine.Graph.Contract.Signature.Result!)] : [], effect);
            else if (block.Edges.Count == 2)
            {
                var taken = block.Edges.Single(edge => edge.Source?.Source.Condition?.RequiredValue == true);
                var other = block.Edges.Single(edge => edge.Source?.Source.Condition?.RequiredValue == false);
                terminator = new NirBranch(Bits(block.Condition!.Value), Edge(taken.Target), Edge(other.Target));
            }
            else if (block.Edges.Count == 1) terminator = new NirJump(Edge(block.Edges[0].Target));
            else throw new InvalidOperationException("Closed recovered block has no logical terminator");
            blocks.Add(new(new(block.Id), blockParameters.ToImmutableArray(), operations.ToImmutableArray(), terminator));

            NirEffectFlow Flow()
            {
                var input = effect;
                effect = Fresh(NirEffectType.Instance);
                return new(input, effect);
            }
            NirValue Address(NativeValue value)
            {
                if (frame.TryOffset(value, out var offset))
                    return LocalAddress(offset);
                var converted = Fresh(new NirAddressType("memory", machine.Width(value)));
                operations.Add(new NirPure(converted, NirPureCode.BitsToAddress, [Bits(value)]));
                return converted;
            }
            NirValue LocalAddress(long offset)
            {
                var delta = Fresh(new NirBitsType(64));
                var address = Fresh(new NirAddressType("memory", 64));
                operations.Add(new NirConstant(delta, offset - frameStart));
                operations.Add(new NirPure(address, NirPureCode.AddressAdd, [local!.Value, delta]));
                return address;
            }
            NirValue Logical(NativeValue value, RecoveryScalarType type) => type.Kind == RecoveryScalarKind.Address ? Address(value) : Bits(value);
            ImmutableArray<NirValue> CallArguments(RecoverySsaCall call) => call.Arguments.Select((value, index) =>
                Logical(value, call.Summary.Callee.Signature.Arguments[index])).ToImmutableArray();
            NirEdge Edge(int target) => new(new(target), selectedParameters[target]
                .Select(parameter => Bits(block.Outputs[parameter.Slot!])).Append(effect).ToImmutableArray());
        }
        return new(machine.Graph.Contract.Name, signature, new(machine.Entry.Id), blocks.ToImmutable())
        { Outcomes = NirRecovery.Outcomes(machine.Graph.Contract) };
    }

    private void SelectSlice()
    {
        foreach (var block in machine.Blocks)
        {
            if (block.Condition is { } condition) Mark(condition);
            if (block.ReturnValue is { } returned) Mark(returned);
            if (block.Source?.Edges.Any(edge => edge.Kind == DerivedEdgeKind.Return) == true && !machine.Graph.Contract.Effects.MayReturn)
                Gap(block, "contract.return", "函数合同排除正常返回，但机器体存在返回出口");
            foreach (var node in block.Nodes)
            {
                if (block.Call is { } call && node.Source.OperationIndex == call.OperationIndex)
                {
                    Keep(block, node);
                    if (call.Summary.Callee.Effects.MayThrow) Gap(block, "call.unwind", "语言异常调用尚无 NIR unwind 转换");
                    if (Constant(call.Target) is { } target && target != call.Summary.Callee.EntryAddress)
                        Gap(block, "contract.call-target", "已知机器调用目标与采用的被调合同入口矛盾");
                    if (call.Tail && call.Summary.Callee.Effects.MayReturn && !machine.Graph.Contract.Effects.MayReturn)
                        Gap(block, "contract.return", "尾调用可能返回，但当前函数合同排除返回");
                    if (call.Summary.Callee.Effects.MayTerminate && !machine.Graph.Contract.Effects.MayTerminate)
                        Gap(block, "contract.call-outcome", "被调函数可能终止，但当前函数合同排除该出口");
                    var effects = call.Summary.Callee.Effects;
                    var ownerEffects = machine.Graph.Contract.Effects;
                    if (effects.ReadsMemory && !ownerEffects.ReadsMemory || effects.WritesMemory && !ownerEffects.WritesMemory ||
                        effects.ExternalEffects && !ownerEffects.ExternalEffects)
                        Gap(block, "contract.call-effects", "被调合同的内存或环境效应超出当前函数声明");
                    continue;
                }
                if (node.Code == OpCode.Guard)
                {
                    var guard = (GuardPayload)node.Payload;
                    var constant = Constant(node.Inputs[0]);
                    if (constant == BigInteger.One) continue;
                    if (constant == BigInteger.Zero || !NormalDomain || guard.Kind == StopKind.UnmodeledSemantics)
                        Gap(block, "guard.domain", $"不能解除机器条件: {guard.Kind}: {guard.Reason}");
                    else machine.Evidence.Add(new("domain.normal", node.Source.Origin.Address, node.Source.OperationIndex, guard.Reason));
                    continue;
                }
                if (node.Code == OpCode.CodeGuarded)
                {
                    if (!NormalDomain) Gap(block, "environment.code-page", "代码页环境依赖尚未在正常执行合同中解除");
                    continue;
                }
                if (node.Code == OpCode.WriteProbe && frame.TryOffset(node.Inputs[0], out _) && PrivateFrame)
                {
                    machine.Evidence.Add(new("frame.valid", node.Source.Origin.Address, node.Source.OperationIndex, "私有有效栈写入探测"));
                    continue;
                }
                if (node.Code is OpCode.Load or OpCode.Store)
                {
                    if (node.Payload is not MemoryPayload { Specification.Order: MemoryOrder.Relaxed, Specification.NonTemporal: false })
                        Gap(block, "memory.order", "当前 NIR 转换尚不支持该内存顺序或访问提示");
                    if (frame.TryOffset(node.Inputs[0], out _))
                    {
                        if (!PrivateFrame) Gap(block, "frame.contract", "消除机器帧或转换局部对象需要私有有效帧合同");
                        continue;
                    }
                    if (!(options.AssumeSequentialMemory || machine.Graph.Contract.Domain?.SequentialMemory == true))
                        Gap(block, "memory.concurrent-domain", "顺序字节内存转换需要显式的顺序内存观察合同");
                    else machine.Evidence.Add(new("memory.sequential", node.Source.Origin.Address, node.Source.OperationIndex,
                        "采用顺序内存观察合同；不声明并发原子性等价"));
                    if (node.Code == OpCode.Load && !machine.Graph.Contract.Effects.ReadsMemory ||
                        node.Code == OpCode.Store && !machine.Graph.Contract.Effects.WritesMemory)
                        Gap(block, "contract.memory-effects", "机器体访问程序内存，但逻辑合同排除了对应读写效应");
                    Keep(block, node);
                    continue;
                }
                if (node.Flow is not null && node.Code != OpCode.Undefined)
                    Gap(block, "effect.unsupported", $"尚未转换机器效应 {node.Code}");
            }
        }
        Drain();
        // 内存 SSA 保留有歧义但已初始化的局部读写；只转发有逐字节证据的读取。
        var changed = true;
        while (changed)
        {
            changed = false;
            var loads = machine.Blocks.SelectMany(block => block.Nodes.Select(node => (block, node)))
                .Where(pair => pair.node.Code == OpCode.Load && retained.Contains(Key(pair.block, pair.node)) &&
                    frame.TryOffset(pair.node.Inputs[0], out _)).Select(pair => Range(pair.node)).ToArray();
            foreach (var block in machine.Blocks)
            foreach (var node in block.Nodes.Where(node => node.Code == OpCode.Store && frame.TryOffset(node.Inputs[0], out _)))
            {
                var range = Range(node);
                if (loads.Any(load => range.Start < load.End && load.Start < range.End) && retained.Add(Key(block, node)))
                {
                    Mark(node.Inputs[1]);
                    changed = true;
                }
            }
            Drain();
        }
        foreach (var block in machine.Blocks)
        foreach (var node in block.Nodes.Where(node => node.Code is OpCode.Load or OpCode.Store && frame.TryOffset(node.Inputs[0], out _)))
        {
            if (!retained.Contains(Key(block, node))) { EliminatedFrameAccesses++; continue; }
            var range = Range(node);
            frameStart = Math.Min(frameStart, range.Start);
            frameEnd = Math.Max(frameEnd, range.End);
            if (node.Code == OpCode.Load && !frame.InitializedLoads.Contains(node.Result!.Value.Id))
                Gap(block, "frame.uninitialized", "保留的局部读取没有所有路径上的初始化证据");
        }
        if (EliminatedFrameAccesses != 0) machine.Evidence.Add(new("frame.private", machine.Graph.Contract.EntryAddress, null,
            $"在私有有效帧合同下消除 {EliminatedFrameAccesses} 次协议或已证明的局部访问"));
        var reads = machine.Blocks.SelectMany(block => block.Nodes.Where(node => node.Code == OpCode.Load &&
            retained.Contains(Key(block, node)) && frame.TryOffset(node.Inputs[0], out _))).Select(Range).ToArray();
        foreach (var (offset, value) in machine.EntryBytes)
        {
            if (!reads.Any(range => offset >= range.Start && offset < range.End)) continue;
            if (value.Value is not { } source || value.ByteOffset * 8 + 8 > machine.Width(source))
            { Gap(machine.Entry, "frame.entry-padding", "保留的局部读取依赖栈参数未定义的填充位"); continue; }
            initialFrame.Add((offset, value));
            Mark(source);
        }
        Drain();
        if (new BigInteger(frameEnd) - frameStart > (BigInteger.One << 32))
            Gap(machine.Entry, "frame.object-size", "恢复的局部区间超过当前模块明确提供的分配范围");
    }

    private void Drain()
    {
        while (pending.TryDequeue(out var value))
        {
            if (machine.LogicalArguments.Contains(value)) continue;
            if (definitions.TryGetValue(value.Id, out var definition))
            {
                var (block, node) = definition;
                var info = block.Information.GetValueOrDefault(node.Source.OperationIndex);
                if (info?.Role is RecoveryValueRole.UnboundInput or RecoveryValueRole.CallClobber or RecoveryValueRole.StackBase or RecoveryValueRole.ReturnAddress)
                {
                    Gap(block, info.Role is RecoveryValueRole.UnboundInput or RecoveryValueRole.CallClobber
                        ? "contract.machine-input" : "value.machine-dependency", $"逻辑结果仍依赖未恢复的机器值: {info.Detail}");
                    continue;
                }
                if (node.Code is not (OpCode.Constant or OpCode.Load or OpCode.Undefined) && PureCode(node.Code) is null)
                { Gap(block, "value.unsupported", $"尚未转换纯值操作 {node.Code}"); continue; }
                Keep(block, node);
            }
            else if (parameters.TryGetValue(value.Id, out var parameter) && parameter.Parameter.Slot is { } slot)
            {
                foreach (var parent in machine.Blocks.Where(parent => parent.Edges.Any(edge => edge.Target == parameter.Block.Id)))
                    Mark(parent.Outputs[slot]);
            }
            else throw new InvalidOperationException($"Recovery SSA value {value.Id.Id} has no definition");
        }
    }
    private void Keep(RecoverySsaBlock block, NativeNode node)
    {
        if (!retained.Add(Key(block, node))) return;
        for (var index = 0; index < node.Inputs.Length; index++)
            if (!(index == 0 && node.Code is OpCode.Load or OpCode.Store && frame.TryOffset(node.Inputs[0], out _))) Mark(node.Inputs[index]);
    }
    private void Mark(NativeValue value)
    {
        value = machine.Resolve(value);
        if (live.Add(value.Id)) pending.Enqueue(value);
    }
    private BigInteger? Constant(NativeValue value) => definitions.TryGetValue(machine.Resolve(value).Id, out var found) &&
        found.Node.Code == OpCode.Constant ? ((ImmediatePayload)found.Node.Payload).Value : null;
    private (long Start, long End) Range(NativeNode node)
    {
        if (!frame.TryOffset(node.Inputs[0], out var start)) throw new InvalidOperationException("Not a frame access");
        var width = machine.Width(node.Code == OpCode.Store ? node.Inputs[1] : node.Result!.Value);
        return (start, checked(start + width / 8));
    }
    private void Gap(RecoverySsaBlock block, string code, string message) => diagnostics.Add(new(block.Source?.Address ?? machine.Graph.Contract.EntryAddress, code, message));
    private static (int, int) Key(RecoverySsaBlock block, NativeNode node) => (block.Id, node.Source.OperationIndex);
    private NirValue Fresh(NirType type) => new(new(nextValue++), type);
    private NirValue Bits(NativeValue value)
    {
        value = machine.Resolve(value);
        return NirValue.Bits(value.Id.Id, machine.Width(value));
    }
    private static NirPureCode? PureCode(OpCode code) => code switch
    {
        OpCode.Add => NirPureCode.Add, OpCode.Sub => NirPureCode.Sub, OpCode.Mul => NirPureCode.Mul,
        OpCode.And => NirPureCode.And, OpCode.Or => NirPureCode.Or, OpCode.Xor => NirPureCode.Xor, OpCode.Not => NirPureCode.Not,
        OpCode.Shl => NirPureCode.Shl, OpCode.Shr => NirPureCode.Shr, OpCode.Sar => NirPureCode.Sar,
        OpCode.UDiv => NirPureCode.UDiv, OpCode.SDiv => NirPureCode.SDiv, OpCode.Eq => NirPureCode.Eq,
        OpCode.Ult => NirPureCode.Ult, OpCode.Slt => NirPureCode.Slt, OpCode.Select => NirPureCode.Select,
        OpCode.Zext => NirPureCode.Zext, OpCode.Sext => NirPureCode.Sext, OpCode.Extract => NirPureCode.Extract,
        OpCode.Concat => NirPureCode.Concat, _ => null
    };
}
