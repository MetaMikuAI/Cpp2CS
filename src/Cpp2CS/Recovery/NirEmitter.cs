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
            var environment = new Dictionary<NirEnvironmentField, NirValue>();
            NirValue? floatingExceptions = null;
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
                    {
                        var memory = ((MemoryPayload)node.Payload).Specification;
                        operations.Add(new NirLoad(result!.Value, Address(node.Inputs[0]), NirByteOrder.Little, Flow(),
                            MemoryOrderFor(memory), memory.AtomicWidth));
                        break;
                    }
                    case OpCode.Store:
                    {
                        var memory = ((MemoryPayload)node.Payload).Specification;
                        operations.Add(new NirStore(Address(node.Inputs[0]), inputs[1], NirByteOrder.Little, Flow(),
                            MemoryOrderFor(memory), memory.AtomicWidth));
                        break;
                    }
                    case OpCode.AtomicRmw:
                    {
                        var atomic = ((AtomicPayload)node.Payload).Specification;
                        var address = Address(node.Inputs[0]);
                        var order = AtomicOrderFor(atomic.Order);
                        if (atomic.Kind == AtomicKind.CompareExchange)
                            operations.Add(new NirCompareExchange(result!.Value, Fresh(new NirBitsType(1)), address,
                                inputs[2], inputs[1], NirByteOrder.Little, order, order, Flow(), WriteBackOnFailure: true));
                        else operations.Add(new NirAtomicRmw(result!.Value, address, inputs[1], AtomicCode(atomic.Kind),
                            NirByteOrder.Little, order, Flow()));
                        break;
                    }
                    case OpCode.Barrier:
                        operations.Add(new NirFence(FenceOrder(((BarrierPayload)node.Payload).Specification)!.Value, Flow()));
                        break;
                    case OpCode.Float:
                    case OpCode.FloatFused:
                    {
                        var source = ((FloatPayload)node.Payload).Specification;
                        var spec = RecoveryFloating.Specification(machine.Graph.Architecture, source);
                        var rounding = source.Rounding == FloatRounding.Current ? Environment(NirEnvironmentField.RoundingMode)
                            : ConstantValue(3, (int)RecoveryFloating.Rounding(source.Rounding));
                        var flushInput = Environment(NirEnvironmentField.FlushSubnormalInput);
                        var flushOutput = Environment(NirEnvironmentField.FlushSubnormalOutput);
                        var enabledUnderflow = Pure(1, NirPureCode.Extract, [Environment(NirEnvironmentField.FloatingTrapMask)], 3);
                        var canonical = machine.Graph.Architecture == Architecture.Arm64
                            ? Environment(NirEnvironmentField.CanonicalNaN) : ConstantValue(1, 0);
                        if (machine.Graph.Architecture == Architecture.X64)
                            flushOutput = Pure(1, NirPureCode.And, [flushOutput, Pure(1, NirPureCode.Not, [enabledUnderflow])]);
                        var data = Fresh(new NirBitsType(spec.ResultWidth));
                        var flags = Fresh(new NirBitsType(6));
                        operations.Add(new NirFloat(data, flags, spec, inputs.Take(spec.InputCount).ToImmutableArray(),
                            new(rounding, flushInput, flushOutput, canonical, enabledUnderflow)));
                        floatingExceptions = floatingExceptions is { } accumulated ? Pure(6, NirPureCode.Or, [accumulated, flags]) : flags;
                        if (source.Kind is FloatKind.Compare or FloatKind.CompareSignal)
                        {
                            var isEqual = Pure(1, NirPureCode.Eq, [data, ConstantValue(2, 0)]);
                            var isLess = Pure(1, NirPureCode.Eq, [data, ConstantValue(2, 1)]);
                            var isGreater = Pure(1, NirPureCode.Eq, [data, ConstantValue(2, 2)]);
                            data = Pure(4, NirPureCode.Select, [isEqual, ConstantValue(4, 6),
                                Pure(4, NirPureCode.Select, [isLess, ConstantValue(4, 8),
                                    Pure(4, NirPureCode.Select, [isGreater, ConstantValue(4, 2), ConstantValue(4, 3)])])]);
                        }
                        var lower = Pure(source.ResultWidth + 6, NirPureCode.Concat, [flags, data]);
                        // 原 trapflags 仅流向已由正常执行域解除的 Guard；不成为逻辑输出。
                        operations.Add(new NirPure(result!.Value, NirPureCode.Concat, [flags, lower]));
                        break;
                    }
                    case OpCode.Undefined:
                        operations.Add(new NirChoose(result!.Value, Flow()));
                        break;
                    default:
                        operations.Add(new NirPure(result!.Value, PureCode(node.Code)!.Value, inputs,
                            node.Code == OpCode.Extract ? checked((int)((ImmediatePayload)node.Payload).Value) : 0));
                        break;
                }
            }
            if (floatingExceptions is { } raised)
            {
                var previous = Environment(NirEnvironmentField.FloatingExceptions);
                var accumulated = Pure(6, NirPureCode.Or, [previous, raised]);
                operations.Add(new NirEnvironmentWrite(NirEnvironmentField.FloatingExceptions, accumulated, Flow()));
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
            NirValue Environment(NirEnvironmentField field)
            {
                if (environment.TryGetValue(field, out var value)) return value;
                value = Fresh(new NirBitsType(NirEnvironmentContract.Width(field)));
                operations.Add(new NirEnvironmentRead(value, field, Flow()));
                environment.Add(field, value);
                return value;
            }
            NirValue ConstantValue(int width, BigInteger bits)
            {
                var value = Fresh(new NirBitsType(width));
                operations.Add(new NirConstant(value, bits));
                return value;
            }
            NirValue Pure(int width, NirPureCode code, ImmutableArray<NirValue> inputs, int offset = 0)
            {
                var value = Fresh(new NirBitsType(width));
                operations.Add(new NirPure(value, code, inputs, offset));
                return value;
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
                if (RecoveryFloating.IsFloating(node.Code))
                {
                    if (!NormalDomain) Gap(block, "floating.trap-domain", "浮点 trap 出口转换需要显式正常执行域，启用掩码仍参与数值计算");
                    if (!machine.Graph.Contract.Effects.ExternalEffects)
                        Gap(block, "contract.floating-effects", "粘滞浮点异常属于可观察环境效应，不能按数值结果不活跃而删除");
                    if (machine.Blocks.Any(candidate => candidate.Call is not null))
                        Gap(block, "floating.call-environment", "混合调用的机器浮点环境关系尚未单独核验");
                    machine.Evidence.Add(new("floating.environment", node.Source.Origin.Address, node.Source.OperationIndex,
                        "控制来自中立环境字段；每机器指令汇总六位异常后更新粘滞状态；机器 trapflags 仅用于正常执行域条件"));
                    Keep(block, node);
                    continue;
                }
                if (block.Call is { } call && node.Source.OperationIndex == call.OperationIndex)
                {
                    Keep(block, node);
                    if (call.Tail && !machine.Evidence.Any(evidence => evidence.Rule == "tail.return-protocol" &&
                        evidence.Address == block.Source!.Address))
                        Gap(block, "tail.frame-proof", "尾调用缺少已完成的本帧移除与实参来源证明");
                    if (call.Summary.Callee.Effects.MayThrow)
                    {
                        if (!call.Tail) Gap(block, "call.unwind", "普通调用缺少源异常处理证据，尚不能恢复本地展开路径");
                        else if (!machine.Graph.Contract.Effects.MayThrow)
                            Gap(block, "contract.call-unwind", "已证明尾调用可能向外抛出异常，但当前函数合同排除该出口");
                    }
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
                    var memory = ((MemoryPayload)node.Payload).Specification;
                    if (memory.NonTemporal)
                        Gap(block, "memory.hint", "非临时内存访问提示尚无对应的 NIR 观察合同");
                    if (frame.TryOffset(node.Inputs[0], out _))
                    {
                        if (!PrivateFrame) Gap(block, "frame.contract", "消除机器帧或转换局部对象需要私有有效帧合同");
                        if (memory.Order != MemoryOrder.Relaxed || memory.AtomicWidth != 0)
                            Gap(block, "memory.atomic-frame", "私有帧上的有序或原子访问不能按普通局部读写消除");
                        continue;
                    }
                    RequireSequential(block, node);
                    if (node.Code == OpCode.Load && !machine.Graph.Contract.Effects.ReadsMemory ||
                        node.Code == OpCode.Store && !machine.Graph.Contract.Effects.WritesMemory)
                        Gap(block, "contract.memory-effects", "机器体访问程序内存，但逻辑合同排除了对应读写效应");
                    if (memory.AtomicWidth != 0)
                        machine.Evidence.Add(new("memory.atomic-beats", node.Source.Origin.Address, node.Source.OperationIndex,
                            $"保留 {memory.Order} 顺序及每次 {memory.AtomicWidth} 位访问；不合并多个观察事件"));
                    Keep(block, node);
                    continue;
                }
                if (node.Code == OpCode.AtomicRmw)
                {
                    if (frame.TryOffset(node.Inputs[0], out _))
                        Gap(block, "memory.atomic-frame", "私有帧上的原子读改写尚无独立局部存储恢复合同");
                    RequireSequential(block, node);
                    if (!NormalDomain)
                        Gap(block, "memory.atomic-address", "原子访问的机器地址与对齐故障需要显式正常执行域");
                    else machine.Evidence.Add(new("domain.atomic-address", node.Source.Origin.Address, node.Source.OperationIndex,
                        "正常执行域采用有效的机器地址与原子访问对齐；NIR 不携带机器地址合法性规则"));
                    if (!machine.Graph.Contract.Effects.ReadsMemory || !machine.Graph.Contract.Effects.WritesMemory)
                        Gap(block, "contract.memory-effects", "机器原子读改写超出函数声明的程序内存读写效应");
                    var atomic = ((AtomicPayload)node.Payload).Specification;
                    machine.Evidence.Add(new("memory.atomic-rmw", node.Source.Origin.Address, node.Source.OperationIndex,
                        $"{atomic.Kind} 保留旧值结果、{atomic.Order} 顺序和完整读改写；比较成功标记不代替旧值"));
                    Keep(block, node);
                    continue;
                }
                if (node.Code == OpCode.Barrier)
                {
                    var barrier = ((BarrierPayload)node.Payload).Specification;
                    if (FenceOrder(barrier) is null)
                        Gap(block, "memory.barrier", "屏障的完成性、取指或共享域要求尚无中立 NIR fence 合同");
                    else
                    {
                        RequireSequential(block, node);
                        if (!machine.Graph.Contract.Effects.ExternalEffects)
                            Gap(block, "contract.barrier-effects", "函数合同排除了机器屏障的可观察顺序效应");
                        machine.Evidence.Add(new("memory.fence", node.Source.Origin.Address, node.Source.OperationIndex,
                            $"在顺序观察域中保留 {barrier.Kind}/{barrier.Domain}/{barrier.Access} 顺序事件"));
                        Keep(block, node);
                    }
                    continue;
                }
                if (node.Code is OpCode.LoadExclusive or OpCode.StoreExclusive or OpCode.ClearExclusive)
                {
                    Gap(block, "memory.exclusive", "LL/SC 监视器协议尚未恢复为有逻辑依据的原子操作");
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
                if (node.Code is not (OpCode.Constant or OpCode.Load or OpCode.AtomicRmw or OpCode.Float or OpCode.FloatFused or OpCode.Undefined) && PureCode(node.Code) is null)
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
        {
            if (RecoveryFloating.IsFloating(node.Code) && index == node.Inputs.Length - 1) continue;
            if (!(index == 0 && node.Code is OpCode.Load or OpCode.Store && frame.TryOffset(node.Inputs[0], out _))) Mark(node.Inputs[index]);
        }
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
    private void RequireSequential(RecoverySsaBlock block, NativeNode node)
    {
        if (!(options.AssumeSequentialMemory || machine.Graph.Contract.Domain?.SequentialMemory == true))
            Gap(block, "memory.concurrent-domain", "内存转换需要显式的顺序内存观察合同；当前验证不求解弱内存执行");
        else machine.Evidence.Add(new("memory.sequential", node.Source.Origin.Address, node.Source.OperationIndex,
            "采用顺序内存观察域，保留原子宽度和顺序标签；不声明跨线程弱内存等价"));
    }
    private static NirMemoryOrder MemoryOrderFor(MemoryOperation memory) => memory.AtomicWidth == 0
        ? NirMemoryOrder.Unordered : AtomicOrderFor(memory.Order);
    private static NirMemoryOrder AtomicOrderFor(MemoryOrder order) => order switch
    {
        MemoryOrder.Relaxed => NirMemoryOrder.Relaxed, MemoryOrder.Acquire => NirMemoryOrder.Acquire,
        MemoryOrder.Release => NirMemoryOrder.Release, MemoryOrder.X64Locked => NirMemoryOrder.SequentiallyConsistent,
        _ => throw new ArgumentOutOfRangeException(nameof(order))
    };
    private static NirMemoryOrder? FenceOrder(BarrierOperation barrier) => barrier switch
    {
        { Kind: BarrierKind.Mfence, Domain: BarrierDomain.FullSystem, Access: BarrierAccess.All } => NirMemoryOrder.SequentiallyConsistent,
        { Kind: BarrierKind.Lfence, Domain: BarrierDomain.FullSystem, Access: BarrierAccess.Loads } => NirMemoryOrder.Acquire,
        { Kind: BarrierKind.Sfence, Domain: BarrierDomain.FullSystem, Access: BarrierAccess.Stores } => NirMemoryOrder.Release,
        { Kind: BarrierKind.Dmb, Domain: BarrierDomain.FullSystem, Access: BarrierAccess.All } => NirMemoryOrder.SequentiallyConsistent,
        { Kind: BarrierKind.Dmb, Domain: BarrierDomain.FullSystem, Access: BarrierAccess.Loads } => NirMemoryOrder.Acquire,
        { Kind: BarrierKind.Dmb, Domain: BarrierDomain.FullSystem, Access: BarrierAccess.Stores } => NirMemoryOrder.Release,
        _ => null
    };
    private static NirAtomicCode AtomicCode(AtomicKind kind) => kind switch
    {
        AtomicKind.Exchange => NirAtomicCode.Exchange, AtomicKind.Add => NirAtomicCode.Add,
        AtomicKind.Sub => NirAtomicCode.Sub, AtomicKind.And => NirAtomicCode.And, AtomicKind.Or => NirAtomicCode.Or,
        AtomicKind.Xor => NirAtomicCode.Xor, AtomicKind.Neg => NirAtomicCode.Neg, AtomicKind.Not => NirAtomicCode.Not,
        _ => throw new ArgumentOutOfRangeException(nameof(kind))
    };
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
