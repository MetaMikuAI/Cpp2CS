using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Targets.Frontend;

/// <summary>发现指令后按地址组块；块入口状态按需构造。实例及输入不保存跨函数可变状态。</summary>
public static class FunctionLifter
{
    public static LiftResult Lift(IInstructionSet instructionSet, RegisterConvention convention, IFlowFacts facts,
        FunctionRange range, ulong entry, IComparer<ulong>? discoveryOrder = null, Action<LiftPhase>? phaseCompleted = null)
        => new Session(instructionSet, convention, facts, range, entry, discoveryOrder, phaseCompleted).Run();

    private sealed record Node(ulong Address, int Length, Emission Emission, Transfer Transfer, bool Explicit);
    internal sealed class Draft(ulong address)
    {
        internal ulong Address { get; } = address;
        internal ulong TraceAddress { get; init; } = address;
        internal BlockIdentity Identity { get; } = new();
        internal Dictionary<Register, Term> State { get; } = [];
        internal List<Statement> Statements { get; } = [];
        internal List<Draft> Predecessors { get; } = [];
        internal List<(ulong Address, Term Value, long Offset)> StackChecks { get; } = [];
        internal Term? IndirectTarget { get; set; }
        internal ulong IndirectAddress { get; set; }
        internal Terminator End { get; set; } = new Unreachable();
    }

    private sealed class Session(IInstructionSet isa, RegisterConvention convention, IFlowFacts facts,
        FunctionRange range, ulong entry, IComparer<ulong>? discoveryOrder, Action<LiftPhase>? phaseCompleted)
    {
        private readonly TermTable terms = new();
        private readonly SortedDictionary<ulong, Node> nodes = [];
        private readonly Dictionary<ulong, Draft> drafts = [];
        private readonly Dictionary<ulong, Draft> blockAt = [];
        private readonly Dictionary<(ulong Source, ulong Target), Draft> tails = [];
        private readonly Dictionary<ulong, IndirectResolution> resolutions = [];
        private ulong syntheticKey = ulong.MaxValue;
        private LiftResult Hole(ulong address, string code, string message) => new(null, new(address, new(code, message)));
        private bool Inside(ulong address) => address >= range.Start && address - range.Start < range.Length;
        internal LiftResult Run()
        {
            Validate();
            if (!Inside(entry)) return Hole(entry, "entry-range", "入口不在函数范围内。");
            while (true)
            {
                drafts.Clear(); blockAt.Clear(); tails.Clear(); syntheticKey = ulong.MaxValue;
                var failure = Discover();
                phaseCompleted?.Invoke(LiftPhase.Discovery);
                if (failure is not null) return failure;
                var ordered = nodes.Values.ToArray();
                for (int i = 1; i < ordered.Length; i++)
                    if (ordered[i - 1].Length > 0 && ordered[i].Address - ordered[i - 1].Address < (ulong)ordered[i - 1].Length)
                        return Hole(ordered[i].Address, "instruction-overlap", "控制转移落入指令内部。");
                var leaders = new HashSet<ulong> { entry };
                foreach (var node in ordered)
                    if (node.Explicit) foreach (var target in DiscoveryTargets(node)) if (Inside(target)) leaders.Add(target);
                Draft? current = null;
                Node? previous = null;
                foreach (var node in ordered)
                {
                    if (current is null || leaders.Contains(node.Address) || previous!.Explicit ||
                        previous.Address + (ulong)previous.Length != node.Address)
                    {
                        current = new(node.Address);
                        drafts.Add(node.Address, current);
                    }
                    previous = node;
                }
                current = null;
                foreach (var node in ordered)
                {
                    if (drafts.TryGetValue(node.Address, out var start)) current = start;
                    blockAt[node.Address] = current!;
                }
                current = null;
                foreach (var node in ordered)
                {
                    if (drafts.TryGetValue(node.Address, out var start)) current = start;
                    var block = current!;
                    // 每条指令独立求值，按指令边界一次性接入块状态。
                    var map = new TermRewrite(terms, t => t.Identity is RegisterInput input
                        ? ReadBlock(block, input.Register) : null);
                    var writes = node.Emission.State.Select(p => (p.Key, Value: map.Map(p.Value))).ToArray();
                    block.Statements.AddRange(node.Emission.Statements.Select(map.Statement));
                    var transfer = map.Transfer(node.Transfer);
                    foreach (var (register, value) in writes) block.State[register] = value;
                    if (transfer is Indirect indirect)
                    {
                        block.IndirectTarget = indirect.Target;
                        block.IndirectAddress = node.Address;
                    }
                    if (transfer is Finished { End: Return }) block.StackChecks.Add((node.Address, ReadBlock(block, convention.StackPointer), convention.ReturnStackOffset));
                    block.End = transfer is Indirect && resolutions.TryGetValue(node.Address, out var known) && known is IndirectTable knownTable
                        ? Lower(new TableTransfer(knownTable), node.Address) : Lower(transfer, node.Address);
                }
                var byIdentity = drafts.Values.ToDictionary(b => b.Identity);
                foreach (var block in drafts.Values)
                    foreach (var target in Targets(block.End).Distinct())
                        byIdentity[target].Predecessors.Add(block);
                phaseCompleted?.Invoke(LiftPhase.Composition);
                bool newTargets = false;
                foreach (var block in drafts.Values.Where(b => b.IndirectTarget is not null).ToArray())
                {
                    var resolution = facts.ResolveIndirect(block.IndirectAddress, block.IndirectTarget!, new FlowContext(terms, block, entry));
                    ArgumentNullException.ThrowIfNull(resolution);
                    if (resolution is IndirectUnknown unknown) return new(null, new(block.IndirectAddress, unknown.Reason));
                    var oldTargets = resolutions.TryGetValue(block.IndirectAddress, out var old) && old is IndirectTable oldTable
                        ? oldTable.Cases.Select(c => c.Target).Append(oldTable.Default).Order().ToArray() : [];
                    var nextTargets = resolution is IndirectTable nextTable
                        ? nextTable.Cases.Select(c => c.Target).Append(nextTable.Default).Order().ToArray() : [];
                    newTargets |= !oldTargets.SequenceEqual(nextTargets);
                    resolutions[block.IndirectAddress] = resolution;
                    if (resolution is IndirectTable table)
                    {
                        if (table.Selector.Table != terms) throw new ArgumentException("解析结果必须来自本函数项表。");
                        newTargets |= table.Cases.Select(c => c.Target).Append(table.Default).Any(t => Inside(t) && !nodes.ContainsKey(t));
                    }
                }
                // 新边可能改变块划分和唯一前驱；下一次组块后重新询问所有间接跳转。
                phaseCompleted?.Invoke(LiftPhase.IndirectResolution);
                if (newTargets) continue;
                foreach (var block in drafts.Values.Where(b => b.IndirectTarget is not null).ToArray())
                {
                    switch (resolutions[block.IndirectAddress])
                    {
                        case IndirectTable table: block.End = Lower(new TableTransfer(table), block.IndirectAddress); break;
                        case IndirectTailCall tail:
                            block.StackChecks.Add((block.IndirectAddress, ReadBlock(block, convention.StackPointer), convention.TailCallStackOffset));
                            var emitter = new Emission(block.IndirectAddress, terms, isa.Registers, convention, facts);
                            emitter.Call(new ComputedTarget(tail.Target));
                            if (emitter.End is null) emitter.Return();
                            var map = new TermRewrite(terms, t => t.Identity is RegisterInput input && input.Address == block.IndirectAddress
                                ? ReadBlock(block, input.Register) : null);
                            block.Statements.AddRange(emitter.Statements.Select(map.Statement));
                            block.End = map.End(((Finished)emitter.End!).End);
                            break;
                        default: throw new InvalidOperationException("未支持的间接解析结果。");
                    }
                }
                foreach (var block in drafts.Values) block.Predecessors.Clear();
                byIdentity = drafts.Values.ToDictionary(b => b.Identity);
                foreach (var block in drafts.Values)
                    foreach (var target in Targets(block.End).Distinct()) byIdentity[target].Predecessors.Add(block);
                var frame = terms.Atom(new RootAtom(AddressRoot.Frame), convention.StackPointer.Width);
                var initial = new Draft(entry);
                initial.End = new Jump(drafts[entry].Identity);
                drafts[entry].Predecessors.Insert(0, initial);
                initial.State[convention.StackPointer] = frame;
                var builder = new FunctionBuilder(terms, initial.Identity, frame.Width, new(frame))
                {
                    ImageBase = terms.Atom(new RootAtom(AddressRoot.Image), frame.Width),
                    ThreadPointer = terms.Atom(new RootAtom(AddressRoot.Thread), frame.Width),
                    IncomingArgumentArea = Offset(frame, convention.IncomingAreaOffset)
                };
                foreach (var slot in convention.Arguments)
                {
                    var value = terms.Atom(new EntryAtom(slot.Slot), slot.Register.Width);
                    initial.State.Add(slot.Register, value);
                    builder.Inputs.Add(new(slot.Slot, value, slot.Role));
                }
                var ssa = new SparseSsa(terms, drafts, initial, convention);
                builder.Blocks.Add(new(initial.Identity, [], [], initial.End));
                builder.Blocks.AddRange(ssa.Build());
                var function = builder.Freeze();
                phaseCompleted?.Invoke(LiftPhase.Ssa);
                if (ssa.BadStackAddress is { } badStack) return Hole(badStack, "stack-restore", "返回或尾调用处栈指针不等于约定的入口帧偏移。");
                var check = ExitChecker.Check(function);
                phaseCompleted?.Invoke(LiftPhase.ExitCheck);
                if (!check.IsValid) throw new InvalidOperationException(string.Join("; ", check.Violations.Select(v => v.Code + ": " + v.Message)));
                if (!check.Holes.IsEmpty) return new(null, new(entry, check.Holes[0].Reason));
                return new(function, null);
            }
        }
        private void Validate()
        {
            if (isa.Registers.IsDefaultOrEmpty || isa.Registers.Any(r => r.Width <= 0 || string.IsNullOrWhiteSpace(r.Name)) ||
                isa.Registers.Select(r => r.Name).Distinct().Count() != isa.Registers.Length)
                throw new ArgumentException("寄存器文件必须有唯一名称和正位宽。");
            var all = isa.Registers.ToHashSet();
            if (!all.Contains(convention.StackPointer) || !convention.Preserved.IsSubsetOf(all) || convention.CallerValues.IsDefault || convention.CallerValues.Any(r => !all.Contains(r)))
                throw new ArgumentException("调用约定引用了未知寄存器。");
            if (convention.PreservedParts.IsDefault) throw new ArgumentException("保存位段集合必须初始化。");
            if (convention.CallerValues.Distinct().Count() != convention.CallerValues.Length ||
                convention.Preserved.Any(r => !convention.CallerValues.Contains(r)) ||
                convention.PreservedParts.Any(p => !convention.CallerValues.Contains(p.Register)))
                throw new ArgumentException("有序调用方值必须包含全部保存单元且不能重复。");
            foreach (var group in convention.PreservedParts.GroupBy(p => p.Register))
            {
                if (!all.Contains(group.Key) || convention.Preserved.Contains(group.Key) || group.Key == convention.StackPointer)
                    throw new ArgumentException("部分保存必须引用独立的非整单元保存寄存器。");
                int end = 0;
                foreach (var part in group.OrderBy(p => p.Low))
                {
                    if (part.Low < end || part.Width <= 0 || (long)part.Low + part.Width > group.Key.Width)
                        throw new ArgumentException("保存位段不能重叠或越过单元边界。");
                    end = part.Low + part.Width;
                }
            }
            foreach (var slots in new[] { convention.Arguments, convention.Results })
                if (slots.IsDefault || slots.Any(s => !all.Contains(s.Register) || s.Register == convention.StackPointer) ||
                    slots.Select(s => s.Register).Distinct().Count() != slots.Length || slots.Select(s => s.Slot).Distinct().Count() != slots.Length)
                    throw new ArgumentException("槽位映射必须唯一且不能占用 SP。");
        }
        private LiftResult? Discover()
        {
            var pending = new SortedSet<ulong>(discoveryOrder) { entry };
            foreach (var table in resolutions.Values.OfType<IndirectTable>())
                foreach (var target in table.Cases.Select(c => c.Target).Append(table.Default)) if (Inside(target)) pending.Add(target);
            while (pending.Count != 0)
            {
                var address = pending.Min;
                pending.Remove(address);
                if (nodes.ContainsKey(address)) continue;
                var emitter = new Emission(address, terms, isa.Registers, convention, facts);
                var decoded = isa.Decode(address);
                if (decoded.Instruction is not { } instruction)
                    return new(null, new(address, decoded.Failure ?? new("decode", "解码器未提供指令或失败原因。")));
                var length = instruction.Length;
                if (length <= 0 || (ulong)length > range.Length - (address - range.Start))
                    return Hole(address, "instruction-range", "指令长度无效或越出函数范围。");
                instruction.Emit(emitter);
                if (emitter.Failure is { } reason) return new(null, new(address, reason));
                var explicitTransfer = emitter.End is not null;
                if (!explicitTransfer && (address > ulong.MaxValue - (ulong)length || !Inside(address + (ulong)length)))
                    return Hole(address, "fallthrough-range", "指令隐式落出函数范围。");
                var transfer = emitter.End ?? new Direct(address + (ulong)length);
                nodes.Add(address, new(address, length, emitter, transfer, explicitTransfer));
                foreach (var target in Targets(transfer)) if (Inside(target) && !nodes.ContainsKey(target)) pending.Add(target);
            }
            return null;
        }
        private IEnumerable<ulong> DiscoveryTargets(Node node) => node.Transfer is Indirect && resolutions.TryGetValue(node.Address, out var result)
            && result is IndirectTable table ? table.Cases.Select(c => c.Target).Append(table.Default) : Targets(node.Transfer);
        private Term ReadBlock(Draft block, Register register) => block.State.TryGetValue(register, out var value)
            ? value : terms.Atom(new RegisterInput(block.Address, register), register.Width);
        private Term Offset(Term basis, long offset) => offset == 0 ? basis : terms.Apply(new CoreOperator(CoreOperation.Add), basis.Width,
            basis, terms.Constant((new BigInteger(offset) + (BigInteger.One << basis.Width)) % (BigInteger.One << basis.Width), basis.Width));
        private Terminator Lower(Transfer transfer, ulong source) => transfer switch
        {
            Direct d => new Jump(BlockFor(d.Target, source)),
            Conditional c => new Branch(c.Condition, BlockFor(c.Yes, source), BlockFor(c.No, source)),
            TableTransfer t => new JumpTable(t.Resolution.Selector, t.Resolution.Cases.OrderBy(c => c.Value)
                .Select(c => new SwitchCase(c.Value, BlockFor(c.Target, source))).ToImmutableArray(), BlockFor(t.Resolution.Default, source)),
            Finished f => f.End,
            Indirect => new Unreachable(),
            _ => throw new InvalidOperationException()
        };
        // 隐式落入当前块的临时终结会被下一条指令覆盖。
        private BlockIdentity BlockFor(ulong address, ulong source)
        {
            if (Inside(address)) return blockAt[address].Identity;
            if (tails.TryGetValue((source, address), out var existing)) return existing.Identity;
            while (nodes.ContainsKey(syntheticKey) || drafts.ContainsKey(syntheticKey)) syntheticKey--;
            var tail = new Draft(syntheticKey--) { TraceAddress = source };
            drafts.Add(tail.Address, tail);
            tails.Add((source, address), tail);
            var emitter = new Emission(source, terms, isa.Registers, convention, facts);
            emitter.Call(new ImageFunction(address));
            if (emitter.End is null) emitter.Return();
            var map = new TermRewrite(terms, t => t.Identity is RegisterInput input
                ? terms.Atom(new RegisterInput(tail.Address, input.Register), input.Register.Width) : null);
            foreach (var (register, value) in emitter.State) tail.State[register] = map.Map(value);
            tail.StackChecks.Add((source, terms.Atom(new RegisterInput(tail.Address, convention.StackPointer), convention.StackPointer.Width), convention.TailCallStackOffset));
            tail.Statements.AddRange(emitter.Statements.Select(map.Statement));
            tail.End = map.End(((Finished)emitter.End!).End);
            return tail.Identity;
        }
    }
    internal static IEnumerable<ulong> Targets(Transfer transfer) => transfer switch
    {
        Direct d => [d.Target], Conditional c => [c.Yes, c.No],
        TableTransfer t => t.Resolution.Cases.Select(c => c.Target).Append(t.Resolution.Default), _ => []
    };
    internal static IEnumerable<BlockIdentity> Targets(Terminator end) => end switch
    {
        Jump j => [j.Target], Branch b => [b.True, b.False], JumpTable t => t.Cases.Select(c => c.Target).Append(t.Default), _ => []
    };
    internal static IEnumerable<Term> Uses(Statement statement) => statement switch
    {
        MemoryRead r => [r.Address], MemoryWrite w => [w.Address, w.Value],
        Call c => c.Arguments.Select(a => a.Value).Concat(c.OutgoingArgumentArea is { } a ? [a] : [])
            .Concat(c.Target is ComputedTarget t ? [t.Value] : []), _ => []
    };
    internal static IEnumerable<Term> Uses(Terminator end) => end switch
    {
        Branch b => [b.Condition], JumpTable t => [t.Selector], Return r => r.Results.Select(s => s.Value), _ => []
    };
}
