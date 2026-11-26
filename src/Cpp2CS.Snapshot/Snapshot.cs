using System.Collections.Immutable;

namespace Cpp2CS.Snapshot;

/// <summary>快照里出现的种类。</summary>
public enum OccurrenceKind : byte { Read, Write, Call, StackAllocate }

/// <summary>快照里占位置的一项：内存读取、内存写入、调用、动态栈分配。纯计算不占位置，是项。</summary>
public abstract class Occurrence : IFlowOccurrence
{
    public abstract OccurrenceKind Kind { get; }
    public ImmutableArray<Term> Operands { get; }
    public ImmutableArray<int> ResultWidths { get; }
    public abstract bool DefinesMemory { get; }
    /// <summary>追溯用的原生地址，只用于诊断，不作身份，不进入摘要。</summary>
    public ulong Address { get; }

    private protected Occurrence(ImmutableArray<Term> operands, ImmutableArray<int> resultWidths, ulong address)
    {
        Operands = operands;
        ResultWidths = resultWidths;
        Address = address;
    }

    public virtual void WriteContent(DigestWriter writer) => writer.Write((int)Kind);
}

/// <summary>内存读取：从地址读 Width 位，小端。结果是一个项。</summary>
public sealed class ReadOccurrence : Occurrence
{
    public override OccurrenceKind Kind => OccurrenceKind.Read;
    public override bool DefinesMemory => false;
    public Term Location => Operands[0];
    public int Width => ResultWidths[0];

    public ReadOccurrence(Term location, int width, ulong address = 0) : base([location], [width], address) { }
}

/// <summary>内存写入：向地址写入值的全部位，小端。产生一个内存版本。</summary>
public sealed class WriteOccurrence : Occurrence
{
    public override OccurrenceKind Kind => OccurrenceKind.Write;
    public override bool DefinesMemory => true;
    public Term Location => Operands[0];
    public Term Value => Operands[1];

    public WriteOccurrence(Term location, Term value, ulong address = 0) : base([location, value], [], address) { }
}

/// <summary>
/// 调用。目标是代码地址（一个项），或目标描述定义的原语（原子操作、内存屏障、系统调用等）。
/// 实参按抽象槽位给出：前端不知道被调方的参数个数，把调用点上各实参槽当时的值都列出。
/// 结果同样按槽位列出。带展开出口的调用，展开出口上由运行时给出的值列在 Unwind 槽。
/// 每次调用产生一个内存版本。
/// </summary>
public sealed class CallOccurrence : Occurrence
{
    public override OccurrenceKind Kind => OccurrenceKind.Call;
    public override bool DefinesMemory => true;
    /// <summary>代码地址；原语调用时为空。</summary>
    public Term? Target { get; }
    /// <summary>原语的代码；普通调用时为空。</summary>
    public int? Primitive { get; }
    public ImmutableArray<Slot> ArgumentSlots { get; }
    public ImmutableArray<Slot> ResultSlots { get; }
    /// <summary>
    /// 由跳转完成：控制经一条离开本函数的跳转指令到达目标，随后的返回出口取跳转那一刻的返回地址、栈指针与保存寄存器。
    /// 把它读成“调用后返回”的前提（目标是函数入口，返回行等于入口值）由内核核对（设计 7.1）。
    /// </summary>
    public bool ByJump { get; }
    public ReadOnlySpan<Term> Arguments => Operands.AsSpan()[(Target is null ? 0 : 1)..];

    private CallOccurrence(Term? target, int? primitive, ImmutableArray<Term> operands, ImmutableArray<Slot> argumentSlots,
        ImmutableArray<Slot> resultSlots, ImmutableArray<int> resultWidths, ulong address, bool byJump) : base(operands, resultWidths, address)
    {
        Target = target;
        Primitive = primitive;
        ArgumentSlots = argumentSlots;
        ResultSlots = resultSlots;
        ByJump = byJump;
    }

    /// <summary>由跳转完成的调用，见 <see cref="ByJump"/>。</summary>
    public static CallOccurrence ByJumpTo(Term target, ReadOnlySpan<(Slot Slot, Term Value)> arguments,
        ReadOnlySpan<(Slot Slot, int Width)> results, ulong address = 0) => Create(target, null, arguments, results, address, true);

    public static CallOccurrence To(Term target, ReadOnlySpan<(Slot Slot, Term Value)> arguments,
        ReadOnlySpan<(Slot Slot, int Width)> results, ulong address = 0) => Create(target, null, arguments, results, address);

    public static CallOccurrence OfPrimitive(int primitive, ReadOnlySpan<(Slot Slot, Term Value)> arguments,
        ReadOnlySpan<(Slot Slot, int Width)> results, ulong address = 0) => Create(null, primitive, arguments, results, address);

    private static CallOccurrence Create(Term? target, int? primitive, ReadOnlySpan<(Slot Slot, Term Value)> arguments,
        ReadOnlySpan<(Slot Slot, int Width)> results, ulong address, bool byJump = false)
    {
        var operands = ImmutableArray.CreateBuilder<Term>(arguments.Length + 1);
        if (target is not null) operands.Add(target);
        var argumentSlots = ImmutableArray.CreateBuilder<Slot>(arguments.Length);
        foreach (var (slot, value) in arguments) { argumentSlots.Add(slot); operands.Add(value); }
        var resultSlots = ImmutableArray.CreateBuilder<Slot>(results.Length);
        var widths = ImmutableArray.CreateBuilder<int>(results.Length);
        foreach (var (slot, width) in results) { resultSlots.Add(slot); widths.Add(width); }
        return new(target, primitive, operands.ToImmutable(), argumentSlots.ToImmutable(), resultSlots.ToImmutable(), widths.ToImmutable(), address, byJump);
    }

    public override void WriteContent(DigestWriter writer)
    {
        base.WriteContent(writer);
        writer.Write(Target is null ? 1 : 0);
        writer.Write(Primitive ?? -1);
        writer.Write(ArgumentSlots.Length);
        foreach (var slot in ArgumentSlots) { writer.Write((int)slot.Kind); writer.Write(slot.Index); }
        writer.Write(ResultSlots.Length);
        foreach (var slot in ResultSlots) { writer.Write((int)slot.Kind); writer.Write(slot.Index); }
        // 标记只在设置时写入：没有标记的调用，摘要与引入标记之前相同。
        if (ByJump) writer.Write(-2);
    }
}

/// <summary>
/// 动态栈分配。带基址时：栈指针从 Base 改为 Base − Size，结果是新的栈指针，恒等于 Base − Size；
/// 前端只陈述这次改写，不判断方向（设计 7.1）。不带基址时：分配 Size 字节，结果是这块存储的地址，与栈指针没有关系。
/// </summary>
public sealed class StackAllocateOccurrence : Occurrence
{
    public override OccurrenceKind Kind => OccurrenceKind.StackAllocate;
    public override bool DefinesMemory => false;
    public Term Size => Operands[0];
    /// <summary>改写前的栈指针；没有给出时为空。</summary>
    public Term? Base => Operands.Length > 1 ? Operands[1] : null;

    public StackAllocateOccurrence(Term size, int pointerBits, ulong address = 0) : base([size], [pointerBits], address) { }
    public StackAllocateOccurrence(Term @base, Term size, int pointerBits, ulong address = 0) : base([size, @base], [pointerBits], address) { }
}

/// <summary>
/// 一个方法的快照：前端产出的不可变原生 IR，后面各层的唯一事实来源。任何步骤都不改写它。
/// </summary>
public sealed class MethodSnapshot : IFlowGraph
{
    /// <summary>图：块、块参数、出现、出口与边。</summary>
    public FlowGraph<Occurrence> Flow { get; }
    /// <summary>指针的位宽。地址操作数都是这个位宽。</summary>
    public int PointerBits { get; }
    /// <summary>各返回槽，与每个返回出口的实参行逐项对应。</summary>
    public ImmutableArray<Slot> ReturnSlots { get; }

    internal MethodSnapshot(FlowGraph<Occurrence> flow, int pointerBits, ImmutableArray<Slot> returnSlots)
    {
        Flow = flow;
        PointerBits = pointerBits;
        ReturnSlots = returnSlots;
    }

    public TermPool Terms => Flow.Terms;
    public ImmutableArray<FlowBlock<Occurrence>> Blocks => Flow.Blocks;
    /// <summary>入口参数，按抽象槽位区分。</summary>
    public ImmutableArray<Term> EntryParameters => Flow.EntryParameters;
    /// <summary>内容摘要：图的内容，加指针位宽与各返回槽。</summary>
    public ImmutableArray<byte> Digest => Flow.Digest;
    public string DigestText => Flow.DigestText;
    public Occurrence this[OccurrenceId occurrence] => Flow[occurrence];
    public MemoryVersion VersionAt(ProgramPoint point) => Flow.VersionAt(point);
    public MemoryVersion VersionAtExit(BlockId block) => Flow.VersionAtExit(block);

    public int Graph => Flow.Graph;
    public int BlockCount => Flow.BlockCount;
    public BlockId Entry => Flow.Entry;
    public ImmutableArray<Term> Parameters(BlockId block) => Flow.Parameters(block);
    public int OccurrenceCount(BlockId block) => Flow.OccurrenceCount(block);
    public IFlowOccurrence Occurrence(OccurrenceId occurrence) => Flow.Occurrence(occurrence);
    public ImmutableArray<Term> Operands(OccurrenceId occurrence) => Flow.Operands(occurrence);
    public ImmutableArray<Term> Results(OccurrenceId occurrence) => Flow.Results(occurrence);
    public Terminator Terminator(BlockId block) => Flow.Terminator(block);
}

/// <summary>
/// 前端构造快照的入口。用法与约定见 docs/前端.md。
/// </summary>
public sealed class SnapshotBuilder
{
    private readonly FlowBuilder<Occurrence> flow;
    private ImmutableArray<Slot> returnSlots = [];

    public int PointerBits { get; }
    public TermPool Terms => flow.Terms;

    /// <param name="pointerBits">指针位宽。</param>
    /// <param name="terms">项池；不给时新建一个。同一个方法的快照与它之上的结论共用一个池。</param>
    public SnapshotBuilder(int pointerBits, TermPool? terms = null)
    {
        if (pointerBits is not (32 or 64)) throw new ArgumentException("指针位宽须为 32 或 64");
        PointerBits = pointerBits;
        flow = new FlowBuilder<Occurrence>(terms ?? new TermPool());
    }

    public BlockId Entry => flow.Entry;

    /// <summary>声明一个入口参数，返回代表它的项。只在入口块可见。</summary>
    public Term EntryParameter(Slot slot, int width) => flow.EntryParameter(slot, width);

    /// <summary>声明各返回槽及其位宽。</summary>
    public void SetReturnSlots(params ReadOnlySpan<(Slot Slot, int Width)> slots)
    {
        var kinds = ImmutableArray.CreateBuilder<Slot>(slots.Length);
        Span<int> widths = stackalloc int[slots.Length];
        for (int i = 0; i < slots.Length; i++) { kinds.Add(slots[i].Slot); widths[i] = slots[i].Width; }
        returnSlots = kinds.MoveToImmutable();
        flow.SetReturnWidths(widths);
    }

    /// <summary>声明一个块，给出各参数的位宽。</summary>
    public BlockId Block(params ReadOnlySpan<int> parameterWidths) => flow.Block(parameterWidths);
    public Term Parameter(BlockId block, int index) => flow.Parameter(block, index);
    public ImmutableArray<Term> Parameters(BlockId block) => flow.Parameters(block);

    /// <summary>内存读取，返回读到的值。</summary>
    public Term Read(BlockId block, Term location, int width, ulong address = 0) =>
        flow.Append(block, new ReadOccurrence(location, width, address))[0];

    /// <summary>内存写入。</summary>
    public void Write(BlockId block, Term location, Term value, ulong address = 0) =>
        flow.Append(block, new WriteOccurrence(location, value, address));

    /// <summary>对代码地址的调用，返回各结果槽的值。</summary>
    public ImmutableArray<Term> Call(BlockId block, Term target, ReadOnlySpan<(Slot Slot, Term Value)> arguments,
        ReadOnlySpan<(Slot Slot, int Width)> results, ulong address = 0) =>
        flow.Append(block, CallOccurrence.To(target, arguments, results, address));

    /// <summary>原语调用，返回各结果槽的值。</summary>
    public ImmutableArray<Term> CallPrimitive(BlockId block, int primitive, ReadOnlySpan<(Slot Slot, Term Value)> arguments,
        ReadOnlySpan<(Slot Slot, int Width)> results, ulong address = 0) =>
        flow.Append(block, CallOccurrence.OfPrimitive(primitive, arguments, results, address));

    /// <summary>
    /// 由跳转完成的调用（docs/前端.md 第 4 节“离开本函数的跳转”）：返回各结果槽的值；随后块须以单独的返回出口结束。
    /// </summary>
    public ImmutableArray<Term> TailCall(BlockId block, Term target, ReadOnlySpan<(Slot Slot, Term Value)> arguments,
        ReadOnlySpan<(Slot Slot, int Width)> results, ulong address = 0) =>
        flow.Append(block, CallOccurrence.ByJumpTo(target, arguments, results, address));

    /// <summary>动态栈分配，返回存储的地址。</summary>
    public Term StackAllocate(BlockId block, Term size, ulong address = 0) =>
        flow.Append(block, new StackAllocateOccurrence(size, PointerBits, address))[0];

    /// <summary>带基址的动态栈分配：栈指针从 base 改为 base − size，返回新的栈指针。</summary>
    public Term StackAllocate(BlockId block, Term @base, Term size, ulong address = 0) =>
        flow.Append(block, new StackAllocateOccurrence(@base, size, PointerBits, address))[0];

    public void Terminate(BlockId block, Terminator terminator) => flow.Terminate(block, terminator);
    public void Jump(BlockId block, BlockId target, params ReadOnlySpan<Term> arguments) =>
        flow.Terminate(block, Terminator.Single(Exit.To(target, arguments)));
    public void Return(BlockId block, params ReadOnlySpan<Term> values) =>
        flow.Terminate(block, Terminator.Single(Exit.Return(values)));

    /// <summary>校验契约并构造快照。不满足契约时抛出 <see cref="FlowException"/>，列出全部违反之处。</summary>
    public MethodSnapshot Build()
    {
        int pointerBits = PointerBits;
        var slots = returnSlots;
        var graph = flow.Build(draft => Check(draft, pointerBits, slots), writer =>
        {
            // 返回槽的身份与指针位宽属于方法的契约，写入摘要。
            writer.Write(pointerBits);
            writer.Write(slots.Length);
            foreach (var slot in slots) { writer.Write((int)slot.Kind); writer.Write(slot.Index); }
        });
        return new MethodSnapshot(graph, pointerBits, slots);
    }

    /// <summary>快照特有的契约，见 docs/前端.md 第 4、5 节。</summary>
    private static void Check(FlowDraft<Occurrence> draft, int pointerBits, ImmutableArray<Slot> returnSlots)
    {
        // 槽位：Managed 只用于模板一侧；Unwind 只是带展开出口的调用的结果。
        foreach (var parameter in draft.EntryParameters)
            if (parameter.Slot.Kind is SlotKind.Managed or SlotKind.Unwind)
                draft.Report($"入口参数不能用 {parameter.Slot.Kind} 槽位：{parameter.Slot}");
        Slots(draft, "返回行", returnSlots, allowUnwind: false);

        bool returns = false;
        for (int b = 0; b < draft.BlockCount; b++)
        {
            var block = new BlockId(b);
            var occurrences = draft.Occurrences(block);
            var terminator = draft.Terminator(block);
            bool invoke = terminator is { Kind: TerminatorKind.Invoke };
            for (int i = 0; i < occurrences.Length; i++)
            {
                var occurrence = occurrences[i];
                string where = $"B{b} 的出现 {i}";
                // 地址是指针位宽。
                Term? location = occurrence switch
                {
                    ReadOccurrence read => read.Location,
                    WriteOccurrence write => write.Location,
                    CallOccurrence { Target: { } target } => target,
                    _ => null,
                };
                if (location is not null && location.Width != pointerBits)
                    draft.Report($"{where}：地址是 {location.Width} 位，指针是 {pointerBits} 位");
                if (occurrence is StackAllocateOccurrence { Base: { } stackBase } && stackBase.Width != pointerBits)
                    draft.Report($"{where}：栈基址是 {stackBase.Width} 位，指针是 {pointerBits} 位");
                if (occurrence is not CallOccurrence call) continue;
                // 由跳转完成的调用是块的最后一个出现，块以单独的返回出口结束。
                if (call.ByJump && (i != occurrences.Length - 1
                    || terminator is not { Kind: TerminatorKind.Single } || terminator.Exits[0].Kind != ExitKind.Return))
                    draft.Report($"{where}：由跳转完成的调用须是块的最后一个出现，块以单独的返回出口结束");
                if (call.Target is null == call.Primitive is null)
                    draft.Report($"{where}：调用须恰好给出代码地址与原语之一");
                Slots(draft, $"{where} 的实参", call.ArgumentSlots, allowUnwind: false);
                Slots(draft, $"{where} 的结果", call.ResultSlots, allowUnwind: invoke && i == occurrences.Length - 1);
                // 对代码地址的调用列出栈指针：经栈传递的实参是相对它的读取。
                if (call.Target is not null && !call.ArgumentSlots.Any(s => s.Kind == SlotKind.StackPointer))
                    draft.Report($"{where}：调用没有列出栈指针");
            }

            if (terminator is null) continue;
            bool afterCall = terminator.Kind == TerminatorKind.Invoke
                || (terminator.Kind == TerminatorKind.Single && terminator.Exits[0].Kind == ExitKind.NoReturn);
            if (afterCall && (occurrences.Length == 0 || occurrences[^1] is not CallOccurrence))
                draft.Report($"B{b}：带展开出口的调用与不返回的出口之前须是一次调用");
            returns |= terminator.Exits.Any(e => e.Kind == ExitKind.Return);

            // 带展开出口的调用：正常返回的结果只在正常出口上存在，Unwind 槽的结果只在展开出口上存在。
            if (invoke && terminator.Exits.Length == 2 && occurrences.Length > 0 && occurrences[^1] is CallOccurrence last)
            {
                var results = draft.Results(new OccurrenceId(block, occurrences.Length - 1));
                var normal = new HashSet<Term>(ReferenceEqualityComparer.Instance);
                var unwind = new HashSet<Term>(ReferenceEqualityComparer.Instance);
                for (int k = 0; k < results.Length; k++) (last.ResultSlots[k].Kind == SlotKind.Unwind ? unwind : normal).Add(results[k]);
                if (Mentions(terminator.Exits[0].Arguments, unwind) is { } early)
                    draft.Report($"B{b} 的正常出口使用了展开时才有的结果 {early}");
                if (Mentions(terminator.Exits[1].Arguments, normal) is { } late)
                    draft.Report($"B{b} 的展开出口使用了正常返回才有的结果 {late}");
            }
        }

        // 返回行列出实际返回到的地址与栈指针。
        if (returns)
            foreach (var kind in (ReadOnlySpan<SlotKind>)[SlotKind.ReturnAddress, SlotKind.StackPointer])
                if (!returnSlots.Any(s => s.Kind == kind)) draft.Report($"返回行没有列出 {kind} 槽");

        // 快照里没有实体与运行时属性：它们由事实层引入。
        var seen = new HashSet<Term>(ReferenceEqualityComparer.Instance);
        for (int b = 0; b < draft.BlockCount; b++)
        {
            var block = new BlockId(b);
            var terms = new List<Term>();
            for (int i = 0; i < draft.Occurrences(block).Length; i++) terms.AddRange(draft.Operands(new OccurrenceId(block, i)));
            if (draft.Terminator(block) is { } terminator)
            {
                if (terminator.Condition is not null) terms.Add(terminator.Condition);
                foreach (var exit in terminator.Exits) terms.AddRange(exit.Arguments);
            }
            foreach (var term in terms)
                if (Named(term, seen) is { } named)
                    draft.Report(named.Kind == TermKind.Arbitrary ? $"B{b} 使用了任意值 {named}；任意值由内核引入，前端不构造"
                        : $"B{b} 使用了实体或运行时属性 {named}；快照里不含事实层的项");
        }
    }

    /// <summary>一组槽位：不重复，不用 Managed；allowUnwind 为假时不用 Unwind。</summary>
    private static void Slots(FlowDraft<Occurrence> draft, string where, ImmutableArray<Slot> slots, bool allowUnwind)
    {
        var distinct = new HashSet<Slot>();
        foreach (var slot in slots)
        {
            if (!distinct.Add(slot)) draft.Report($"{where}：槽位 {slot} 重复");
            if (slot.Kind == SlotKind.Managed) draft.Report($"{where}：Managed 槽位只用于模板一侧：{slot}");
            if (slot.Kind == SlotKind.Unwind && !allowUnwind) draft.Report($"{where}：Unwind 槽位只出现在带展开出口的调用的结果里：{slot}");
        }
    }

    /// <summary>一行实参里是否用到某组项，返回用到的第一个。</summary>
    private static Term? Mentions(ImmutableArray<Term> row, HashSet<Term> targets)
    {
        if (targets.Count == 0) return null;
        var seen = new HashSet<Term>(ReferenceEqualityComparer.Instance);
        Term? Find(Term term)
        {
            if (!seen.Add(term)) return null;
            if (targets.Contains(term)) return term;
            foreach (var operand in term.Operands)
                if (Find(operand) is { } found) return found;
            return null;
        }
        foreach (var term in row)
            if (Find(term) is { } found) return found;
        return null;
    }

    /// <summary>项里的第一个实体或运行时属性。</summary>
    private static Term? Named(Term term, HashSet<Term> seen)
    {
        if (!seen.Add(term)) return null;
        if (term.Kind is TermKind.Entity or TermKind.Attribute or TermKind.Arbitrary) return term;
        foreach (var operand in term.Operands)
            if (Named(operand, seen) is { } found) return found;
        return null;
    }
}
