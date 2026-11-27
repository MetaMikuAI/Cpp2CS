using System.Collections.Immutable;
using Cpp2CS.Kernel.Engine;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Kernel.Sources;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;
using Cpp2CS.Spec.Runtime;

namespace Cpp2CS.Kernel.Facts;

/// <summary>出现在托管语义下的效果的种类（设计 7.5）。None 是不可观察的效果：帧对象、映像数据区、登记为不可观察或纯函数的运行时操作。</summary>
public enum NativeEffectKind : byte { None, Read, Write, Call, ClassInitialize, NewObject, Throw, Unnamed }

/// <summary>
/// 一个出现的效果。项都是取定之后的写法（见 <see cref="EffectGraph.Resolve"/>）。
/// 读：Address、Width，Value 是读取的结果；写：Address、Value；新对象：Class，Value 是新引用；调用：Target、Callee，Arguments 按被调方法的签名、按栈上的位宽，
/// Result 是按返回类型取出的栈上的值；类初始化：Class；抛出：运行时构造的异常给出 Exception，托管代码给出的异常对象在 Value 里；未命名：Detail 是原因。
/// </summary>
public sealed record NativeEffect(OccurrenceId Occurrence, NativeEffectKind Kind)
{
    public Term? Address { get; init; }
    public int Width { get; init; }
    public Term? Value { get; init; }
    public ulong Target { get; init; }
    public MethodShape? Callee { get; init; }
    public ImmutableArray<Term> Arguments { get; init; } = [];
    public Term? Result { get; init; }
    public Term? Class { get; init; }
    public ExceptionKind Exception { get; init; }
    /// <summary>路径在这个效果处结束：这次调用不返回（设计 7.5）。依据是规格的登记、被调方法的效果摘要，或这次调用是函数范围里的最后一条指令。</summary>
    public bool Ends { get; init; }
    public string Detail { get; init; } = "";
}

/// <summary>条件抛出（设计 7.5）：分支的一条边通往只抛出尾。Condition 取 Polarity 时走这条边。</summary>
public sealed record ConditionalThrow(EdgeId Edge, Term Condition, bool Polarity, ExceptionKind Exception);

/// <summary>
/// 效果图（设计 7.5）：快照加上每个出现的效果，以及值的事实——每个块参数、每个出现的结果取定成什么。
/// 取定只用关于快照的真命题：各条入边传入同一个值的块参数就是那个值；帧上常量偏移处的读取是此前存在那里的值
/// （各条路径存的是同一个值时）；类型的元数据槽上的读取是该类型的实体；装入后只读的指针字是链接期常量；
/// 登记为纯函数的运行时操作的结果是具名函数作用在实参上。其余的值保持为原子。
/// 这是内核的只读查询面：发现器、选择、下降都从这里读，这里不提供入边与来源关系的遍历。
/// </summary>
public sealed class EffectGraph
{
    public MethodSnapshot Snapshot { get; }
    public MethodShape Host { get; }
    public FlowShape Shape { get; }
    /// <summary>事实层整体不能回答时的原因（调用约定没有登记等）；此时没有效果。</summary>
    public string? Failure { get; }
    /// <summary>方法里有环（回边）。</summary>
    public bool Cyclic { get; private set; }

    private readonly TermPool terms;
    /// <summary>取定视图（设计 7.2）：读图的每一行时，未定义的占位已经换成按位置区分的任意值。</summary>
    private readonly PlacedGraph placed;
    private readonly Dictionary<Term, Term> resolved = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<Term, Term> memo = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<OccurrenceId, NativeEffect> effects = [];
    private readonly bool[] reachable;
    private readonly bool[] ends;                 // 块在一次抛出处结束
    private readonly ExceptionKind[] thrown;      // 块结束处抛出的异常
    private readonly Term?[] conditions;
    private readonly Term?[] returns, returnSlots;
    private readonly List<ConditionalThrow> checks = [];
    private readonly List<(Term Value, TypeShape Type, int Index)> arguments = [];
    private readonly List<Term> stored = [];
    private readonly List<int> order = [];
    private readonly HashSet<EdgeId> live = [];
    private readonly Dictionary<Term, Term> runtimeReads = new(ReferenceEqualityComparer.Instance);

    /// <summary>各形参在栈上的值（原生一侧的项）与类型。</summary>
    public IReadOnlyList<(Term Value, TypeShape Type, int Index)> Arguments => arguments;
    /// <summary>各形参按存储位宽取出的值：入口槽位的低位；C++ 的 bool 只取 0 与 1（设计 7.7）。</summary>
    public IReadOnlyList<Term> Stored => stored;
    /// <summary>一条边上传给目标块第 index 个参数的值，取定之后的写法。</summary>
    public Term EdgeArgument(EdgeId edge, int index) => Resolve(placed.Terminator(edge.Source).Exits[edge.Exit].Arguments[index]);
    /// <summary>可达的块，按逆后序。</summary>
    public IReadOnlyList<int> Order => order;
    public IReadOnlyList<ConditionalThrow> Checks => checks;
    public IEnumerable<NativeEffect> Effects => order.SelectMany(b => Enumerable.Range(0, Snapshot.OccurrenceCount(new(b))))
        .Zip(order.SelectMany(b => Enumerable.Repeat(b, Snapshot.OccurrenceCount(new(b)))), (i, b) => new OccurrenceId(new(b), i))
        .Where(effects.ContainsKey).Select(id => effects[id]);

    public bool Reachable(BlockId block) => reachable[block.Index];
    /// <summary>这条边在某次执行里会被走到（源块可达，且没有在此之前以抛出结束）。</summary>
    public bool Live(EdgeId edge) => live.Contains(edge);
    public NativeEffect? Effect(OccurrenceId occurrence) => effects.GetValueOrDefault(occurrence);
    /// <summary>块末分支的条件（或跳转表的选择子），取定之后的写法。</summary>
    public Term? Condition(BlockId block) => conditions[block.Index];
    /// <summary>块以返回结束时，返回值按返回类型的存储位宽取出的项；没有返回值或不是返回时为空。</summary>
    public Term? Returned(BlockId block) => returns[block.Index];
    /// <summary>块以返回结束时，返回值所在槽位的整个值。</summary>
    public Term? ReturnSlot(BlockId block) => returnSlots[block.Index];
    /// <summary>块在一次不返回的调用处结束：其后的出现与出口不属于任何执行（设计 7.5）。</summary>
    public bool EndsInThrow(BlockId block) => ends[block.Index];

    /// <summary>
    /// 这个值是运行时状态上一次读取的结果时，是那次读取的地址（设计 7.4）：映像可写数据区里既不是元数据槽、也不是链接期常量的字
    /// （运行时私有状态，例如方法的元数据初始化标志），或类结构上的字（类的初始化完成标志、静态区指针）。
    /// 这些读取不是托管位置上的读取，没有效果；条件只依赖这种值的分支不可表达（设计 9.5）。
    /// </summary>
    public Term? RuntimeStateAddress(Term value) => runtimeReads.GetValueOrDefault(value);

    /// <summary>地址落在类结构里（设计 7.4）：类指针（类型实体）本身，或它加常量偏移。类结构是运行时的数据，不是托管位置。</summary>
    internal static bool OnClassStructure(Term address) =>
        address is { Kind: TermKind.Entity } named ? named.Entity.Kind == EntityKind.Type
        : address is { Kind: TermKind.Operation, Op: Op.Add } sum && sum.Operands[1].IsConstant
            && sum.Operands[0] is { Kind: TermKind.Entity } root && root.Entity.Kind == EntityKind.Type;

    /// <summary>块是只抛出尾（设计 7.5）时，是它抛出的异常的种类：到抛出为止没有可观察的效果。</summary>
    public ExceptionKind Tail(BlockId block)
    {
        for (int hops = 0; hops < Snapshot.BlockCount; hops++)
        {
            if (!reachable[block.Index]) return ExceptionKind.None;
            for (int i = 0; i < Snapshot.OccurrenceCount(block); i++)
                if (effects.TryGetValue(new(block, i), out var effect) && effect.Kind != NativeEffectKind.Throw) return ExceptionKind.None;
            if (ends[block.Index]) return thrown[block.Index];
            var terminator = Snapshot.Terminator(block);
            if (terminator.Kind != TerminatorKind.Single || terminator.Exits[0].Kind != ExitKind.Target) return ExceptionKind.None;
            block = terminator.Exits[0].Target;
        }
        return ExceptionKind.None;
    }

    /// <summary>把项里的块参数与出现的结果换成它们取定的值。</summary>
    public Term Resolve(Term term)
    {
        if (term.Operands.Length == 0 && !resolved.ContainsKey(term)) return term;
        if (memo.TryGetValue(term, out var done)) return done;
        Term result;
        if (resolved.TryGetValue(term, out var known)) result = known;
        else
        {
            var parts = new Term[term.Operands.Length];
            bool changed = false;
            for (int i = 0; i < parts.Length; i++)
            {
                parts[i] = Resolve(term.Operands[i]);
                changed |= !ReferenceEquals(parts[i], term.Operands[i]);
            }
            result = changed ? terms.Rebuild(term, parts) : term;
        }
        memo[term] = result;
        return result;
    }

    /// <summary>snapshots 按入口给出别的方法的快照，用来取调用的效果摘要（设计 5.4）；没有时为空，摘要一律未知。</summary>
    public EffectGraph(MethodSnapshot snapshot, MethodShape host, INativeFacts facts, Func<ulong, MethodSnapshot?>? snapshots = null)
    {
        Snapshot = snapshot;
        Host = host;
        Shape = new FlowShape(snapshot);
        terms = snapshot.Terms;
        placed = new PlacedGraph(snapshot);
        int count = snapshot.BlockCount;
        reachable = new bool[count];
        ends = new bool[count];
        thrown = new ExceptionKind[count];
        conditions = new Term?[count];
        returns = new Term?[count];
        returnSlots = new Term?[count];

        var convention = EngineFacts.Convention(host, out var returned, out string reason);
        Term? pointer = snapshot.EntryParameters.FirstOrDefault(p => p.Slot == new Slot(SlotKind.StackPointer, 0));
        if (convention is null || pointer is null) { Failure = convention is null ? reason : "快照的入口没有声明栈指针"; return; }
        Term? Entry(Slot slot) => snapshot.EntryParameters.FirstOrDefault(p => p.Slot == slot);
        if (facts.GenericEntry(host.Entity) is { } generic &&
            Entry(NativeEntryQueries.MethodArgumentSlot(convention.Value)) is { } hidden && hidden.Width == snapshot.PointerBits &&
            ParameterSummary.ReadsHidden(snapshot, hidden.Slot))
            resolved[hidden] = terms.Entity(generic.ExpectedMethod, snapshot.PointerBits);
        for (int i = 0; i < convention.Value.Length; i++)
        {
            if (EngineFacts.Gather(terms, convention.Value[i], Entry) is not { } entry) { Failure = $"快照的入口没有声明第 {i} 个形参的槽位"; return; }
            arguments.Add((OnStack(entry, host.Parameters[i]), ClaimTemplate.OnStack(host.Parameters[i]), i));
            stored.Add(host.Parameters[i].TwoValued ? terms.ZeroExtend(terms.Slice(entry, 0, 1), entry.Width) : entry);
        }

        // 逆后序（按快照里写出的出口）。在抛出处结束的块没有后继，它写出的出口不计入可达。
        var postorder = new List<int>();
        var visited = new bool[count];
        var stack = new Stack<(int Block, int Next)>();
        stack.Push((snapshot.Entry.Index, 0));
        visited[snapshot.Entry.Index] = true;
        while (stack.Count > 0)
        {
            var (block, next) = stack.Pop();
            var exits = snapshot.Terminator(new(block)).Exits;
            if (next < exits.Length)
            {
                stack.Push((block, next + 1));
                if (exits[next].Kind == ExitKind.Target && !visited[exits[next].Target.Index])
                {
                    visited[exits[next].Target.Index] = true;
                    stack.Push((exits[next].Target.Index, 0));
                }
            }
            else postorder.Add(block);
        }
        postorder.Reverse();
        var position = new int[count];
        for (int i = 0; i < postorder.Count; i++) position[postorder[i]] = i;

        var incoming = new List<(EdgeId Edge, ImmutableArray<Term> Row)>[count];
        var frameOut = new Dictionary<long, Term>?[count];
        reachable[snapshot.Entry.Index] = true;
        foreach (int index in postorder)
        {
            if (!reachable[index]) continue;
            order.Add(index);
            var block = new BlockId(index);
            // 块参数：各条入边传入同一个值时就是那个值。有回边进入的块，参数保留为原子（这一次经过的值）。
            var edges = incoming[index] ?? [];
            bool head = Shape.IsLoopHead(block);
            Cyclic |= head;
            var parameters = snapshot.Parameters(block);
            if (!head && edges.Count > 0)
                for (int k = 0; k < parameters.Length; k++)
                {
                    var first = edges[0].Row[k];
                    if (edges.TrueForAll(e => ReferenceEquals(e.Row[k], first))) resolved[parameters[k]] = first;
                    // 各条入边只在低位传入同一个值（被调方只保存低半的寄存器：高半各不相关）：参数的低位就是那个值，高位仍是它自己的高位。
                    else if (first is { Kind: TermKind.Concat } pieces && pieces.Operands[0] is var low
                        && edges.TrueForAll(e => e.Row[k] is { Kind: TermKind.Concat } other && ReferenceEquals(other.Operands[0], low)))
                        resolved[parameters[k]] = terms.Concat(low, terms.Slice(parameters[k], low.Width, first.Width - low.Width));
                }
            // 帧：各条入边上内容相同的偏移保留。
            Dictionary<long, Term> frame = [];
            if (!head && edges.Count > 0)
            {
                var first = frameOut[edges[0].Edge.Source.Index]!;
                foreach (var (offset, value) in first)
                    if (edges.TrueForAll(e => frameOut[e.Edge.Source.Index]!.TryGetValue(offset, out var other) && ReferenceEquals(other, value)))
                        frame[offset] = value;
            }

            int ended = -1;
            for (int i = 0; i < snapshot.OccurrenceCount(block) && !ends[index]; i++)
            {
                var id = new OccurrenceId(block, i);
                var operands = placed.Operands(id).Select(Resolve).ToImmutableArray();
                var results = snapshot.Results(id);
                NativeEffect Unnamed(string detail) => new(id, NativeEffectKind.Unnamed) { Detail = detail };
                NativeEffect? effect = null;
                switch (snapshot[id])
                {
                    case ReadOccurrence read:
                    {
                        var address = operands[0];
                        if (StructureReads.Name(address, read.Width, facts, terms) is { } named)
                            resolved[results[0]] = named;
                        else if (EngineFacts.FrameOffset(address, pointer) is long offset)
                        {
                            if (frame.TryGetValue(offset, out var stored) && stored.Width >= read.Width) resolved[results[0]] = terms.Slice(stored, 0, read.Width);
                        }
                        else if (address.IsConstant && facts.InImageData((ulong)address.Value))
                        {
                            if (read.Width == facts.Layout.PointerBits && facts.EntityAtSlot((ulong)address.Value) is { } type)
                                resolved[results[0]] = terms.Entity(type, read.Width);
                            else if (read.Width == facts.Layout.PointerBits && facts.LinkConstant((ulong)address.Value) is { } constant)
                                resolved[results[0]] = terms.Bits(constant, read.Width);
                            else runtimeReads[results[0]] = address;
                        }
                        else if (OnClassStructure(address)) runtimeReads[results[0]] = address;
                        else if (EngineFacts.MentionsStack(address, pointer)) effect = Unnamed($"地址由栈指针算出，但不是常量偏移：{address}");
                        else effect = new(id, NativeEffectKind.Read) { Address = address, Width = read.Width, Value = results[0] };
                        break;
                    }
                    case WriteOccurrence:
                    {
                        var (address, value) = (operands[0], operands[1]);
                        if (EngineFacts.FrameOffset(address, pointer) is long offset)
                        {
                            foreach (long at in frame.Keys.ToArray())
                                if (at != offset && at < offset + value.Width / 8 && offset < at + frame[at].Width / 8) frame.Remove(at);
                            frame[offset] = value;
                        }
                        else if (address.IsConstant && facts.InImageData((ulong)address.Value)) { }
                        else if (EngineFacts.MentionsStack(address, pointer)) effect = Unnamed($"地址由栈指针算出，但不是常量偏移：{address}");
                        else if (EngineFacts.MentionsStack(value, pointer)) effect = Unnamed("帧地址被写入堆：帧对象逃逸");
                        else effect = new(id, NativeEffectKind.Write) { Address = address, Width = value.Width, Value = value };
                        break;
                    }
                    case CallOccurrence call:
                        effect = Call(id, call, operands, results, facts, pointer, snapshots, Unnamed);
                        // 不返回的另外两种依据（设计 7.5）：这次调用是函数范围里的最后一条指令；被调托管方法的效果摘要。
                        if (ReturnSummary.LastInFunction(snapshot, id))
                        {
                            // 托管调用与未命名的调用在此结束路径。登记为会返回的运行时操作排在函数范围的末尾，是登记与代码不符：当作未命名的效果。
                            if (effect is { Kind: NativeEffectKind.Call or NativeEffectKind.Unnamed, Ends: false }) effect = effect with { Ends = true };
                            else if (effect is not { Ends: true }) effect = Unnamed("登记为会返回的运行时操作排在函数范围的末尾") with { Ends = true };
                        }
                        else if (effect is { Kind: NativeEffectKind.Call, Ends: false } && snapshots is not null
                            && ReturnSummary.EndsBlock(snapshot, id) && ReturnSummary.NeverReturns(snapshots(effect.Target)))
                            effect = effect with { Ends = true };
                        break;
                    default:
                        effect = Unnamed("动态栈分配的定位尚未实现");
                        break;
                }
                if (effect is null) continue;
                effects[id] = effect;
                if (effect.Ends)
                {
                    ended = i;
                    ends[index] = true;
                    thrown[index] = effect.Kind == NativeEffectKind.Throw ? effect.Exception : ExceptionKind.None;
                }
            }
            frameOut[index] = frame;
            var terminator = placed.Terminator(block);
            // 块在不返回的调用处结束：其后的出口不属于任何执行。这次调用自己带展开出口时，它抛出的异常仍沿展开出口离开。
            bool unwinds = ends[index] && terminator.Kind == TerminatorKind.Invoke && ended == snapshot.OccurrenceCount(block) - 1;
            if (ends[index] && !unwinds) continue;

            if (terminator.Condition is { } condition) conditions[index] = Resolve(condition);
            for (int e = unwinds ? 1 : 0; e < terminator.Exits.Length; e++)
            {
                var exit = terminator.Exits[e];
                if (exit.Kind == ExitKind.Return && returned is { } passing)
                {
                    Term? Slot(Slot slot) => snapshot.ReturnSlots.IndexOf(slot) is var at && at >= 0 ? Resolve(exit.Arguments[at]) : null;
                    returns[index] = EngineFacts.Gather(terms, passing, Slot);
                    if (passing.Pieces.Length == 1) returnSlots[index] = Slot(passing.Pieces[0].Slot);
                }
                if (exit.Kind != ExitKind.Target) continue;
                live.Add(new(block, e));
                int target = exit.Target.Index;
                reachable[target] = true;
                if (position[target] > position[index])
                    (incoming[target] ??= []).Add((new(block, e), exit.Arguments.Select(Resolve).ToImmutableArray()));
            }
        }

        foreach (int index in order)
        {
            var block = new BlockId(index);
            var terminator = snapshot.Terminator(block);
            if (ends[index] || terminator.Kind != TerminatorKind.Branch) continue;
            for (int e = 0; e < 2; e++)
                if (terminator.Exits[e].Kind == ExitKind.Target && Tail(terminator.Exits[e].Target) is var kind && kind != ExceptionKind.None)
                    checks.Add(new(new(block, e), conditions[index]!, e == 0, kind));
        }
    }

    /// <summary>存储位宽的值在栈上的写法（ECMA-335 III.1.1）：不超过 32 位的整数按类型的符号扩到 32 位。</summary>
    private Term OnStack(Term stored, TypeShape type)
    {
        if (type.Kind != StackKind.Int32 || stored.Width >= 32) return stored;
        if (type.TwoValued) return terms.ZeroExtend(terms.Slice(stored, 0, 1), 32);
        return type.Signed ? terms.SignExtend(stored, 32) : terms.ZeroExtend(stored, 32);
    }

    private NativeEffect? Call(OccurrenceId id, CallOccurrence call, ImmutableArray<Term> operands, ImmutableArray<Term> results, INativeFacts facts,
        Term pointer, Func<ulong, MethodSnapshot?>? snapshots, Func<string, NativeEffect> unnamed)
    {
        if (call.Target is null) return unnamed($"原语调用 {call.Primitive} 没有登记");
        if (!operands[0].IsConstant) return unnamed($"调用的目标没有命名：{operands[0]}");
        ulong address = (ulong)operands[0].Value;
        var callee = facts.Callee(address);
        if (callee.Kind == CalleeKind.Unknown) return unnamed($"未命名的调用：{callee.Name}");
        if (call.ByJump)
        {
            // 由跳转完成的调用读成“调用后返回”的前提（设计 7.1）：返回行里的返回地址、栈指针、各保存寄存器等于入口值。
            var row = placed.Terminator(id.Block).Exits[0].Arguments;
            for (int k = 0; k < Snapshot.ReturnSlots.Length; k++)
            {
                var slot = Snapshot.ReturnSlots[k];
                if (slot.Kind is not (SlotKind.ReturnAddress or SlotKind.StackPointer or SlotKind.Preserved)) continue;
                if (!ReferenceEquals(Resolve(row[k]), Snapshot.EntryParameters.FirstOrDefault(p => p.Slot == slot)))
                    return unnamed($"由跳转完成的调用：返回行的 {slot} 不是入口处的值");
            }
        }
        Term? Argument(Slot slot)
        {
            int at = call.ArgumentSlots.IndexOf(slot);
            return at < 0 ? null : operands[at + 1];
        }
        int pointerBits = facts.Layout.PointerBits;
        Term? Returned(Slot slot)
        {
            int at = call.ResultSlots.IndexOf(slot);
            return at < 0 ? null : results[at];
        }
        if (callee.Kind == CalleeKind.Managed)
        {
            if (callee.MethodAtCall(address, snapshots, Argument, out string reason) is not { } shape) return unnamed(reason);
            if (EngineFacts.Convention(shape, out var returned, out reason) is not { } slots) return unnamed(reason);
            var arguments = ImmutableArray.CreateBuilder<Term>(slots.Length);
            for (int i = 0; i < slots.Length; i++)
            {
                // 实参按栈上的位宽取：不超过 32 位的整数取所在槽位的低 32 位（被调方法只用其中的低位）。
                var type = ClaimTemplate.OnStack(shape.Parameters[i]);
                var passing = slots[i];
                if (passing.Pieces is [var piece] && piece.Bits != ClaimTemplate.StackBits(type))
                    passing = passing with { Pieces = [(piece.Slot, ClaimTemplate.StackBits(type))] };
                if (EngineFacts.Gather(terms, passing, Argument) is not { } given) return unnamed($"调用没有给出第 {i} 个实参的槽位");
                if (EngineFacts.MentionsStack(given, pointer)) return unnamed("帧地址作为实参：帧对象逃逸");
                arguments.Add(given);
            }
            Term? result = null;
            if (returned is { } slot)
            {
                if (EngineFacts.Gather(terms, slot, Returned) is not { } produced) return unnamed("调用的结果里没有返回值的槽位");
                result = OnStack(produced, shape.Return!);
            }
            return new(id, NativeEffectKind.Call) { Target = address, Callee = shape, Arguments = arguments.MoveToImmutable(), Result = result };
        }
        var operation = callee.Operation!;
        switch (operation.Effect)
        {
            case RuntimeEffect.Throw:
                return new(id, NativeEffectKind.Throw) { Exception = operation.Exception, Ends = true };
            case RuntimeEffect.ClassInitialize:
                return Argument(new Slot(SlotKind.Integer, 0)) is { } initialized
                    ? new(id, NativeEffectKind.ClassInitialize) { Class = initialized } : unnamed("类初始化没有给出实参");
            case RuntimeEffect.NewObject:
                return Argument(new Slot(SlotKind.Integer, 0)) is { } allocated && Returned(new Slot(SlotKind.Integer, 0)) is { } created
                    ? new(id, NativeEffectKind.NewObject) { Class = allocated, Value = created } : unnamed("新对象的调用没有给出类或结果的槽位");
            case RuntimeEffect.Unobservable:
                // 结果登记为“实参所指的元数据槽的内容”：类型的槽给出该类型的实体。
                if (operation.ReturnsSlot && Argument(new Slot(SlotKind.Integer, 0)) is { IsConstant: true } slot
                    && facts.EntityAtSlot((ulong)slot.Value) is { } type && Returned(new Slot(SlotKind.Integer, 0)) is { } content && content.Width == pointerBits)
                    resolved[content] = terms.Entity(type, pointerBits);
                if (operation.ReturnsArgument && Argument(new Slot(SlotKind.Integer, 0)) is { } argument &&
                    Returned(new Slot(SlotKind.Integer, 0)) is { } result && result.Width == argument.Width)
                    resolved[result] = argument;
                return null;
            case RuntimeEffect.Pure:
            {
                var arguments = new Term[operation.Arguments];
                for (int k = 0; k < arguments.Length; k++)
                {
                    if (Argument(new Slot(SlotKind.Integer, k)) is not { } given) return unnamed($"调用没有给出实参槽 Integer{k}");
                    arguments[k] = given;
                }
                if (Returned(new Slot(SlotKind.Integer, 0)) is { } value && value.Width == pointerBits)
                    resolved[value] = terms.Attribute(new AttributeId((int)operation.Function), pointerBits, arguments);
                return null;
            }
            case RuntimeEffect.MakeException:
                if (Returned(new Slot(SlotKind.Integer, 0)) is { } made && made.Width == pointerBits)
                    resolved[made] = terms.Attribute(new AttributeId(KernelAttributes.ExceptionObject), pointerBits,
                        terms.Constant((int)operation.Exception, 32), terms.Constant(id.Block.Index * 4096 + id.Index, 32));
                return null;
            case RuntimeEffect.ThrowArgument:
                if (Argument(new Slot(SlotKind.Integer, 0)) is { Kind: TermKind.Attribute } thrownObject
                    && thrownObject.Attribute.Value == KernelAttributes.ExceptionObject)
                    return new(id, NativeEffectKind.Throw) { Exception = (ExceptionKind)(int)thrownObject.Operands[0].Value, Ends = true };
                // 抛出一个托管代码给出的异常对象：Value 是这个对象。路径在此结束。
                return Argument(new Slot(SlotKind.Integer, 0)) is { } thrown
                    ? new(id, NativeEffectKind.Throw) { Value = thrown, Ends = true } : unnamed("抛出没有给出异常对象的槽位") with { Ends = true };
            default:
                return unnamed($"运行时操作 {operation.Id} 的效果种类没有处理");
        }
    }
}

/// <summary>发现器看到的只读查询面（设计 9.6）：效果图、元数据、布局。</summary>
public sealed record FactView(EffectGraph Effects, IEntityMetadata Metadata, RuntimeLayout Layout);

/// <summary>发现器（设计 9.6）：纯函数，只读查询面进，声明出。它看不到别的发现器的产出，也看不到选择的结果。</summary>
public interface IDiscoverer
{
    string Name { get; }
    IEnumerable<Claim> Propose(FactView facts);
}
