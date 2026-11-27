using System.Collections.Immutable;
using Cpp2CS.Kernel.Engine;
using Cpp2CS.Kernel.Facts;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;

namespace Cpp2CS.Kernel;

/// <summary>
/// 把一组带凭据的声明照着写出来（设计第 10 节）。骨架是快照的控制流，去掉被消费的分支与只抛出尾；
/// 每条声明在落点处写出目录项的指令；项成为表达式，声明的定义与没有取定的块参数成为局部变量。
/// 每个表达式写出之后按目录展开回项，与要表达的项相同才算可得（值可得，设计 9.7）；写不出的地方是洞。
/// 选择用它试写来数洞、核对值可得；下降用它写出选定的解释。
/// 它不走查路径，不解释合流，不判断效果能否越过。
/// </summary>
internal sealed class Writer
{
    private sealed record Expr(ImmutableArray<ManagedInstruction> Code, TypeShape Type, bool Null = false);

    private readonly EffectGraph graph;
    private readonly IEntityMetadata metadata;
    private readonly IReadOnlyList<Certificate> selected;
    private readonly IReadOnlyList<ProofOutcome> outcomes;
    private readonly MethodShape host;
    private readonly TermPool terms;
    private readonly int pointerBits;
    private readonly PathConditions empty;
    private readonly Dictionary<Term, int> argumentOf = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<Term, Certificate> definitions = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<Certificate, int> definitionLocal = [];
    /// <summary>成为局部变量的块参数：每个块参数按用到的低位宽度各有一个局部变量（整个参数，或它的低位切片）。</summary>
    private readonly Dictionary<Term, SortedDictionary<int, int>> parameterLocals = new(ReferenceEqualityComparer.Instance);
    private int parameterLocalCount;
    /// <summary>操作数不可得、写不出来的声明：含有它们的选择不满足“值可得”。</summary>
    public List<Certificate> Unwritable { get; } = [];
    private readonly Dictionary<EffectRef, Certificate> occupiedBy = [];
    private readonly List<TypeShape?> localTypes = [];
    private readonly List<Term> localTerms = [];
    private readonly HashSet<Certificate> written = [];
    private readonly Dictionary<(Term, bool), Expr?> cache = [];
    private List<ManagedInstruction> code = [];
    private List<Hole> holes = [];
    private ProgramPoint use;
    private int labels;
    private bool[] kept = [];

    public IReadOnlyList<ManagedInstruction> Code => code;
    public IReadOnlyList<Hole> Holes => holes;
    public ImmutableArray<TypeShape> Locals => [.. localTypes.Select(t => t ?? new TypeShape(StackKind.Int32, 32, true, default))];
    public IReadOnlyList<Certificate> Selected => selected;
    public MethodShape Host => host;
    public EffectGraph Graph => graph;

    public Writer(EffectGraph graph, IEntityMetadata metadata, IReadOnlyList<Certificate> selected, IReadOnlyList<ProofOutcome> outcomes)
    {
        this.graph = graph;
        this.metadata = metadata;
        this.selected = selected;
        this.outcomes = outcomes;
        host = graph.Host;
        terms = graph.Snapshot.Terms;
        pointerBits = graph.Snapshot.PointerBits;
        empty = PathConditions.Empty(terms);
        foreach (var (value, _, index) in graph.Arguments) argumentOf.TryAdd(value, index);
        foreach (var certificate in selected)
        {
            foreach (var effect in certificate.Claim.Occupied) occupiedBy[effect] = certificate;
            if (certificate.Claim.Definition is not { } definition) continue;
            definitions.TryAdd(definition, certificate);
            definitionLocal[certificate] = localTypes.Count;
            localTypes.Add(certificate.ResultType);
            localTerms.Add(definition);
        }
    }

    /// <summary>写出。块参数的局部变量是按需出现的，所以反复写到它们的集合与类型不再变化。</summary>
    public void Run()
    {
        for (int round = 0; round < 8; round++)
        {
            int before = parameterLocalCount;
            var types = localTypes.ToArray();
            code = [];
            holes = [];
            labels = graph.Snapshot.BlockCount;
            written.Clear();
            cache.Clear();
            Unwritable.Clear();
            Write();
            if (parameterLocalCount == before && types.SequenceEqual(localTypes)) return;
        }
    }

    // ---- 骨架 ----

    private void Emit(string opcode, long operand = 0, EntityRef? entity = null, int target = -1) => code.Add(new(opcode, operand, entity, target));

    private void Hole(EffectRef? effect, string what, HoleLayer layer, Obligation? obligation, string reason, bool derived = false)
    {
        Emit(".unrecovered", holes.Count);
        holes.Add(new(effect, what, layer, obligation, reason, derived));
    }

    /// <summary>没被占用的效果为什么是洞：触及它的声明里最接近成立的那条的反驳（设计 9.8）。</summary>
    private void EffectHole(EffectRef effect, string what)
    {
        Refutation? closest = null;
        bool certified = false;
        foreach (var outcome in outcomes)
        {
            if (!outcome.Claim.Occupied.Contains(effect)) continue;
            if (outcome.Certificate is not null) { certified = true; continue; }
            if (closest is null || Rank(outcome.Refutation!) > Rank(closest)) closest = outcome.Refutation;
        }
        if (certified) Hole(effect, what, HoleLayer.Selection, null, "有凭据的声明没有被选中：占用冲突、落点约束不成立，或它的操作数不可得");
        else if (closest is null) Hole(effect, what, HoleLayer.Discovery, null, "没有声明触及这个效果");
        else Hole(effect, what, closest.Layer switch
        {
            RefutationLayer.Catalog => HoleLayer.Catalog,
            RefutationLayer.Fact => HoleLayer.Fact,
            RefutationLayer.Engine => HoleLayer.Engine,
            RefutationLayer.Budget => HoleLayer.Budget,
            _ => HoleLayer.Explanation,
        }, closest.Obligation, closest.Detail);
    }

    private static int Rank(Refutation refutation) => refutation.Layer != RefutationLayer.Explanation ? -1 : refutation.Obligation switch
    {
        Obligation.Legality => 0,
        Obligation.Coverage => 1,
        Obligation.Correspondence => 2,
        Obligation.Motion => 3,
        _ => 4,
    };

    private void Write()
    {
        var snapshot = graph.Snapshot;
        // 写出的块：从入口沿没有被消费的边可达的块；只抛出尾不写。被消费的分支之后接的是消费它的声明的落点所在的块。
        kept = new bool[snapshot.BlockCount];
        kept[snapshot.Entry.Index] = true;
        foreach (int index in graph.Order)
        {
            var block = new BlockId(index);
            if (!kept[index] || graph.EndsInThrow(block)) continue;
            if (Consumer(block) is { } consumer) { kept[consumer.Claim.Landing.Block.Index] = true; continue; }
            var exits = snapshot.Terminator(block).Exits;
            for (int e = 0; e < exits.Length; e++)
                if (exits[e].Kind == ExitKind.Target && !IsCheck(new EdgeId(block, e))) kept[exits[e].Target.Index] = true;
        }
        foreach (int index in graph.Order)
        {
            if (!kept[index]) continue;
            var block = new BlockId(index);
            Emit(".label", index);
            int count = snapshot.OccurrenceCount(block);
            bool ended = false;
            for (int p = 0; p <= count && !ended; p++)
            {
                Landing(new ProgramPoint(block, p));
                if (p == count || graph.Effect(new OccurrenceId(block, p)) is not { } effect) continue;
                var reference = EffectRef.Of(effect.Occurrence);
                if (effect.Kind == NativeEffectKind.Unnamed) Hole(reference, "未命名的效果", HoleLayer.Fact, null, effect.Detail);
                else if (effect.Kind == NativeEffectKind.Throw && effect.Value is null) EffectHole(reference, $"抛出 {effect.Exception}");
                else if (effect.Kind != NativeEffectKind.None && !occupiedBy.ContainsKey(reference))
                    EffectHole(reference, effect.Kind == NativeEffectKind.Throw ? "抛出异常对象" : effect.Kind.ToString());
                ended = effect.Ends;
                // 路径在这个效果处结束时，落在它之后的声明（占用它的那个操作）仍在这里写出。
                if (ended) Landing(new ProgramPoint(block, p + 1));
            }
            if (!ended) Terminate(block, count);
        }
    }

    private bool IsCheck(EdgeId edge) =>
        graph.Snapshot.Terminator(edge.Source) is { Kind: TerminatorKind.Branch } terminator
        && graph.Tail(terminator.Exits[edge.Exit].Target) != ExceptionKind.None;

    /// <summary>
    /// 被消费的分支（设计 9.5、第 10 节）：块末有一条不通往只抛出尾的出口被某条声明占用。这个分支是那个操作内部的判断，
    /// 输出里从这里直接接到那条声明的落点所在的块；凭据保证了经过这个分支的每条路径都到达落点，其间没有别的效果。
    /// </summary>
    private Certificate? Consumer(BlockId block)
    {
        var exits = graph.Snapshot.Terminator(block).Exits;
        for (int e = 0; e < exits.Length; e++)
            if (exits[e].Kind == ExitKind.Target && !IsCheck(new EdgeId(block, e))
                && occupiedBy.TryGetValue(EffectRef.Of(new EdgeId(block, e)), out var consumer)) return consumer;
        return null;
    }

    /// <summary>
    /// 块的参数在输出里有没有值：每条走得到的入边都由输出写出并赋值。入边的源块被一个被消费的分支略去，或源块的块末被消费
    /// （输出从那里直接接到落点，不经过这条边）时，经这条边进入的执行在输出里没有这次赋值，参数不可得。
    /// 源块是只抛出尾的不计：走到那里的执行以异常结束。
    /// </summary>
    private bool Assigned(BlockId block)
    {
        foreach (var edge in graph.Shape.InEdges(block))
        {
            if (!graph.Live(edge)) continue;
            var source = edge.Source;
            if (kept[source.Index] ? Consumer(source) is not null && !IsCheck(edge) : graph.Tail(source) == ExceptionKind.None) return false;
        }
        return true;
    }

    private void Terminate(BlockId block, int count)
    {
        use = new ProgramPoint(block, count + 1);
        var terminator = graph.Snapshot.Terminator(block);
        if (Consumer(block) is { } consumer)
        {
            for (int e = 0; e < terminator.Exits.Length; e++)
                if (IsCheck(new EdgeId(block, e)) && !occupiedBy.ContainsKey(EffectRef.Of(new EdgeId(block, e))))
                    EffectHole(EffectRef.Of(new EdgeId(block, e)), $"条件抛出 {graph.Tail(terminator.Exits[e].Target)}");
            Emit("br", target: consumer.Claim.Landing.Block.Index);
            return;
        }
        switch (terminator.Kind)
        {
            case TerminatorKind.Single when terminator.Exits[0].Kind == ExitKind.Target:
                Leave(new EdgeId(block, 0));
                return;
            case TerminatorKind.Single when terminator.Exits[0].Kind == ExitKind.Return:
                Return(block);
                return;
            case TerminatorKind.Branch:
            {
                bool first = IsCheck(new EdgeId(block, 0)), second = IsCheck(new EdgeId(block, 1));
                for (int e = 0; e < 2; e++)
                    if ((e == 0 ? first : second) && !occupiedBy.ContainsKey(EffectRef.Of(new EdgeId(block, e))))
                        EffectHole(EffectRef.Of(new EdgeId(block, e)), $"条件抛出 {graph.Tail(terminator.Exits[e].Target)}");
                if (first && second) return;
                if (first || second) { Leave(new EdgeId(block, first ? 1 : 0)); return; }
                Branch(block);
                return;
            }
            default:
                Hole(null, $"B{block.Index} 的块末", HoleLayer.Skeleton, null, $"{terminator.Kind} 的下降尚未实现");
                return;
        }
    }

    /// <summary>沿一条边离开：给目标块里需要的参数并行赋值，再转移。</summary>
    private void Leave(EdgeId edge)
    {
        var target = graph.Snapshot.Terminator(edge.Source).Exits[edge.Exit].Target;
        var parameters = graph.Snapshot.Parameters(target);
        var stores = new List<int>();
        for (int k = 0; k < parameters.Length; k++)
        {
            if (!parameterLocals.TryGetValue(parameters[k], out var widths)) continue;
            foreach (var (width, local) in widths)
            {
                var whole = graph.EdgeArgument(edge, k);
                var value = width == whole.Width ? whole : terms.Slice(whole, 0, width);
                if (Express(value, reference: width == pointerBits) is not { } expression)
                {
                    ValueHole($"B{edge.Source.Index}→B{target.Index} 上第 {k} 个参数的值", value);
                    continue;
                }
                // 局部变量的类型取各条入边上的值的类型；对象引用的类不一致时类未知。
                var known = localTypes[local];
                if (known is null) localTypes[local] = expression.Type;
                else if (known.Kind != expression.Type.Kind) { ValueHole($"B{target.Index} 第 {k} 个参数在各入边上的类型不同", value); continue; }
                else if (known.Entity != expression.Type.Entity && !expression.Null) localTypes[local] = known with { Entity = default };
                code.AddRange(expression.Code);
                stores.Add(local);
            }
        }
        for (int i = stores.Count - 1; i >= 0; i--) Emit("stloc", stores[i]);
        Emit("br", target: target.Index);
    }

    private void Return(BlockId block)
    {
        if (host.Return is not { } type) { Emit("ret"); return; }
        if (graph.Returned(block) is not { } stored) { Hole(null, "返回值", HoleLayer.Value, null, "返回值的槽位不在返回行里"); return; }
        // 返回值按返回类型存储：栈上的值只要低位（存储位宽）相同。候选：槽位里更宽的值，或按类型扩展的值。
        var candidates = new List<Term>();
        int stack = ClaimTemplate.StackBits(ClaimTemplate.OnStack(type));
        if (stored.Width == stack) candidates.Add(stored);
        else if (stored.Width < stack)
        {
            if (graph.ReturnSlot(block) is { } slot && slot.Width >= stack) candidates.Add(terms.Slice(slot, 0, stack));
            candidates.Add(type.Signed && !type.TwoValued ? terms.SignExtend(stored, stack) : terms.ZeroExtend(stored, stack));
        }
        foreach (var candidate in candidates)
        {
            if (!ReferenceEquals(terms.Slice(candidate, 0, stored.Width), stored)) continue;
            if (Express(candidate, type.Kind == StackKind.Object) is not { } expression || !Compatible(expression, ClaimTemplate.OnStack(type), 0)) continue;
            code.AddRange(expression.Code);
            Emit("ret");
            return;
        }
        ValueHole("返回值", stored);
    }

    private void Branch(BlockId block)
    {
        var condition = graph.Condition(block)!;
        int whenTrue = 0, whenFalse = 1;
        while (condition is { Kind: TermKind.Operation, Op: Op.Not }) (condition, whenTrue, whenFalse) = (condition.Operands[0], whenFalse, whenTrue);
        foreach (var (body, opcode, swap) in Conditions(condition))
        {
            int taken = swap ? whenFalse : whenTrue, other = swap ? whenTrue : whenFalse, trampoline = labels++;
            code.AddRange(body);
            Emit(opcode, target: trampoline);
            Leave(new EdgeId(block, other));
            Emit(".label", trampoline);
            Leave(new EdgeId(block, taken));
            return;
        }
        ValueHole($"B{block.Index} 的分支条件", condition);
    }

    /// <summary>
    /// 条件的写法：比较成为带条件的转移（目录里的 brfalse、blt、bne.un、cgt.un 与 brtrue）。给出转移之前的指令、转移的助记符，
    /// 以及转移是否在条件不成立时发生。每种写法都按目录展开回项核对，与条件（或它的否定）相同才给出。条件已去掉外层的取反。
    /// </summary>
    private IEnumerable<(List<ManagedInstruction> Body, string Opcode, bool Swap)> Conditions(Term condition)
    {
        var forms = new List<(Term[] Operands, string[] Middle, string Opcode, bool Swap)>();
        if (condition is { Kind: TermKind.Operation, Op: Op.Eq })
        {
            if (condition.Operands[1].IsZero) forms.Add(([condition.Operands[0]], [], "brfalse", false));
            forms.Add(([condition.Operands[0], condition.Operands[1]], [], "bne.un", true));
        }
        else if (condition is { Kind: TermKind.Operation, Op: Op.Slt }) forms.Add(([condition.Operands[0], condition.Operands[1]], [], "blt", false));
        else if (condition is { Kind: TermKind.Operation, Op: Op.Ult }) forms.Add(([condition.Operands[1], condition.Operands[0]], ["cgt.un"], "brtrue", false));
        else
        {
            // 一位的条件的其他写法，都只是候选，写出之后照常按目录展开核对：
            // 某个值的符号位——“小于零”；只取 0 与 1 的值的最低位——“非零”。
            if (condition is { Kind: TermKind.Slice } bit)
                foreach (int width in (int[])[32, 64])
                    if (bit.Offset == width - 1 && bit.Operands[0].Width >= width)
                        forms.Add(([bit.Operands[0].Width == width ? bit.Operands[0] : terms.Slice(bit.Operands[0], 0, width), terms.Zero(width)], [], "blt", false));
            forms.Add(([terms.ZeroExtend(condition, 32)], [], "brtrue", false));
        }
        foreach (var (operands, middle, opcode, swap) in forms)
        {
            var body = new List<ManagedInstruction>();
            bool available = true;
            foreach (var operand in operands)
            {
                if (Express(operand, reference: operand.Width == pointerBits && opcode == "brfalse") is not { } expression) { available = false; break; }
                body.AddRange(expression.Code);
            }
            if (!available) continue;
            foreach (string instruction in middle) body.Add(new(instruction));
            var expected = swap ? terms.Not(condition) : condition;
            if (Denote(body, opcode) is not { } denoted || !Same(denoted, expected)) continue;
            yield return (body, opcode, swap);
        }
    }

    private void ValueHole(string what, Term value)
    {
        // 值里含有别的洞的结果时，这个洞是派生的。
        bool derived = false;
        foreach (var leaf in Leaves(value))
            derived |= leaf.Kind == TermKind.Result && !definitions.ContainsKey(leaf) && graph.Effect(leaf.Occurrence) is { } effect
                && effect.Kind != NativeEffectKind.None && !occupiedBy.ContainsKey(EffectRef.Of(leaf.Occurrence));
        Hole(null, what, HoleLayer.Value, null, $"值不可得：{value}", derived);
    }

    private static IEnumerable<Term> Leaves(Term term)
    {
        var seen = new HashSet<Term>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<Term>();
        pending.Push(term);
        while (pending.Count > 0)
        {
            var current = pending.Pop();
            if (!seen.Add(current)) continue;
            if (current.Operands.Length == 0) yield return current;
            foreach (var operand in current.Operands) pending.Push(operand);
        }
    }

    // ---- 语句 ----

    /// <summary>落在这个程序点的声明，先按落点约束、再按稳定键排列，依次写出。</summary>
    private void Landing(ProgramPoint point)
    {
        use = point;
        var here = Selection.Order([.. selected.Where(c => c.Claim.Landing == point)])
            ?? throw new InvalidOperationException("落点相同的声明之间的落点约束成环：这组声明不该被选中");
        foreach (var certificate in here)
        {
            var claim = certificate.Claim;
            var entry = OperationCatalog.Get(claim.Operation);
            var body = new List<ManagedInstruction>();
            bool available = true;
            for (int i = 0; i < claim.Operands.Length && available; i++)
            {
                var expected = certificate.OperandTypes[i];
                if (Express(claim.Operands[i], expected.Kind == StackKind.Object) is { } expression
                    && Compatible(expression, expected, i == 0 ? certificate.ElementBits : 0)) body.AddRange(expression.Code);
                else
                {
                    available = false;
                    ValueHole($"{claim.Operation} 的第 {i} 个操作数（静态类型须与 {expected.Kind} 相容）", claim.Operands[i]);
                }
            }
            if (!available)
            {
                Unwritable.Add(certificate);
                continue;
            }
            code.AddRange(body);
            if (!entry.Elided) Emit(entry.Il, entity: claim.Entity);
            if (certificate.ResultType is not null)
            {
                if (definitionLocal.TryGetValue(certificate, out int local)) Emit("stloc", local);
                else Emit("pop");
            }
            written.Add(certificate);
        }
    }

    /// <summary>
    /// 静态类型相容（设计 9.7，不补转换）：栈上的类别相同；对象引用的类能当作所要求的类使用；数组操作的对象是元素位宽相符的数组；
    /// 托管指针指向的类型与所要求的相同（ECMA-335 III.1.8.1.2.1：托管指针之间只有指向同一类型才相容）——
    /// 两个地址数值相同（外层值与它偏移为零的字段）不说明它们的类型相同。
    /// </summary>
    private bool Compatible(Expr expression, TypeShape expected, int elementBits)
    {
        var actual = expression.Type;
        if (actual.Kind != expected.Kind) return false;
        if (expected.Kind == StackKind.ByRef) return expected.Entity == default || actual.Entity == expected.Entity;
        if (expected.Kind != StackKind.Object) return true;
        if (elementBits > 0)
            return !expression.Null && metadata.ElementOf(actual.Entity) is { } element && element.StorageBits == elementBits && element.Kind == StackKind.Int32;
        return expression.Null || expected.Entity == default || metadata.Assignable(actual.Entity, expected.Entity);
    }

    // ---- 值 ----

    private bool Same(Term a, Term b) => ReferenceEquals(a, b) || (a.Width == b.Width && empty.Same(a, b));

    /// <summary>项成为表达式。写出之后按目录展开回项，与原来的项相同才算数。</summary>
    private Expr? Express(Term term, bool reference)
    {
        if (cache.TryGetValue((term, reference), out var known) && (known is null || known.Code.All(i => i.Opcode != "ldloc" || Available((int)i.Operand))))
            return known is null ? null : Relabel(known);
        var built = Build(term, reference, 0);
        if (built is not null && (Denote(built.Code, null) is not { } denoted || !Same(denoted, term))) built = null;
        cache[(term, reference)] = built;
        return built;
    }

    /// <summary>方法体里每个标号只出现一次：再次取用的表达式里的标号换成新的。</summary>
    private Expr Relabel(Expr expression)
    {
        if (!expression.Code.Any(i => i.Opcode == ".label")) return expression;
        var renamed = new Dictionary<long, int>();
        int Rename(long label) => renamed.TryGetValue(label, out int fresh) ? fresh : renamed[label] = labels++;
        return expression with
        {
            Code = [.. expression.Code.Select(i => i.Opcode == ".label" ? i with { Operand = Rename(i.Operand) } : i.Target >= 0 ? i with { Target = Rename(i.Target) } : i)],
        };
    }

    /// <summary>局部变量在当前程序点有没有值：声明的定义从它的落点起可用（落点支配使用处，或同一程序点上已经写出）。</summary>
    private bool Available(int local)
    {
        foreach (var (certificate, index) in definitionLocal)
        {
            if (index != local) continue;
            var landing = certificate.Claim.Landing;
            return landing.Block == use.Block
                ? landing.Index < use.Index || (landing.Index == use.Index && written.Contains(certificate))
                : graph.Shape.Dominates(landing.Block, use.Block);
        }
        return true;
    }

    private Expr? Build(Term term, bool reference, int depth)
    {
        if (depth > 24) return null;
        if (definitions.TryGetValue(term, out var defined) && definitionLocal.TryGetValue(defined, out int local) && Available(local) && localTypes[local] is { } type)
            return new([new("ldloc", local)], type);
        if (argumentOf.TryGetValue(term, out int argument)) return new([new("ldarg", argument)], ClaimTemplate.OnStack(host.Parameters[argument]));
        if (term.Kind == TermKind.BlockParameter || term is { Kind: TermKind.Slice, Offset: 0 } && term.Operands[0].Kind == TermKind.BlockParameter)
        {
            var parameter = term.Kind == TermKind.BlockParameter ? term : term.Operands[0];
            if (!Assigned(parameter.Block)) return null;
            if (!parameterLocals.TryGetValue(parameter, out var widths)) parameterLocals[parameter] = widths = [];
            if (!widths.TryGetValue(term.Width, out int slot))
            {
                slot = widths[term.Width] = localTypes.Count;
                parameterLocalCount++;
                localTypes.Add(null);
                localTerms.Add(term);
            }
            return localTypes[slot] is { } assigned ? new([new("ldloc", slot)], assigned) : null;
        }
        if (term.IsConstant)
        {
            if (term.Width == 32) return new([new("ldc.i4", unchecked((int)(uint)term.Value))], Integer(32));
            return term.Width == pointerBits && term.IsZero && reference
                ? new([new("ldnull")], new TypeShape(StackKind.Object, pointerBits, false, default), Null: true) : null;
        }
        Expr? Unary(Term operand, string opcode, TypeShape result) =>
            Build(operand, false, depth + 1) is { } inner ? new([.. inner.Code, new(opcode)], result) : null;
        Expr? Binary(Term x, Term y, string opcode, bool sameKind = true)
        {
            if (Build(x, false, depth + 1) is not { } a || Build(y, false, depth + 1) is not { } b) return null;
            if (sameKind && a.Type.Kind != b.Type.Kind) return null;
            return new([.. a.Code, .. b.Code, new(opcode)], a.Type);
        }
        switch (term.Kind)
        {
            case TermKind.Operation when term.Width is 32 or 64:
                switch (term.Op)
                {
                    case Op.Add or Op.FAdd: return Binary(term.Operands[0], term.Operands[1], "add");
                    case Op.Sub or Op.FSub: return Binary(term.Operands[0], term.Operands[1], "sub");
                    case Op.Mul or Op.FMul: return Binary(term.Operands[0], term.Operands[1], "mul");
                    case Op.FDiv: return Binary(term.Operands[0], term.Operands[1], "div");
                    case Op.And: return Binary(term.Operands[0], term.Operands[1], "and");
                    case Op.Xor: return Binary(term.Operands[0], term.Operands[1], "xor");
                    case Op.Neg: return Build(term.Operands[0], false, depth + 1) is { } negated ? new([.. negated.Code, new("neg")], negated.Type) : null;
                    case Op.Shl: return Shift(term, "shl");
                    case Op.LShr: return Shift(term, "shr.un");
                    case Op.AShr: return Shift(term, "shr");
                    case Op.FConvert when term.Width == 64: return Unary(term.Operands[0], "conv.r8", Float(64));
                    case Op.UToF when term.Width == 64: return Unary(term.Operands[0], "conv.r.un", Float(64));
                    case Op.SignExtend when term.Width == 32 && term.Operands[0].Width == 16:
                        foreach (int width in (int[])[32, 64])
                            if (Lift(term.Operands[0], width) is { } wide && Unary(wide, "conv.i2", Integer(32)) is { } narrowed) return narrowed;
                        return null;
                }
                return null;
            case TermKind.Slice when term.Offset == 0 && term.Width == 32 && term.Operands[0].Width == 64:
                return Unary(term.Operands[0], "conv.i4", Integer(32));
            case TermKind.Concat when term.Operands.Length == 2 && term.Width is 32 or 64:
            {
                var (low, high) = (term.Operands[0], term.Operands[1]);
                // 高位补零：与掩码相与。低位补零：左移。
                if (high.IsZero && term.Width == 32 && Lift(low, 32) is { } masked)
                    return Binary(masked, terms.Constant((1L << low.Width) - 1, 32), "and");
                if (low.IsZero && Lift(high, term.Width) is { } shifted && Build(shifted, false, depth + 1) is { } value)
                    return new([.. value.Code, new("ldc.i4", low.Width), new("shl")], value.Type);
                return null;
            }
            case TermKind.Select:
                return Choose(term.Operands[0], term.Operands[1], term.Operands[2]);
            default:
                return null;
        }

        // 选择：IL 里没有选择指令，写成带栈上汇合的转移（ECMA-335 III.1.8.1.3：汇合处各条入边的栈状态合并）。
        // 条件的转移去往一支，另一支顺序执行后转到汇合处；两支在栈上的类别须相同。条件的写法与分支相同。
        Expr? Choose(Term condition, Term whenTrue, Term whenFalse)
        {
            while (condition is { Kind: TermKind.Operation, Op: Op.Not }) (condition, whenTrue, whenFalse) = (condition.Operands[0], whenFalse, whenTrue);
            if (Build(whenTrue, reference, depth + 1) is not { } a || Build(whenFalse, reference, depth + 1) is not { } b || a.Type.Kind != b.Type.Kind) return null;
            var type = a.Null ? b.Type : b.Null || a.Type.Entity == b.Type.Entity ? a.Type : a.Type with { Entity = default };
            foreach (var (body, opcode, swap) in Conditions(condition))
            {
                var (taken, fallthrough) = swap ? (b, a) : (a, b);
                int target = labels++, join = labels++;
                return new([.. body, new(opcode, Target: target), .. fallthrough.Code, new("br", Target: join),
                    new(".label", target), .. taken.Code, new(".label", join)], type, a.Null && b.Null);
            }
            return null;
        }

        Expr? Shift(Term shift, string opcode)
        {
            // 移位量在栈上是 int32；项里它与被移位的值同宽。
            var amount = shift.Operands[1];
            if (amount.Width != 32 && Lift(terms.Slice(amount, 0, 32), 32) is { } narrow) amount = narrow;
            return amount.Width == 32 ? Binary(shift.Operands[0], amount, opcode, sameKind: false) : null;
        }
    }

    private static TypeShape Integer(int bits) => new(bits == 32 ? StackKind.Int32 : StackKind.Int64, bits, true, default);
    private static TypeShape Float(int bits) => new(bits == 32 ? StackKind.Float32 : StackKind.Float64, bits, true, default);

    /// <summary>找一个更宽的项，它的低位就是给定的项：切片取被切的值，按位运算与加减乘逐操作数加宽。只是候选，写出之后另行核对。</summary>
    private Term? Lift(Term term, int width)
    {
        if (term.Width == width) return term;
        if (term.Width > width) return null;
        if (term.IsConstant) return terms.Constant(unchecked((long)(ulong)term.Value), width);
        if (term is { Kind: TermKind.Slice, Offset: 0 })
            return term.Operands[0].Width == width ? term.Operands[0] : term.Operands[0].Width > width ? terms.Slice(term.Operands[0], 0, width) : null;
        if (term.Kind == TermKind.Operation && term.Op is Op.Add or Op.Sub or Op.Mul or Op.And or Op.Or or Op.Xor
            && Lift(term.Operands[0], width) is { } a && Lift(term.Operands[1], width) is { } b)
            return term.Op switch
            {
                Op.Add => terms.Add(a, b), Op.Sub => terms.Sub(a, b), Op.Mul => terms.Mul(a, b),
                Op.And => terms.And(a, b), Op.Or => terms.Or(a, b), _ => terms.Xor(a, b),
            };
        return null;
    }

    /// <summary>
    /// 一段表达式代表哪个项：由按目录展开的读法（<see cref="ExpressionDenotation"/>）给出。ldarg 绑定宿主的形参与它存放的项，
    /// ldloc 绑定已有的局部变量与它代表的项。
    /// </summary>
    private Term? Denote(IReadOnlyList<ManagedInstruction> expression, string? branch) =>
        ExpressionDenotation.Denote(expression, branch, (argument, index) => argument ? (host.Parameters[index], graph.Stored[index])
            : localTypes[index] is { } type ? (type, localTerms[index]) : null, metadata, terms, pointerBits);
}
