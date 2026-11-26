using System.Buffers.Binary;
using System.Collections.Immutable;
using System.Security.Cryptography;

namespace Cpp2CS.Snapshot;

/// <summary>块末终结的种类。</summary>
public enum TerminatorKind : byte
{
    /// <summary>一个出口，无条件离开。</summary>
    Single,
    /// <summary>两个出口：条件为 1 走第 0 个，否则走第 1 个。</summary>
    Branch,
    /// <summary>跳转表：选择子等于 i 走第 i 个出口；最后一个出口是其余取值的去向。</summary>
    Switch,
    /// <summary>带展开出口的调用：块内最后一个出现是这次调用，第 0 个出口是正常返回，第 1 个是展开。</summary>
    Invoke,
}

/// <summary>出口的去向。</summary>
public enum ExitKind : byte
{
    /// <summary>去往本图的一个块，实参行与该块的参数逐项对应。</summary>
    Target,
    /// <summary>方法返回，实参行是各返回槽的值。</summary>
    Return,
    /// <summary>块以一次不返回的调用结束。</summary>
    NoReturn,
    /// <summary>陷阱：到达即终止。条件陷阱是一臂为陷阱的条件分支。</summary>
    Trap,
}

/// <summary>出口。边的身份是（源块，出口在终结里的序号）。</summary>
public sealed class Exit
{
    public ExitKind Kind { get; }
    /// <summary>Kind 为 Target 时的目标块。</summary>
    public BlockId Target { get; }
    /// <summary>整行实参：同一条边上的各项同时到达。</summary>
    public ImmutableArray<Term> Arguments { get; }

    private Exit(ExitKind kind, BlockId target, ImmutableArray<Term> arguments)
    {
        Kind = kind;
        Target = target;
        Arguments = arguments;
    }

    public static Exit To(BlockId target, params ReadOnlySpan<Term> arguments) => new(ExitKind.Target, target, [.. arguments]);
    public static Exit Return(params ReadOnlySpan<Term> values) => new(ExitKind.Return, default, [.. values]);
    public static Exit NoReturn { get; } = new(ExitKind.NoReturn, default, []);
    public static Exit Trap { get; } = new(ExitKind.Trap, default, []);
}

/// <summary>块末的终结。</summary>
public sealed class Terminator
{
    public TerminatorKind Kind { get; }
    /// <summary>Branch 的 1 位条件，或 Switch 的选择子。</summary>
    public Term? Condition { get; }
    public ImmutableArray<Exit> Exits { get; }
    /// <summary>追溯用的原生地址，不作身份。</summary>
    public ulong Address { get; }

    private Terminator(TerminatorKind kind, Term? condition, ImmutableArray<Exit> exits, ulong address)
    {
        Kind = kind;
        Condition = condition;
        Exits = exits;
        Address = address;
    }

    public static Terminator Single(Exit exit, ulong address = 0) => new(TerminatorKind.Single, null, [exit], address);
    public static Terminator Branch(Term condition, Exit whenTrue, Exit whenFalse, ulong address = 0) =>
        new(TerminatorKind.Branch, condition, [whenTrue, whenFalse], address);
    public static Terminator Switch(Term selector, ImmutableArray<Exit> exits, ulong address = 0) =>
        new(TerminatorKind.Switch, selector, exits, address);
    public static Terminator Invoke(Exit normal, Exit unwind, ulong address = 0) =>
        new(TerminatorKind.Invoke, null, [normal, unwind], address);
}

/// <summary>图里占位置的一项。</summary>
public interface IFlowOccurrence
{
    /// <summary>操作数，都是项。</summary>
    ImmutableArray<Term> Operands { get; }
    /// <summary>各结果槽的位宽。</summary>
    ImmutableArray<int> ResultWidths { get; }
    /// <summary>是否产生新的内存版本。</summary>
    bool DefinesMemory { get; }
    /// <summary>把内容写入摘要。操作数与结果位宽由图统一写入，这里只写其余的内容；追溯信息不写。</summary>
    void WriteContent(DigestWriter writer);
}

/// <summary>图的骨架：块、块参数、出现的操作数、出口与边。内核解释合流的三个操作只依赖这个接口。</summary>
public interface IFlowGraph
{
    /// <summary>图号，区分同一个项池里的多张图。</summary>
    int Graph { get; }
    int BlockCount { get; }
    /// <summary>入口块。它没有入边，使用入口参数而不是块参数。</summary>
    BlockId Entry { get; }
    ImmutableArray<Term> Parameters(BlockId block);
    int OccurrenceCount(BlockId block);
    IFlowOccurrence Occurrence(OccurrenceId occurrence);
    /// <summary>某个出现的各结果项。</summary>
    ImmutableArray<Term> Results(OccurrenceId occurrence);
    Terminator Terminator(BlockId block);
}

/// <summary>块。每个块只使用自己的参数和块内按次序产生的值。</summary>
public sealed class FlowBlock<T> where T : class, IFlowOccurrence
{
    public BlockId Id { get; }
    public ImmutableArray<Term> Parameters { get; }
    public ImmutableArray<T> Occurrences { get; }
    public ImmutableArray<ImmutableArray<Term>> Results { get; }
    public Terminator Terminator { get; }

    internal FlowBlock(BlockId id, ImmutableArray<Term> parameters, ImmutableArray<T> occurrences,
        ImmutableArray<ImmutableArray<Term>> results, Terminator terminator)
    {
        Id = id;
        Parameters = parameters;
        Occurrences = occurrences;
        Results = results;
        Terminator = terminator;
    }
}

/// <summary>不可变的图。只由 <see cref="FlowBuilder{T}"/> 在校验通过之后构造。</summary>
public sealed class FlowGraph<T> : IFlowGraph where T : class, IFlowOccurrence
{
    public int Graph { get; }
    public TermPool Terms { get; }
    public ImmutableArray<FlowBlock<T>> Blocks { get; }
    public ImmutableArray<Term> EntryParameters { get; }
    public ImmutableArray<int> ReturnWidths { get; }
    /// <summary>内容摘要（SHA-256）。只取决于图的内容，与项池的构造次序、图号、追溯信息无关。</summary>
    public ImmutableArray<byte> Digest { get; }

    internal FlowGraph(int graph, TermPool terms, ImmutableArray<FlowBlock<T>> blocks, ImmutableArray<Term> entryParameters,
        ImmutableArray<int> returnWidths, ImmutableArray<byte> digest)
    {
        Graph = graph;
        Terms = terms;
        Blocks = blocks;
        EntryParameters = entryParameters;
        ReturnWidths = returnWidths;
        Digest = digest;
    }

    public int BlockCount => Blocks.Length;
    public BlockId Entry => new(0);
    public FlowBlock<T> this[BlockId block] => Blocks[block.Index];
    public T this[OccurrenceId occurrence] => Blocks[occurrence.Block.Index].Occurrences[occurrence.Index];
    public ImmutableArray<Term> Parameters(BlockId block) => Blocks[block.Index].Parameters;
    public int OccurrenceCount(BlockId block) => Blocks[block.Index].Occurrences.Length;
    public IFlowOccurrence Occurrence(OccurrenceId occurrence) => this[occurrence];
    public ImmutableArray<Term> Results(OccurrenceId occurrence) => Blocks[occurrence.Block.Index].Results[occurrence.Index];
    public Terminator Terminator(BlockId block) => Blocks[block.Index].Terminator;
    public string DigestText => Convert.ToHexString(Digest.AsSpan());

    /// <summary>程序点处的内存版本：块内此前最近一个产生版本的出现；没有则是块入口的版本。</summary>
    public MemoryVersion VersionAt(ProgramPoint point)
    {
        var occurrences = Blocks[point.Block.Index].Occurrences;
        for (int i = Math.Min(point.Index, occurrences.Length) - 1; i >= 0; i--)
            if (occurrences[i].DefinesMemory) return new(point.Block, i);
        return new(point.Block, -1);
    }

    /// <summary>离开块时的内存版本，随该块的每条边传给目标块。</summary>
    public MemoryVersion VersionAtExit(BlockId block) => VersionAt(new(block, Blocks[block.Index].Occurrences.Length));
}

/// <summary>摘要的写入器。项按结构写入，共享的子项只写一次；不使用池内序号。</summary>
public sealed class DigestWriter
{
    private readonly IncrementalHash hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
    private readonly Dictionary<Term, int> numbers = new(ReferenceEqualityComparer.Instance);
    private readonly byte[] scratch = new byte[16];

    public void Write(int value)
    {
        BinaryPrimitives.WriteInt32LittleEndian(scratch, value);
        hash.AppendData(scratch, 0, 4);
    }

    public void Write(long value)
    {
        BinaryPrimitives.WriteInt64LittleEndian(scratch, value);
        hash.AppendData(scratch, 0, 8);
    }

    public void Write(UInt128 value)
    {
        BinaryPrimitives.WriteUInt128LittleEndian(scratch, value);
        hash.AppendData(scratch, 0, 16);
    }

    public void Write(string text)
    {
        var bytes = System.Text.Encoding.UTF8.GetBytes(text);
        Write(bytes.Length);
        hash.AppendData(bytes);
    }

    public void Write(Term term) => Write(Number(term));

    public void Write(ImmutableArray<Term> terms)
    {
        Write(terms.Length);
        foreach (var term in terms) Write(term);
    }

    private int Number(Term term)
    {
        if (numbers.TryGetValue(term, out int known)) return known;
        var operands = new int[term.Operands.Length];
        for (int i = 0; i < operands.Length; i++) operands[i] = Number(term.Operands[i]);
        int number = numbers.Count;
        numbers.Add(term, number);
        // 记号 -1 引出一个新项的定义，其后的引用用它的编号。
        Write(-1);
        Write((int)term.Kind);
        Write(term.Width);
        Write((int)term.Op);
        Write(term.Payload);
        // 图号不进入摘要：同一段代码在不同的图号下摘要相同。
        bool tagged = term.Kind is TermKind.EntryParameter or TermKind.BlockParameter or TermKind.Result;
        Write(tagged ? 0 : term.A);
        Write(term.B);
        Write(term.C);
        Write(term.D);
        Write(operands.Length);
        foreach (int operand in operands) Write(operand);
        return number;
    }

    internal ImmutableArray<byte> Finish() => [.. hash.GetHashAndReset()];
}

/// <summary>图不满足契约。Violations 列出全部违反之处。</summary>
public sealed class FlowException : Exception
{
    public ImmutableArray<string> Violations { get; }

    public FlowException(ImmutableArray<string> violations)
        : base($"图不满足契约，共 {violations.Length} 处：{string.Join("；", violations.Take(8))}")
    {
        Violations = violations;
    }
}

/// <summary>
/// 图的构造。先声明块（给出各参数的位宽），再向块里追加出现、设置终结，最后 <see cref="Build"/>。
/// Build 校验契约并计算摘要；校验不通过时抛出 <see cref="FlowException"/>，不产生图。
/// </summary>
public sealed class FlowBuilder<T> where T : class, IFlowOccurrence
{
    private sealed class Pending
    {
        public ImmutableArray<Term> Parameters;
        public readonly List<T> Occurrences = [];
        public readonly List<ImmutableArray<Term>> Results = [];
        public Terminator? Terminator;
    }

    private readonly List<Pending> blocks = [];
    private readonly List<Term> entryParameters = [];
    private ImmutableArray<int> returnWidths = [];
    private bool built;

    public TermPool Terms { get; }
    public int Graph { get; }

    public FlowBuilder(TermPool terms, int graph = 0)
    {
        Terms = terms;
        Graph = graph;
        blocks.Add(new Pending { Parameters = [] });
    }

    /// <summary>入口块。它总是第 0 个块，没有块参数。</summary>
    public BlockId Entry => new(0);
    public int BlockCount => blocks.Count;

    /// <summary>声明一个入口参数。同一个槽位只能声明一次。</summary>
    public Term EntryParameter(Slot slot, int width)
    {
        var term = Terms.EntryParameter(Graph, slot, width);
        foreach (var existing in entryParameters)
            if (existing.Slot == slot) throw new ArgumentException($"入口槽位 {slot} 重复声明");
        entryParameters.Add(term);
        return term;
    }

    /// <summary>各返回槽的位宽。每个返回出口的实参行都要与它逐项相符。</summary>
    public void SetReturnWidths(params ReadOnlySpan<int> widths) => returnWidths = [.. widths];

    /// <summary>声明一个块，给出各参数的位宽。</summary>
    public BlockId Block(params ReadOnlySpan<int> parameterWidths)
    {
        var id = new BlockId(blocks.Count);
        var parameters = ImmutableArray.CreateBuilder<Term>(parameterWidths.Length);
        for (int i = 0; i < parameterWidths.Length; i++) parameters.Add(Terms.BlockParameter(Graph, id, i, parameterWidths[i]));
        blocks.Add(new Pending { Parameters = parameters.MoveToImmutable() });
        return id;
    }

    public ImmutableArray<Term> Parameters(BlockId block) => At(block).Parameters;
    public Term Parameter(BlockId block, int index) => At(block).Parameters[index];
    public int OccurrenceCount(BlockId block) => At(block).Occurrences.Count;
    public bool IsTerminated(BlockId block) => At(block).Terminator is not null;

    /// <summary>构造中某个块已有的出现，只读。</summary>
    public IReadOnlyList<T> PendingOccurrences(BlockId block) => blocks[block.Index].Occurrences;
    /// <summary>构造中某个块的终结；尚未终结时抛出。</summary>
    public Terminator PendingTerminator(BlockId block) =>
        blocks[block.Index].Terminator ?? throw new InvalidOperationException($"{block} 尚未终结");

    private Pending At(BlockId block)
    {
        if (built) throw new InvalidOperationException("图已经构造完成");
        if ((uint)block.Index >= (uint)blocks.Count) throw new ArgumentException($"没有块 {block}");
        return blocks[block.Index];
    }

    /// <summary>向块末追加一个出现，返回它的各结果项。</summary>
    public ImmutableArray<Term> Append(BlockId block, T occurrence)
    {
        var pending = At(block);
        if (pending.Terminator is not null) throw new InvalidOperationException($"{block} 已经终结");
        var id = new OccurrenceId(block, pending.Occurrences.Count);
        var results = ImmutableArray.CreateBuilder<Term>(occurrence.ResultWidths.Length);
        for (int i = 0; i < occurrence.ResultWidths.Length; i++) results.Add(Terms.Result(Graph, id, i, occurrence.ResultWidths[i]));
        pending.Occurrences.Add(occurrence);
        pending.Results.Add(results.MoveToImmutable());
        return pending.Results[^1];
    }

    public void Terminate(BlockId block, Terminator terminator)
    {
        var pending = At(block);
        if (pending.Terminator is not null) throw new InvalidOperationException($"{block} 已经终结");
        pending.Terminator = terminator;
    }

    /// <summary>校验并构造。additional 用于在通用契约之外追加检查。</summary>
    public FlowGraph<T> Build(Action<FlowBuilder<T>, List<string>>? additional = null)
    {
        if (built) throw new InvalidOperationException("图已经构造完成");
        var violations = new List<string>();
        Validate(violations);
        additional?.Invoke(this, violations);
        if (violations.Count > 0) throw new FlowException([.. violations]);

        var writer = new DigestWriter();
        writer.Write(entryParameters.Count);
        foreach (var parameter in entryParameters)
        {
            writer.Write((int)parameter.Slot.Kind);
            writer.Write(parameter.Slot.Index);
            writer.Write(parameter.Width);
        }
        writer.Write(returnWidths.Length);
        foreach (int width in returnWidths) writer.Write(width);
        writer.Write(blocks.Count);
        var frozen = ImmutableArray.CreateBuilder<FlowBlock<T>>(blocks.Count);
        for (int b = 0; b < blocks.Count; b++)
        {
            var pending = blocks[b];
            writer.Write(pending.Parameters.Length);
            foreach (var parameter in pending.Parameters) writer.Write(parameter.Width);
            writer.Write(pending.Occurrences.Count);
            foreach (var occurrence in pending.Occurrences)
            {
                writer.Write(occurrence.Operands);
                writer.Write(occurrence.ResultWidths.Length);
                foreach (int width in occurrence.ResultWidths) writer.Write(width);
                writer.Write(occurrence.DefinesMemory ? 1 : 0);
                occurrence.WriteContent(writer);
            }
            var terminator = pending.Terminator!;
            writer.Write((int)terminator.Kind);
            writer.Write(terminator.Condition is null ? 0 : 1);
            if (terminator.Condition is not null) writer.Write(terminator.Condition);
            writer.Write(terminator.Exits.Length);
            foreach (var exit in terminator.Exits)
            {
                writer.Write((int)exit.Kind);
                writer.Write(exit.Kind == ExitKind.Target ? exit.Target.Index : -1);
                writer.Write(exit.Arguments);
            }
            frozen.Add(new FlowBlock<T>(new(b), pending.Parameters, [.. pending.Occurrences], [.. pending.Results], terminator));
        }
        built = true;
        return new FlowGraph<T>(Graph, Terms, frozen.MoveToImmutable(), [.. entryParameters], returnWidths, writer.Finish());
    }

    private void Validate(List<string> violations)
    {
        // 一、每个块都已终结；出口的形状与终结的种类相符。
        for (int b = 0; b < blocks.Count; b++)
        {
            var terminator = blocks[b].Terminator;
            if (terminator is null) { violations.Add($"B{b} 没有终结"); continue; }
            int exits = terminator.Exits.Length;
            switch (terminator.Kind)
            {
                case TerminatorKind.Single:
                    if (exits != 1) violations.Add($"B{b} 的单出口终结有 {exits} 个出口");
                    break;
                case TerminatorKind.Branch:
                    if (exits != 2) violations.Add($"B{b} 的条件分支有 {exits} 个出口");
                    if (terminator.Condition is not { Width: 1 }) violations.Add($"B{b} 的分支条件不是 1 位");
                    break;
                case TerminatorKind.Switch:
                    if (exits < 2) violations.Add($"B{b} 的跳转表少于 2 个出口");
                    if (terminator.Condition is null) violations.Add($"B{b} 的跳转表没有选择子");
                    break;
                case TerminatorKind.Invoke:
                    if (exits != 2 || terminator.Exits.Any(e => e.Kind != ExitKind.Target)) violations.Add($"B{b} 的带展开出口的调用须有两个去往块的出口");
                    if (blocks[b].Occurrences.Count == 0) violations.Add($"B{b} 以带展开出口的调用终结，但块内没有出现");
                    break;
            }
            if (terminator.Kind != TerminatorKind.Single && terminator.Exits.Any(e => e.Kind == ExitKind.NoReturn))
                violations.Add($"B{b}：不返回的出口只能单独作为终结");
        }
        if (violations.Count > 0) return;

        // 二、边：目标存在，入口块没有入边，整行实参与目标块的参数个数、位宽逐项相符。
        var reached = new bool[blocks.Count];
        var work = new Stack<int>();
        reached[0] = true;
        work.Push(0);
        while (work.Count > 0)
        {
            int b = work.Pop();
            var terminator = blocks[b].Terminator!;
            for (int e = 0; e < terminator.Exits.Length; e++)
            {
                var exit = terminator.Exits[e];
                string edge = $"B{b} 的出口 {e}";
                switch (exit.Kind)
                {
                    case ExitKind.Target:
                        if ((uint)exit.Target.Index >= (uint)blocks.Count) { violations.Add($"{edge} 的目标 {exit.Target} 不存在"); break; }
                        if (exit.Target.Index == 0) { violations.Add($"{edge} 指向入口块；原生代码跳回第一条指令时须另设循环头"); break; }
                        var parameters = blocks[exit.Target.Index].Parameters;
                        if (exit.Arguments.Length != parameters.Length)
                            violations.Add($"{edge} 给出 {exit.Arguments.Length} 个实参，{exit.Target} 有 {parameters.Length} 个参数");
                        else
                            for (int i = 0; i < parameters.Length; i++)
                                if (exit.Arguments[i].Width != parameters[i].Width)
                                    violations.Add($"{edge} 的第 {i} 个实参是 {exit.Arguments[i].Width} 位，{exit.Target} 的参数是 {parameters[i].Width} 位");
                        if (!reached[exit.Target.Index]) { reached[exit.Target.Index] = true; work.Push(exit.Target.Index); }
                        break;
                    case ExitKind.Return:
                        if (exit.Arguments.Length != returnWidths.Length)
                            violations.Add($"{edge} 返回 {exit.Arguments.Length} 个值，返回槽有 {returnWidths.Length} 个");
                        else
                            for (int i = 0; i < returnWidths.Length; i++)
                                if (exit.Arguments[i].Width != returnWidths[i])
                                    violations.Add($"{edge} 的第 {i} 个返回值是 {exit.Arguments[i].Width} 位，返回槽是 {returnWidths[i]} 位");
                        break;
                    default:
                        if (exit.Arguments.Length != 0) violations.Add($"{edge} 不带实参");
                        break;
                }
            }
        }
        for (int b = 0; b < blocks.Count; b++)
            if (!reached[b]) violations.Add($"B{b} 从入口不可达");

        // 三、值的可见性：块只使用自己的参数和块内此前产生的值；入口参数只在入口块可见。
        for (int b = 0; b < blocks.Count; b++)
        {
            var pending = blocks[b];
            var need = new Dictionary<Term, int>(ReferenceEqualityComparer.Instance);
            void Use(Term term, int limit, string where)
            {
                int required = Need(term, b, need, out string? reason);
                if (required < 0) violations.Add($"B{b} {where} 使用了不可见的值：{reason}");
                else if (required > limit) violations.Add($"B{b} {where} 使用了块内其后才产生的结果");
            }
            for (int i = 0; i < pending.Occurrences.Count; i++)
                foreach (var operand in pending.Occurrences[i].Operands) Use(operand, i, $"的出现 {i}");
            var terminator = pending.Terminator!;
            int all = pending.Occurrences.Count;
            if (terminator.Condition is not null) Use(terminator.Condition, all, "的终结条件");
            for (int e = 0; e < terminator.Exits.Length; e++)
                foreach (var argument in terminator.Exits[e].Arguments) Use(argument, all, $"的出口 {e}");
        }
    }

    /// <summary>项在块 b 里可见所需的“已产生的出现数”；不可见时返回 -1。</summary>
    private int Need(Term term, int b, Dictionary<Term, int> memo, out string? reason)
    {
        reason = null;
        if (memo.TryGetValue(term, out int known))
        {
            if (known < 0) reason = term.ToString();
            return known;
        }
        int result;
        switch (term.Kind)
        {
            case TermKind.EntryParameter:
                result = term.Graph == Graph && b == 0 && entryParameters.Contains(term) ? 0 : -1;
                if (result < 0) reason = b == 0 ? $"未声明的入口参数 {term}" : $"入口参数 {term} 只在入口块可见，须作为实参传入";
                break;
            case TermKind.BlockParameter:
                result = term.Graph == Graph && term.Block.Index == b && term.ParameterIndex < blocks[b].Parameters.Length
                    && ReferenceEquals(blocks[b].Parameters[term.ParameterIndex], term) ? 0 : -1;
                if (result < 0) reason = $"别的块的参数 {term}";
                break;
            case TermKind.Result:
            {
                var occurrence = term.Occurrence;
                bool own = term.Graph == Graph && occurrence.Block.Index == b && occurrence.Index < blocks[b].Occurrences.Count
                    && term.ResultIndex < blocks[b].Results[occurrence.Index].Length
                    && ReferenceEquals(blocks[b].Results[occurrence.Index][term.ResultIndex], term);
                result = own ? occurrence.Index + 1 : -1;
                if (!own) reason = $"别的块的结果 {term}";
                break;
            }
            default:
                result = 0;
                foreach (var operand in term.Operands)
                {
                    int inner = Need(operand, b, memo, out reason);
                    if (inner < 0) { result = -1; break; }
                    result = Math.Max(result, inner);
                }
                break;
        }
        memo[term] = result;
        return result;
    }
}
