using Cpp2CS.Facts;
using Cpp2CS.Image;
using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Flow;



public sealed class Block
{
    internal Block(ulong start) => Start = start;

    public int Index { get; internal set; }
    public ulong Start { get; }
    /// <summary>最后一条指令之后的地址。</summary>
    public ulong End { get; internal set; }
    private StatementList statements = [];
    public StatementList Statements
    {
        get => statements;
        set { value.Rewriter = statements.Rewriter; statements = value; }
    }
    /// <summary>后继。以 Branch 结尾时 [0] 为跳转目标、[1] 为顺序后继；异常边（Handler）总在最后。</summary>
    public List<Block> Successors { get; } = [];
    public List<Block> Predecessors { get; } = [];
    /// <summary>块末尾的调用抛出异常时进入的落地块。</summary>
    public Block? Handler { get; internal set; }
    public bool IsLandingPad { get; internal set; }
    /// <summary>不含异常边的后继。</summary>
    public IEnumerable<Block> NormalSuccessors => Handler is null ? Successors : Successors.Take(Successors.Count - 1);
    public override string ToString() => $"B{Index}@0x{Start:x}";
}

/// <summary>一个函数的控制流图。Blocks 按逆后序排列，Blocks[0] 为入口。</summary>
public sealed class MachineFunction
{
    public required ulong Entry { get; init; }
    public required CodeFunction Range { get; init; }
    public required List<Block> Blocks { get; set; }
    public List<string> Problems { get; } = [];
    /// <summary>无法解析为跳转表、按尾调用处理的寄存器间接跳转数（推测）。</summary>
    public int UnresolvedIndirectJumps { get; internal set; }
    public int JumpTables { get; internal set; }
    public Block EntryBlock => Blocks[0];
    /// <summary>传播删去的死定义及其所在块：机器状态里这些寄存器仍被写过，追溯某条指令处寄存器的值时需要它们。</summary>
    public List<(Block Block, Define Define)> Dead { get; } = [];

    /// <summary>重新按逆后序编号并删除不可达块（变换之后调用）。</summary>
    public void Renumber()
    {
        var order = new List<Block>();
        var seen = new HashSet<Block>();
        var stack = new Stack<(Block Block, int Next)>();
        stack.Push((Blocks[0], 0));
        seen.Add(Blocks[0]);
        while (stack.Count > 0)
        {
            var (block, next) = stack.Pop();
            if (next < block.Successors.Count)
            {
                stack.Push((block, next + 1));
                var successor = block.Successors[next];
                if (seen.Add(successor)) stack.Push((successor, 0));
            }
            else order.Add(block);
        }
        order.Reverse();
        foreach (var block in Blocks.Where(b => !seen.Contains(b)))
            while (block.Successors.Count > 0) RemoveEdge(block, block.Successors[^1]);
        for (var i = 0; i < order.Count; i++) order[i].Index = i;
        Blocks = order;
    }

    /// <summary>添加一条 from→to 的正常边（加在异常边之前）。to 中各 φ 的新操作数由调用方追加。</summary>
    public static void AddEdge(Block from, Block to)
    {
        if (from.Handler is not null) from.Successors.Insert(from.Successors.Count - 1, to);
        else from.Successors.Add(to);
        to.Predecessors.Add(from);
    }

    /// <summary>删除一条 from→to 边（有重边时删一条），同时删去 to 中各 φ 对应该前驱的操作数。</summary>
    public static void RemoveEdge(Block from, Block to)
    {
        var successor = from.Successors.LastIndexOf(to);
        if (successor < 0) throw new InvalidOperationException($"{from} → {to} 不是边");
        RemoveEdgeAt(from, successor);
    }

    /// <summary>按后继位置删除一条边，保留同目标的其他正常边、异常边及其 φ 输入。</summary>
    public static void RemoveEdgeAt(Block from, int successor)
    {
        var to = from.Successors[successor];
        var predecessor = PredecessorIndex(from, successor);
        var handler = from.Handler is not null && successor == from.Successors.Count - 1;
        from.Successors.RemoveAt(successor);
        to.Predecessors.RemoveAt(predecessor);
        if (handler) from.Handler = null;
        for (var i = 0; i < to.Statements.Count && to.Statements[i] is Phi phi; i++)
            to.Statements[i] = phi with { Sources = [.. phi.Sources[..predecessor], .. phi.Sources[(predecessor + 1)..]] };
    }

    /// <summary>后继位置对应的前驱位置；同一对块的重边按出现顺序对应。</summary>
    public static int PredecessorIndex(Block from, int successor)
    {
        var to = from.Successors[successor];
        var occurrence = from.Successors.Take(successor).Count(b => b == to);
        return to.Predecessors.Select((b, i) => (b, i)).Where(p => p.b == from).Select(p => p.i).ElementAt(occurrence);
    }

    public override string ToString()
    {
        var text = new System.Text.StringBuilder();
        foreach (var block in Blocks)
        {
            text.Append($"{block}{(block.IsLandingPad ? " landing" : "")} <- [{string.Join(", ", block.Predecessors)}]");
            if (block.Handler is not null) text.Append($" handler {block.Handler}");
            text.AppendLine();
            foreach (var stmt in block.Statements) text.AppendLine($"    {stmt.Address:x}: {stmt}");
            text.AppendLine($"    -> [{string.Join(", ", block.Successors)}]");
        }
        return text.ToString();
    }
}

/// <summary>
/// 递归下降构建控制流图。函数外的直接跳转视为尾调用；不返回的被调用者终止基本块；
/// LSDA 落地块作为额外入口，区间内的调用各自结束一个基本块并带一条到落地块的异常边。
/// </summary>
public sealed class CfgBuilder
{
    /// <summary>条件分支跳出函数时，用这个标记位构造的合成地址承载尾调用。</summary>
    private const ulong Synthetic = 1UL << 63;

    private readonly IMachine machine;
    private readonly CodeMap functions;

    public CfgBuilder(IMachine machine, CodeMap functions)
    {
        this.machine = machine;
        this.functions = functions;
        NoReturn = new NoReturnOracle(machine, functions);
    }

    public NoReturnOracle NoReturn { get; }
    public IMachine Machine => machine;
    public CodeMap Functions => functions;

    public MachineFunction Build(ulong entry)
    {
        var range = functions.At(entry) is { } found && found.Start == entry ? found : throw new InvalidOperationException($"0x{entry:x} 不是函数入口");
        return Build(entry, range);
    }

    public MachineFunction Build(ulong entry, CodeFunction range) => new Exploration(this, entry, range).Run();

    private sealed class Insn(ulong address, int size, List<Stmt> statements)
    {
        public ulong Address { get; } = address;
        public int Size { get; } = size;
        public List<Stmt> Statements { get; } = statements;
        public ulong[] Targets { get; set; } = [];
        public bool FallsThrough { get; set; }
        public bool Ends { get; set; }
        public bool IsCall { get; set; }
        public ulong Next => Address + (ulong)Size;
    }

    private sealed class Exploration(CfgBuilder owner, ulong entry, CodeFunction range)
    {
        private readonly Dictionary<ulong, Insn> insns = new();
        private readonly HashSet<ulong> leaders = [];
        private readonly Dictionary<ulong, ulong[]> tables = new();
        private readonly HashSet<ulong> failedTables = [];
        private readonly List<string> problems = [];
        private int resolvedTables;

        private bool InRange(ulong address) => range.Contains(address);

        private ExceptionRegion? RegionAt(ulong address)
        {
            foreach (var region in range.ExceptionRegions)
                if (address >= region.Start && address < region.End) return region;
            return null;
        }

        private bool HasLandingPad(ulong address) => RegionAt(address) is { LandingPad: not 0 };

        public MachineFunction Run()
        {
            var roots = new List<ulong> { entry };
            foreach (var region in range.ExceptionRegions)
                if (region.LandingPad != 0 && InRange(region.LandingPad) && !roots.Contains(region.LandingPad)) roots.Add(region.LandingPad);
            foreach (var root in roots)
            {
                leaders.Add(root);
                Explore(root);
            }
            while (true)
            {
                var blocks = Assemble(out var blockAt);
                var progress = false;
                foreach (var block in blocks)
                {
                    if (block.Statements.LastOrDefault() is not IndirectJump jump || tables.ContainsKey(jump.Address) || failedTables.Contains(jump.Address)) continue;
                    var targets = JumpTables.Resolve(owner.machine, block, blockAt, InRange);
                    if (targets is null) { failedTables.Add(jump.Address); continue; }
                    tables[jump.Address] = targets;
                    resolvedTables++;
                    foreach (var target in targets)
                    {
                        leaders.Add(target);
                        Explore(target);
                    }
                    progress = true;
                }
                if (!progress) return Finish(blocks, blockAt);
            }
        }

        private void Explore(ulong start)
        {
            var work = new Stack<ulong>();
            work.Push(start);
            while (work.Count > 0)
            {
                var address = work.Pop();
                if (insns.ContainsKey(address)) continue;
                if ((address & Synthetic) != 0)
                {
                    var target = address & ~Synthetic;
                    insns[address] = new Insn(address, 0, [new Call(target, CallKind.Tail, Expr.C(target, 64))]) { Ends = true };
                    continue;
                }
                var statements = new List<Stmt>();
                var size = owner.machine.Lift(address, statements);
                if (size == 0)
                {
                    problems.Add($"0x{address:x} 不可读");
                    insns[address] = new Insn(address, 0, [new Trap(address, "unreadable")]) { Ends = true };
                    continue;
                }
                var insn = new Insn(address, size, statements);
                insns[address] = insn;
                Classify(insn);
                if (insn.FallsThrough)
                {
                    if (!InRange(insn.Next))
                    {
                        insn.FallsThrough = false;
                        insn.Ends = true;
                        if (insn.IsCall && statements[^1] is Call { Kind: CallKind.Direct, Target: Const callee })
                            owner.NoReturn.AddEvidence(callee.Value);
                        else problems.Add($"0x{address:x} 顺序执行越出函数范围");
                    }
                    else
                    {
                        if (insn.Ends || insn.IsCall && HasLandingPad(address)) leaders.Add(insn.Next);
                        work.Push(insn.Next);
                    }
                }
                foreach (var target in insn.Targets)
                {
                    leaders.Add(target);
                    work.Push(target);
                }
            }
        }

        private void Classify(Insn insn)
        {
            var statements = insn.Statements;
            switch (statements.LastOrDefault())
            {
                case Jump jump when InRange(jump.Target):
                    insn.Targets = [jump.Target];
                    insn.Ends = true;
                    break;
                case Jump jump:
                    statements[^1] = new Call(jump.Address, CallKind.Tail, Expr.C(jump.Target, 64));
                    insn.Ends = true;
                    break;
                case Branch branch:
                    {
                        var target = InRange(branch.Target) ? branch.Target : branch.Target | Synthetic;
                        if (branch.Target == branch.Fallthrough)
                        {
                            statements[^1] = new Nop(branch.Address, "branch to next");
                            insn.FallsThrough = true;
                            break;
                        }
                        if (target != branch.Target) statements[^1] = branch with { Target = target };
                        insn.Targets = [target];
                        insn.FallsThrough = true;
                        insn.Ends = true;
                        break;
                    }
                case IndirectJump or Return or Trap:
                    insn.Ends = true;
                    break;
                case Call { Kind: CallKind.Tail or CallKind.TailIndirect }:
                    insn.Ends = true;
                    break;
                case Call call:
                    insn.IsCall = true;
                    if (call.Kind == CallKind.Direct && call.Target is Const callee && owner.NoReturn.IsNoReturn(callee.Value)) insn.Ends = true;
                    else insn.FallsThrough = true;
                    break;
                default:
                    insn.FallsThrough = true;
                    break;
            }
        }

        private List<Block> Assemble(out Dictionary<ulong, Block> blockAt)
        {
            blockAt = new Dictionary<ulong, Block>();
            var blocks = new List<Block>();
            var last = new Dictionary<Block, Insn>();
            Block? current = null;
            Insn? previous = null;
            foreach (var address in insns.Keys.Order())
            {
                var insn = insns[address];
                var start = current is null || previous is null || leaders.Contains(address) || previous.Ends || !previous.FallsThrough
                    || previous.Next != address || RegionAt(previous.Address) != RegionAt(address)
                    || previous.IsCall && HasLandingPad(previous.Address);
                if (start)
                {
                    current = new Block(address);
                    blocks.Add(current);
                    blockAt[address] = current;
                }
                current!.Statements.AddRange(insn.Statements);
                current.End = insn.Next;
                last[current] = insn;
                previous = insn;
            }
            foreach (var block in blocks)
            {
                var insn = last[block];
                foreach (var target in insn.Targets) Link(block, blockAt[target]);
                if (insn.FallsThrough) Link(block, blockAt[insn.Next]);
                if (insn.Statements.LastOrDefault() is IndirectJump jump && tables.TryGetValue(jump.Address, out var table))
                    foreach (var target in table.Distinct()) Link(block, blockAt[target]);
                if (insn.IsCall && RegionAt(insn.Address) is { LandingPad: not 0 } region && blockAt.TryGetValue(region.LandingPad, out var pad))
                {
                    block.Handler = pad;
                    pad.IsLandingPad = true;
                    Link(block, pad);
                }
            }
            return blocks;
        }

        private static void Link(Block from, Block to)
        {
            from.Successors.Add(to);
            to.Predecessors.Add(from);
        }

        private MachineFunction Finish(List<Block> blocks, Dictionary<ulong, Block> blockAt)
        {
            var unresolved = 0;
            foreach (var block in blocks)
            {
                if (block.Statements.LastOrDefault() is IndirectJump jump)
                {
                    if (tables.TryGetValue(jump.Address, out var table)) block.Statements[^1] = jump with { Targets = table };
                    else
                    {
                        // 无法解析的寄存器跳转按间接尾调用处理（推测：托管代码里常见于尾位置的虚调用）
                        block.Statements[^1] = new Call(jump.Address, CallKind.TailIndirect, jump.Target);
                        unresolved++;
                    }
                }
            }
            var conv = owner.machine.Convention;
            foreach (var root in range.ExceptionRegions.Select(r => r.LandingPad).Distinct())
            {
                if (!blockAt.TryGetValue(root, out var pad) || !pad.IsLandingPad) continue;
                pad.Statements.InsertRange(0, [
                    new Assign(root, conv.IntegerResults[0], new Intrinsic("eh_exception", [], 64)),
                    new Assign(root, conv.IntegerResults[1], new Intrinsic("eh_selector", [], 64)),
                ]);
            }
            var ordered = blocks.OrderBy(b => b.Start != entry).ToList();
            if (ordered[0].Predecessors.Count > 0)
            {
                // 入口处于环上：加一个空的起始块，保证入口值只从函数外流入
                var start = new Block(entry) { End = entry };
                Link(start, ordered[0]);
                ordered.Insert(0, start);
            }
            var function = new MachineFunction { Entry = entry, Range = range, Blocks = ordered };
            function.Problems.AddRange(problems);
            function.UnresolvedIndirectJumps = unresolved;
            function.JumpTables = resolvedTables;
            var all = function.Blocks.ToList();
            function.Renumber();
            if (function.Blocks.Count != all.Count)
                function.Problems.Add($"从入口不可达的块: {string.Join(", ", all.Except(function.Blocks).Select(b => $"0x{b.Start:x}"))}");
            return function;
        }
    }
}
