using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Flow;

using Storage = Cpp2CS.Ir.Storage;

/// <summary>
/// IL2CPP 把 finally 写成按引用捕获局部的 lambda（<c>il2cpp::utils::Finally([&amp;]{...})</c>）。clang 不内联时，闭包留在调用方的栈上，
/// 其中存着被捕获局部的地址，lambda 成为一个没有元数据的函数。这些局部因此看起来地址逃逸，方法里对它们的读写都无法恢复。
/// 这里在 SSA 之前把这种调用展开回调用方：机器语义不变，SP 相对的访问落到调用方的帧下方，闭包内容经帧转发回到被捕获的局部。
/// 被调函数里的调用抛出异常时进入调用点的落地块，它自身不能带异常表。
/// 展开器在异常离开被调函数时恢复 SP 和被调用者保存的寄存器，正常返回时被调函数自己恢复它们，
/// 所以调用方在任何出口看到的都是调用前的值：副本里写这些寄存器的地方改用专属的临时存储，调用方的寄存器不变。
/// </summary>
internal sealed class ClosureInlining(CfgBuilder cfg, Func<ulong, bool> isClosure, Storage firstArgument, Storage stackPointer, Storage framePointer, IReadOnlySet<Storage> preserved)
{
    /// <summary>展开产生的块用这个标记位的合成地址，不与代码地址和路径复制的合成地址相交。</summary>
    private const ulong Synthetic = 1UL << 62;
    private const int MaxDepth = 3;
    private const int MaxBlocks = 4096;

    /// <summary>提升器只用低编号的临时存储，且只在单条指令内部使用。</summary>
    private const int FirstTemporary = 1024;

    private ulong next;
    private int temporaries = FirstTemporary;

    public void Run(MachineFunction function)
    {
        var depth = new Dictionary<Block, int>();
        var added = 0;
        var changed = false;
        var work = new Stack<Block>(function.Blocks);
        while (work.TryPop(out var block))
        {
            var level = depth.GetValueOrDefault(block);
            if (level >= MaxDepth || added >= MaxBlocks) continue;
            bool Candidate(Stmt statement) => statement is Call { Kind: CallKind.Direct, DoesNotReturn: false, Target: Const target }
                && target.Value != function.Entry && isClosure(target.Value);
            var index = block.Statements.FindIndex(Candidate);
            while (index >= 0 && !StackAddressInFirstArgument(block, index))
                index = block.Statements.FindIndex(index + 1, Candidate);
            if (index < 0) continue;
            var call = (Call)block.Statements[index];
            var callee = cfg.Build(((Const)call.Target).Value);
            if (callee.Problems.Count > 0 || callee.Range.ExceptionRegions.Length > 0) continue;
            var (blocks, continuation) = Inline(block, index, callee);
            added += blocks.Count;
            changed = true;
            function.Blocks.AddRange(blocks);
            function.Blocks.Add(continuation);
            depth[continuation] = level;
            foreach (var clone in blocks) depth[clone] = level + 1;
            work.Push(continuation);
            foreach (var clone in blocks) work.Push(clone);
        }
        if (changed) function.Renumber();
    }

    /// <summary>调用时第一个实参是栈地址：调用之前最近一次写入它的是 SP 或帧指针加常量。沿唯一前驱回溯，遇到调用为止。</summary>
    private bool StackAddressInFirstArgument(Block block, int call)
    {
        var at = block;
        var end = call;
        for (var steps = 0; steps < 4; steps++)
        {
            for (var i = end - 1; i >= 0; i--)
            {
                if (at.Statements[i] is Call) return false;
                if (at.Statements[i] is Assign assign && assign.Target == firstArgument) return IsStackAddress(assign.Value);
            }
            if (at.Predecessors is not [var predecessor]) return false;
            at = predecessor;
            end = at.Statements.Count;
        }
        return false;
    }

    private bool IsStackAddress(Expr value) => value switch
    {
        Read { Storage: var storage } => storage == stackPointer || storage == framePointer,
        Binary { Op: BinOp.Add or BinOp.Sub, Right: Const } binary => IsStackAddress(binary.Left),
        _ => false,
    };

    /// <summary>把 block 中 index 处的调用换成 callee 的一份副本。返回新块与调用之后的续接块。</summary>
    private (List<Block> Blocks, Block Continuation) Inline(Block block, int index, MachineFunction callee)
    {
        var call = (Call)block.Statements[index];
        var handler = block.Handler;
        var continuation = Fresh(block.End);
        continuation.Statements = [.. block.Statements.Skip(index + 1)];

        // 调用之后的语句和原有的正常后继归续接块；异常边属于这次调用，由副本里的调用继承。
        var normal = block.NormalSuccessors.ToArray();
        if (handler is not null) MachineFunction.RemoveEdgeAt(block, block.Successors.Count - 1);
        foreach (var successor in normal)
        {
            successor.Predecessors[successor.Predecessors.IndexOf(block)] = continuation;
            continuation.Successors.Add(successor);
        }
        block.Successors.Clear();
        block.Statements.RemoveRange(index, block.Statements.Count - index);

        // 副本写的 SP 和被调用者保存寄存器换成专属存储，入口时取调用方的值。
        var renamed = callee.Blocks.SelectMany(b => b.Statements).OfType<Assign>().Select(a => a.Target).Where(t => t == stackPointer || preserved.Contains(t))
            .Distinct().ToDictionary(t => t, _ => Storage.Temp(temporaries++));
        foreach (var (register, temporary) in renamed) block.Statements.Add(new Assign(call.Address, temporary, new Read(register, register.Width)));
        var movesStack = renamed.TryGetValue(stackPointer, out var stack);
        Stmt Rename(Stmt statement)
        {
            var mapped = renamed.Count == 0 ? statement : ExprMap.MapOperands(statement, e => ExprMap.Map(e, v => v is Read read && renamed.TryGetValue(read.Storage, out var temporary) ? new Read(temporary, read.Width) : null));
            return mapped is Assign assign && renamed.TryGetValue(assign.Target, out var target) ? assign with { Target = target } : mapped with { };
        }
        Call Copied(Call original)
        {
            var copy = ((Call)Rename(original)).Duplicate();
            return movesStack ? copy with { StackPointer = new Read(stack, stack.Width) } : copy;
        }
        var clones = callee.Blocks.ToDictionary(b => b, b => Fresh(b.End));
        var starts = callee.Blocks.ToDictionary(b => b.Start, b => clones[b].Start);
        var created = new List<Block>();
        foreach (var original in callee.Blocks)
        {
            var current = clones[original];
            created.Add(current);
            var statements = original.Statements.ToList();
            for (var i = 0; i < statements.Count; i++)
            {
                switch (statements[i])
                {
                    case Return:
                        Link(current, continuation);
                        break;
                    case Call { Kind: CallKind.Tail or CallKind.TailIndirect } tail:
                        // 尾调用返回到被调函数的调用者，也就是这里的续接点。
                        current = Called(current, Copied(tail) with { Kind = tail.Kind == CallKind.Tail ? CallKind.Direct : CallKind.Indirect }, handler, created);
                        Link(current, continuation);
                        break;
                    case Call inner:
                        // 落地块只接在块末尾的调用上：调用点在 try 内时，副本里的每个调用各自结束一个块。
                        current = i == statements.Count - 1 && inner.DoesNotReturn
                            ? Terminal(current, Copied(inner), handler)
                            : handler is null ? Append(current, Copied(inner)) : Called(current, Copied(inner), handler, created);
                        break;
                    case Jump jump:
                        current.Statements.Add(jump with { Target = starts[jump.Target] });
                        break;
                    case Branch branch:
                        current.Statements.Add((Branch)Rename(branch) with { Target = starts[branch.Target], Fallthrough = starts[branch.Fallthrough] });
                        break;
                    case IndirectJump table:
                        current.Statements.Add((IndirectJump)Rename(table) with { Targets = table.Targets.Select(t => starts[t]).ToArray() });
                        break;
                    default:
                        current.Statements.Add(Rename(statements[i]));
                        break;
                }
            }
            foreach (var successor in original.NormalSuccessors)
                Link(current, clones[successor]);
        }

        Link(block, clones[callee.EntryBlock]);
        return (created, continuation);
    }

    private static Block Append(Block block, Call call)
    {
        block.Statements.Add(call);
        return block;
    }

    private static Block Terminal(Block block, Call call, Block? handler)
    {
        block.Statements.Add(call);
        if (handler is not null) AttachHandler(block, handler);
        return block;
    }

    /// <summary>调用结束当前块，异常边接到调用点的落地块，返回接续的新块。</summary>
    private Block Called(Block block, Call call, Block? handler, List<Block> created)
    {
        block.Statements.Add(call);
        var following = Fresh(block.End);
        created.Add(following);
        Link(block, following);
        if (handler is not null) AttachHandler(block, handler);
        return following;
    }

    private static void AttachHandler(Block block, Block handler)
    {
        block.Handler = handler;
        Link(block, handler);
    }

    private static void Link(Block from, Block to)
    {
        from.Successors.Add(to);
        to.Predecessors.Add(from);
    }

    private Block Fresh(ulong end) => new(Synthetic | next++) { End = end };
}
