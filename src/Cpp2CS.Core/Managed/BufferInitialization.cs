using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

/// <summary>验证返回缓冲区的所有读取和返回都发生在完整写入之后；入口地址不能流向未知用途。</summary>
public static class BufferInitialization
{
    private sealed record Region(long Offset, int Size);
    private sealed record Site(Stmt Statement, List<Region> Reads, List<Region> Writes);

    public static IReadOnlyList<RecoveryProblem> Check(MachineFunction function, AbiValue? result, ManagedTypes types, Func<Call, AbiSignature?> signature)
    {
        if (result is not { Passing: Passing.Indirect, Pieces: [var pointer] }) return [];
        var size = types.Size(result.Type);
        var root = new Use(new Variable(pointer.Register, 0), pointer.Width);
        var problems = new List<RecoveryProblem>();
        long? Offset(Expr expression) => expression == root ? 0 : expression is Binary { Op: BinOp.Add, Right: Const c } add && add.Left == root ? c.Signed : null;
        var sites = new Dictionary<Block, List<Site>>();
        foreach (var block in function.Blocks)
        {
            var list = new List<Site>();
            foreach (var statement in block.Statements)
            {
                var reads = new List<Region>();
                var writes = new List<Region>();
                void Access(List<Region> accesses, long offset, int bytes)
                {
                    if (offset < 0 || bytes <= 0 || offset + bytes > size) problems.Add(new(statement.Address, "返回缓冲区访问越界或大小未知"));
                    else accesses.Add(new(offset, bytes));
                }
                void Read(Expr expression)
                {
                    if (expression is Load load && Offset(load.Address) is { } at) { Access(reads, at, load.Width / 8); return; }
                    if (expression == root) { problems.Add(new(statement.Address, "返回缓冲区地址的用途尚未确认")); return; }
                    foreach (var child in ExprMap.Children(expression)) Read(child);
                }
                switch (statement)
                {
                    case Store store:
                        Read(store.Value);
                        if (Offset(store.Target) is { } at) Access(writes, at, store.Value.Width / 8);
                        else Read(store.Target);
                        break;
                    case Return returned:
                        if (returned.Buffer != root) problems.Add(new(statement.Address, "返回缓冲区不是入口地址"));
                        Access(reads, 0, size);
                        break;
                    case Call call:
                    {
                        Read(call.Target);
                        var shape = signature(call);
                        for (var i = 0; i < call.Arguments.Length; i++)
                        {
                            var argument = call.Arguments[i];
                            if (Offset(argument) is not { } location || i >= call.Sources.Length || shape is null) { Read(argument); continue; }
                            var register = call.Sources[i];
                            if (shape.Return is { Passing: Passing.Indirect, Pieces: [var output] } target && output.Register == register)
                                Access(writes, location, types.Size(target.Type));
                            else if (shape.Arguments.FirstOrDefault(a => a.Pieces is [var p] && p.Register == register) is { } parameter
                                && (parameter.Passing == Passing.Indirect || parameter.Type is ByRefRef))
                                Access(reads, location, types.Size(parameter.Type is ByRefRef byRef ? byRef.Element : parameter.Type));
                            else Read(argument);
                        }
                        if (call.Kind is CallKind.Tail or CallKind.TailIndirect)
                            if (!writes.Any(w => w.Offset == 0 && w.Size == size)) problems.Add(new(call.Address, "尾调用没有完整写回入口返回缓冲区"));
                        break;
                    }
                    default:
                        foreach (var operand in ExprMap.Operands(statement)) Read(operand);
                        break;
                }
                list.Add(new(statement, reads, writes));
            }
            sites.Add(block, list);
        }
        if (problems.Count > 0) return problems;
        IEnumerable<long> Bytes(Region region) => Enumerable.Range(0, region.Size).Select(i => region.Offset + i);
        var outgoing = function.Blocks.ToDictionary(b => b, _ => Enumerable.Range(0, size).Select(i => (long)i).ToHashSet());
        var incoming = function.Blocks.ToDictionary(b => b, _ => new HashSet<long>());
        bool changed;
        do
        {
            changed = false;
            foreach (var block in function.Blocks)
            {
                var before = block == function.EntryBlock || block.Predecessors.Count == 0 ? [] : new HashSet<long>(outgoing[block.Predecessors[0]]);
                foreach (var predecessor in block.Predecessors.Skip(1)) before.IntersectWith(outgoing[predecessor]);
                var after = new HashSet<long>(before);
                foreach (var site in sites[block]) foreach (var write in site.Writes) after.UnionWith(Bytes(write));
                incoming[block] = before;
                if (outgoing[block].SetEquals(after)) continue;
                outgoing[block] = after;
                changed = true;
            }
        } while (changed);
        foreach (var block in function.Blocks)
        {
            var initialized = new HashSet<long>(incoming[block]);
            foreach (var site in sites[block])
            {
                foreach (var read in site.Reads)
                    if (!Bytes(read).All(initialized.Contains)) problems.Add(new(site.Statement.Address, "返回缓冲区读取前未完整写入"));
                foreach (var write in site.Writes) initialized.UnionWith(Bytes(write));
            }
        }
        return problems;
    }
}
