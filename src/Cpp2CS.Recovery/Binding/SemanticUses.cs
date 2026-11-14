using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Binding;

/// <summary>使用按绑定后的实参与有效位传播；切片、拼接与合流只传递被使用的位。</summary>
public sealed class SemanticUses
{
    public sealed record Use(Point Point, string Kind, Term Value, bool Address = false, bool Condition = false);
    private readonly Dictionary<ReadIdentity, HashSet<Use>> reads = [];
    public IReadOnlyList<Use> Roots { get; }
    private readonly IReadOnlyDictionary<Term, Merge> merges;

    public SemanticUses(QueryContext c, CallNamingQuery calls, StateQueries state, MethodBinder? binder = null, SignatureBinding? entry = null)
    {
        var function = c.Snapshot;
        merges = function.Blocks.SelectMany(b => b.Merges).ToDictionary(m => m.Result);
        var roots = new List<Use>();
        var sources = new BoundSourceQuery(state);
        void Source(BoundSource? source, Point point, string kind)
        {
            switch (source)
            {
                case null: break;
                case TermSource term: roots.Add(new(point, kind, term.Term)); break;
                case PiecesSource pieces:
                    foreach (var piece in pieces.Pieces) Source(piece.Source, point, kind);
                    break;
                case IndirectSource indirect: Source(indirect.Address, point, kind); break;
                case StackSource stack:
                    roots.Add(new(point, kind + "地址", stack.Area, true));
                    var value = c.Get(sources, new(stack, point));
                    if (value.IsSuccess) roots.Add(new(point, kind, value.Value));
                    break;
            }
        }
        foreach (var block in function.Blocks)
        {
            for (int i = 0; i < block.Statements.Length; i++)
            {
                var point = new Point(block.Identity, i);
                switch (block.Statements[i])
                {
                    case MemoryRead read: roots.Add(new(point, "读取地址", read.Address, true)); break;
                    case MemoryWrite write:
                        roots.Add(new(point, "写入地址", write.Address, true));
                        roots.Add(new(point, "写入值", write.Value)); break;
                    case Call call:
                        var classified = c.Get(calls, call.Identity);
                        BoundCall[]? bindings = classified.IsSuccess ? classified.Value switch
                        {
                            { Binding: { } binding } => [binding],
                            { Candidates: { Candidates.Length: > 0 } candidates } when candidates.Candidates.All(x => x.Binding.Success)
                                => candidates.Candidates.Select(x => x.Binding.Value!).ToArray(),
                            _ => null,
                        } : null;
                        if (bindings is null || bindings.Any(x => x.Signature.Signature.IsVariadic))
                            foreach (var arg in call.Arguments) roots.Add(new(point, "未绑定调用槽", arg.Value));
                        else foreach (var binding in bindings)
                        {
                            foreach (var argument in binding.Arguments) Source(argument.Source, point, "调用实参");
                            if (binding.Result.Source is IndirectSource indirect) Source(indirect.Address, point, "间接结果地址");
                        }
                        if (call.Target is ComputedTarget target) roots.Add(new(point, "调用目标", target.Value));
                        if (call.OutgoingArgumentArea is { } area) roots.Add(new(point, "传出实参区", area, true));
                        break;
                    default:
                        foreach (var value in SnapshotRewrite.Uses(block.Statements[i])) roots.Add(new(point, "语句输入", value));
                        break;
                }
            }
            var end = new Point(block.Identity, block.Statements.Length);
            if (block.End is Return ret && binder is not null && entry is not null)
            {
                var returned = binder.Return(ret, entry, function.Terms, function.Inputs.Select(x => new SlotValue(x.Slot, x.Value)).ToImmutableArray());
                if (returned.Success) Source(returned.Value!.Source, end, "返回值");
                else foreach (var value in SnapshotRewrite.Uses(ret)) roots.Add(new(end, "未绑定返回槽", value));
            }
            else foreach (var value in SnapshotRewrite.Uses(block.End))
                roots.Add(new(end, block.End is Branch ? "分支条件" : "结局输入", value, Condition: block.End is Branch));
        }
        Roots = roots;
        foreach (var use in roots) Visit(use.Value, (value, _, _) =>
        {
            if (value.Identity is not ResultAtom { Definition: ReadIdentity id }) return;
            if (!reads.TryGetValue(id, out var users)) reads[id] = users = [];
            users.Add(use);
        });
    }

    public IEnumerable<Use> Of(ReadIdentity id) => reads.GetValueOrDefault(id) ?? [];

    public void Visit(Term value, Action<Term, int, int> visit) => VisitWhile(value, (term, low, width) =>
    { visit(term, low, width); return true; });

    /// <summary>实际值已是完整映像地址时不再把地址计算的子项登记为另一地址。</summary>
    public HashSet<ulong> ImageAddresses(Term value, QueryContext context, StateQueries state)
    {
        if (!ReferenceEquals(context, barrenContext)) { barren.Clear(); barrenContext = context; }
        var addresses = new HashSet<ulong>();
        var seen = VisitWhile(value, (term, low, width) =>
        {
            if (low != 0 || width != context.Snapshot.AddressWidth || term.Width != width || term.ContainsUndefined) return true;
            var resolved = context.Get(state.Resolve, term);
            if (!resolved.IsSuccess || resolved.Value.ContainsUndefined) return true;
            var location = context.Get(state.Locations, new(resolved.Value, 8));
            if (location.IsSuccess && location.Value is { Region: Region.Image, Offset: { } offset } && offset >= 0 && offset <= ulong.MaxValue)
            { addresses.Add((ulong)offset); return false; }
            return true;
        }, barren);
        // 一次遍历没有找到映像地址时没有剪枝，走过的子项集合对后继封闭：其中每一项都到不了映像地址，之后不再重走。
        if (addresses.Count == 0) barren.UnionWith(seen);
        return addresses;
    }
    private readonly HashSet<(Term Value, int Low, int Width)> barren = [];
    private QueryContext? barrenContext;

    private HashSet<(Term Value, int Low, int Width)> VisitWhile(Term value, Func<Term, int, int, bool> visit,
        HashSet<(Term Value, int Low, int Width)>? skip = null)
    {
        var pending = new Stack<(Term Value, int Low, int Width)>(); pending.Push((value, 0, value.Width));
        var seen = new HashSet<(Term Value, int Low, int Width)>();
        while (pending.TryPop(out var item))
        {
            if (skip is not null && skip.Contains(item)) continue;
            if (!seen.Add(item)) continue;
            var (term, low, width) = item;
            if (!visit(term, low, width)) continue;
            if (term.Kind == TermKind.Slice) pending.Push((term.Operands[0], term.SliceLow!.Value + low, width));
            else if (term.Kind == TermKind.Concat)
            {
                int offset = 0;
                foreach (var part in term.Operands)
                {
                    int start = Math.Max(low, offset), end = Math.Min(low + width, offset + part.Width);
                    if (start < end) pending.Push((part, start - offset, end - start));
                    offset += part.Width;
                }
            }
            else if (merges.TryGetValue(term, out var merge))
                foreach (var input in merge.Inputs) pending.Push((input.Value, low, width));
            else foreach (var operand in term.Operands) pending.Push((operand, 0, operand.Width));
        }
        return seen;
    }
}
