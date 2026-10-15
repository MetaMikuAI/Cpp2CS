using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

/// <summary>从托管引用参数确定栈对象，保留共享存储，并验证所有路径上的初始化。未知用途和冲突布局不生成方法体。</summary>
public sealed class StackObjects
{
    private readonly ManagedTypes types;
    private readonly List<StackLocalValue> objects = [];
    public List<RecoveryProblem> Problems { get; } = [];
    public IReadOnlyList<StackLocalValue> Objects => objects;

    private sealed record Access(long Offset, int Size);
    private sealed record Site(Stmt Statement, List<Access> Reads, Access? Write);

    public StackObjects(MachineFunction function, ManagedTypes types, Func<Call, AbiSignature?> signature)
    {
        this.types = types;
        if (!function.Blocks.SelectMany(b => b.Statements).SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).Any(e => e is FrameAddress)) return;
        var references = new Dictionary<Call, Dictionary<int, Access>>();
        var candidates = new List<(ulong Address, long Offset, TypeRef Type, int Size)>();
        foreach (var call in function.Blocks.SelectMany(b => b.Statements).OfType<Call>())
        {
            if (signature(call) is not { } shape) continue;
            var arguments = new Dictionary<int, Access>();
            foreach (var argument in shape.Arguments)
            {
                if (argument is not { Type: ByRefRef byRef, Passing: Passing.Registers, Pieces: [var piece] }) continue;
                var index = Array.IndexOf(call.Sources, piece.Register);
                if (index < 0 || index >= call.Arguments.Length || call.Arguments[index] is not FrameAddress frame) continue;
                var size = types.Size(byRef.Element);
                if (size <= 0 || frame.Offset >= 0 || frame.Offset + size > 0 || types.Kind(byRef.Element) is null or ValueKind.Void or ValueKind.Pointer)
                {
                    Problems.Add(new(call.Address, "栈对象范围或类型尚未支持"));
                    continue;
                }
                if (shape.Return is { } returned && types.Kind(returned.Type) == ValueKind.Pointer)
                    Problems.Add(new(call.Address, "栈引用经调用返回的别名尚未跟踪"));
                candidates.Add((call.Address, frame.Offset, byRef.Element, size));
                arguments[index] = new(frame.Offset, size);
            }
            references.Add(call, arguments);
        }
        foreach (var candidate in candidates.DistinctBy(c => (c.Offset, c.Type)).OrderBy(c => c.Offset).ThenByDescending(c => c.Size))
        {
            var overlaps = objects.Where(o => candidate.Offset < o.Offset + o.Width / 8 && o.Offset < candidate.Offset + candidate.Size).ToArray();
            if (overlaps.Length == 0) objects.Add(new(candidate.Offset, candidate.Type, candidate.Size * 8));
            else if (overlaps.Length != 1 || Location(candidate.Offset, candidate.Size * 8, candidate.Type) is null)
                Problems.Add(new(candidate.Address, "栈对象类型或范围重叠冲突"));
        }
        if (objects.Count == 0) return;

        var sites = new Dictionary<Block, List<Site>>();
        foreach (var block in function.Blocks)
        {
            var list = new List<Site>();
            foreach (var statement in block.Statements)
            {
                var reads = new List<Access>();
                Access? write = null;
                void Read(Expr expression)
                {
                    if (expression is Load { Address: FrameAddress frame } load)
                    {
                        if (Location(frame.Offset, load.Width) is null) Problems.Add(new(statement.Address, "栈读取位置与类型不符"));
                        else reads.Add(new(frame.Offset, load.Width / 8));
                        return;
                    }
                    if (expression is FrameAddress)
                    {
                        Problems.Add(new(statement.Address, "栈地址逃逸或间接用途尚未支持"));
                        return;
                    }
                    foreach (var child in ExprMap.Children(expression)) Read(child);
                }
                if (statement is Store store)
                {
                    Read(store.Value);
                    if (store.Target is FrameAddress frame)
                    {
                        if (Location(frame.Offset, store.Value.Width) is null) Problems.Add(new(statement.Address, "栈写入位置与类型不符"));
                        else write = new(frame.Offset, store.Value.Width / 8);
                    }
                    else Read(store.Target);
                }
                else if (statement is Call call)
                {
                    Read(call.Target);
                    for (var i = 0; i < call.Arguments.Length; i++)
                    {
                        if (references.TryGetValue(call, out var arguments) && arguments.TryGetValue(i, out var access)) reads.Add(access);
                        else Read(call.Arguments[i]);
                    }
                }
                else foreach (var operand in ExprMap.Operands(statement)) Read(operand);
                list.Add(new(statement, reads, write));
            }
            sites.Add(block, list);
        }
        if (Problems.Count > 0) return;
        CheckInitialization(function, sites);
    }

    public ManagedValue? Location(long offset, int width, TypeRef? expected = null)
    {
        if (width <= 0 || width % 8 != 0) return null;
        var root = objects.SingleOrDefault(o => offset >= o.Offset && offset + width / 8 <= o.Offset + o.Width / 8);
        if (root is null) return null;
        if (offset == root.Offset && width == root.Width && (expected is null || expected == root.Type)) return root;
        if (types.Kind(root.Type) != ValueKind.Struct || offset - root.Offset > int.MaxValue
            || types.FieldPath(root.Type, (int)(offset - root.Offset), width / 8) is not { } path) return null;
        ManagedValue value = root;
        foreach (var field in path) value = new FieldValue(value, field.Field, field.Type, types.Size(field.Type) * 8);
        return expected is null || value.Type == expected ? value : null;
    }

    public AddressValue? Address(long offset, TypeRef? expected = null)
    {
        var target = expected is null ? objects.SingleOrDefault(o => o.Offset == offset) : Location(offset, types.Size(expected) * 8, expected);
        return target is null ? null : new(target, new ByRefRef(target.Type));
    }

    private void CheckInitialization(MachineFunction function, Dictionary<Block, List<Site>> sites)
    {
        IEnumerable<long> Bytes(Access access) => Enumerable.Range(0, access.Size).Select(i => access.Offset + i);
        var universe = objects.SelectMany(o => Bytes(new(o.Offset, o.Width / 8))).ToHashSet();
        var incoming = function.Blocks.ToDictionary(b => b, _ => new HashSet<long>());
        var outgoing = function.Blocks.ToDictionary(b => b, _ => new HashSet<long>(universe));
        bool changed;
        do
        {
            changed = false;
            foreach (var block in function.Blocks)
            {
                var before = block == function.EntryBlock || block.Predecessors.Count == 0 ? [] : new HashSet<long>(outgoing[block.Predecessors[0]]);
                foreach (var predecessor in block.Predecessors.Skip(1)) before.IntersectWith(outgoing[predecessor]);
                var after = new HashSet<long>(before);
                foreach (var site in sites[block])
                    if (site.Write is { } write) after.UnionWith(Bytes(write));
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
                    if (!Bytes(read).All(initialized.Contains)) Problems.Add(new(site.Statement.Address, $"栈对象读取前未完整初始化: {read.Offset}:{read.Size}"));
                if (site.Write is { } write) initialized.UnionWith(Bytes(write));
            }
        }
    }
}
