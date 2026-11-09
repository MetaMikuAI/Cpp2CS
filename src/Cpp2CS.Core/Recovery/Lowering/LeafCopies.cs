using System.Reflection;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Lowering;

/// <summary>
/// 局部结构体的逐字段复制：原生代码把一个结构体值逐个字段（叶子或内层结构体）复制进栈上的局部。路径经过只读字段时，这样的写入在 IL 中不能写出
/// （只读字段只能在构造函数中取得可写地址），C# 也不能表达。连续的写入互不重叠、各自取自同一个按值来源的同一路径，中间没有其他语句时，
/// 就是整体赋值 L = S：来源与局部是不同的存储，逐个读和一次读到的是同一组值。
/// 写入没有盖满全部叶子时，只接受除这些写入外从不被写、地址也不交给调用的局部：其余叶子此前未定义，编译器只删去不可观察的写入，
/// 由来源补上这些叶子不改变可观察的行为。
/// </summary>
internal static class LeafCopies
{
    public static ManagedBody Run(ManagedBody body, ManagedTypes types)
    {
        var writes = new Dictionary<Variable, int>();
        var escaped = new HashSet<Variable>();
        static Variable? Root(ManagedValue target) => Path(target) is (LocalValue root, _) ? root.Variable : target is LocalValue local ? local.Variable : null;
        foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
        {
            var targets = ManagedValues.Edges(statement).SelectMany(e => e.Copies).Select(c => (ManagedValue)c.Target).ToList();
            if (statement is ManagedStore store) targets.Add(store.Target);
            if (statement is ManagedAssignment assignment) targets.Add(assignment.Target);
            foreach (var written in targets.Select(Root).OfType<Variable>()) writes[written] = writes.GetValueOrDefault(written) + 1;
            if (statement is ManagedCall call)
                escaped.UnionWith(ManagedValues.Of(call.Invocation).SelectMany(ManagedValues.Walk).OfType<AddressValue>().Select(a => Root(a.Target)).OfType<Variable>());
        }
        bool Fresh(LocalValue local, int stores) => writes.GetValueOrDefault(local.Variable) == stores && !escaped.Contains(local.Variable);
        var changed = false;
        var blocks = body.Blocks.Select(block =>
        {
            if (Merge(block.Statements, types, Fresh) is not { } statements) return block;
            changed = true;
            return block with { Statements = statements };
        }).ToArray();
        return changed ? body with { Blocks = blocks } : body;
    }

    private static List<ManagedStatement>? Merge(IReadOnlyList<ManagedStatement> statements, ManagedTypes types, Func<LocalValue, int, bool> fresh)
    {
        List<ManagedStatement>? output = null;
        for (var i = 0; i < statements.Count; i++)
        {
            if (Copy(statements, i, types, fresh) is var (count, assignment))
            {
                output ??= statements.Take(i).ToList();
                output.Add(assignment);
                i += count - 1;
                continue;
            }
            output?.Add(statements[i]);
        }
        return output;
    }

    private static (int Count, ManagedAssignment Assignment)? Copy(IReadOnlyList<ManagedStatement> statements, int start, ManagedTypes types, Func<LocalValue, int, bool> fresh)
    {
        if (statements[start] is not ManagedStore { Target: var first } || Path(first) is not (LocalValue local, _)
            || local.Type is not DefinitionRef structure || types.Kind(structure) != TypeKind.Struct) return null;
        var leaves = types.Projections(structure).Select(p => p.Path).ToList();
        var seen = new List<IReadOnlyList<FieldRef>>();
        ManagedValue? source = null;
        var end = start;
        bool Covers(IReadOnlyList<FieldRef> path, IReadOnlyList<FieldRef> leaf) => leaf.Count >= path.Count && leaf.Take(path.Count).SequenceEqual(path);
        for (; end < statements.Count && !leaves.All(l => seen.Any(p => Covers(p, l))); end++)
        {
            if (statements[end] is not ManagedStore store || Path(store.Target) is not (LocalValue target, var path) || !target.Equals(local)
                || Path(store.Value) is not (var root and (LocalValue or ArgumentValue), var read) || !read.SequenceEqual(path)
                || !root.Type.Equals(structure) || root.Equals(local) || source is not null && !source.Equals(root)
                || seen.Any(p => Covers(p, path) || Covers(path, p))) break;
            source = root;
            seen.Add(path);
        }
        // 写入的路径（叶子或其外层的结构体字段）互不重叠；没有盖满全部叶子时，局部的其余叶子须未定义。
        if (source is null || !leaves.All(l => seen.Any(p => Covers(p, l))) && !fresh(local, seen.Count)) return null;
        // 只改写经过只读字段的复制，其余逐叶子写入照常写出。
        if (!seen.Any(p => p.SkipLast(1).Any(f => (f.Field.Attributes & FieldAttributes.InitOnly) != 0))) return null;
        return (end - start, new ManagedAssignment(statements[start].Address, local, source));
    }

    /// <summary>字段访问链的根与路径；接收者可以经过取址。</summary>
    private static (ManagedValue Root, List<FieldRef> Path)? Path(ManagedValue value)
    {
        var path = new List<FieldRef>();
        while (true)
        {
            if (value is AddressValue address) value = address.Target;
            if (value is not FieldValue field) break;
            path.Insert(0, field.Field);
            value = field.Receiver;
        }
        return path.Count > 0 ? (value, path) : null;
    }
}
