using Cpp2CS.Ir;

namespace Cpp2CS.Extensions.SourceView;

/// <summary>只把入口中完整、同路径的参数复制认回为状态机捕获字段。</summary>
public static class AsyncCaptures
{
    public static IReadOnlyDictionary<FieldDef, ArgumentValue>? Read(ManagedBody kickoff, out string reason)
    {
        reason = "";
        var statements = kickoff.Blocks.SelectMany(b => b.Statements).ToArray();
        var starts = statements.OfType<ManagedCall>().Where(c => c.Invocation.Method.Method.Name == "Start"
            && c.Invocation.Method.MethodArguments is [DefinitionRef]).ToArray();
        if (starts is not [var start] || start.Invocation.Arguments is not [AddressValue { Target: LocalValue machine }])
        { reason = "入口没有唯一的 Start(ref 状态机)"; return null; }
        var machineType = start.Invocation.Method.MethodArguments[0];
        if (!machine.Type.Equals(machineType)) { reason = "Start 状态机类型不一致"; return null; }
        var copies = statements.OfType<ManagedAssignment>().GroupBy(s => s.Target.Variable).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single().Value);
        var positions = kickoff.Blocks.SelectMany(b => b.Statements.Select((s, i) => (Statement: s, Block: b.Address, Index: i)))
            .ToDictionary(p => p.Statement, (IEqualityComparer<ManagedStatement>)ReferenceEqualityComparer.Instance);
        var predecessors = kickoff.Blocks.ToDictionary(b => b.Address, _ => new HashSet<ulong>());
        foreach (var block in kickoff.Blocks)
            foreach (var edge in block.Statements.SelectMany(ManagedValues.Edges))
                if (predecessors.TryGetValue(edge.Target, out var incoming)) incoming.Add(block.Address);
        var all = predecessors.Keys.ToHashSet();
        var dominators = all.ToDictionary(b => b, b => b == kickoff.Blocks[0].Address ? new HashSet<ulong> { b } : new HashSet<ulong>(all));
        bool changed;
        do
        {
            changed = false;
            foreach (var block in kickoff.Blocks.Skip(1))
            {
                var next = new HashSet<ulong>(all);
                if (predecessors[block.Address].Count == 0) next.Clear();
                foreach (var previous in predecessors[block.Address]) next.IntersectWith(dominators[previous]);
                next.Add(block.Address);
                if (!next.SetEquals(dominators[block.Address])) { dominators[block.Address] = next; changed = true; }
            }
        } while (changed);
        bool Before(ManagedStatement statement, ManagedStatement target)
        {
            var at = positions[statement]; var call = positions[target];
            return at.Block == call.Block ? at.Index < call.Index : dominators[call.Block].Contains(at.Block);
        }
        var writes = new Dictionary<FieldDef, List<(FieldRef[] Path, ManagedValue Value)>>();
        var captureStores = new List<ManagedStore>();
        foreach (var store in statements.OfType<ManagedStore>())
        {
            var (root, path) = Path(store.Target, null);
            if (root is not LocalValue local || local.Variable != machine.Variable || path.Length == 0) continue;
            if (path[0].Field.Name is "<>1__state" or "<>t__builder") continue;
            if (!Before(store, start)) { reason = $"捕获字段 {path[0].Field.Name} 未在 Start 前确定赋值"; return null; }
            captureStores.Add(store);
            if (!writes.TryGetValue(path[0].Field, out var entries)) writes.Add(path[0].Field, entries = []);
            if (store.Value is ComposedValue composed)
                entries.AddRange(composed.Leaves.Select(l => (path.Skip(1).Concat(l.Path).ToArray(), l.Value)));
            else entries.Add((path.Skip(1).ToArray(), store.Value));
        }
        foreach (var statement in statements)
        {
            var wholeWrite = statement is ManagedAssignment a && a.Target.Variable == machine.Variable
                || statement is ManagedStore s && Path(s.Target, null) is (LocalValue root, { Length: 0 }) && root.Variable == machine.Variable;
            if (wholeWrite && captureStores.Any(s => !Before(statement, s)))
            { reason = "捕获后重写了整个状态机"; return null; }
            if (statement is ManagedCall call && !ReferenceEquals(call, start)
                && call.Invocation.Arguments.Any(v => v is AddressValue { Target: LocalValue l } && l.Variable == machine.Variable))
            { reason = "状态机在 Start 之外按引用传出"; return null; }
        }
        var result = new Dictionary<FieldDef, ArgumentValue>();
        foreach (var (field, entries) in writes)
        {
            ArgumentValue? argument = null;
            var matched = new List<FieldRef[]>();
            foreach (var (target, value) in entries)
            {
                var (root, path) = Path(BooleanCopies.Argument(value, copies) ?? value, copies);
                if (root is not ArgumentValue source || !target.SequenceEqual(path)
                    || argument is not null && !argument.Equals(source))
                { reason = $"捕获字段 {field.Name} 不是同一参数的原样复制"; return null; }
                argument = source;
                matched.Add(target);
            }
            var fieldType = field.Type.Substitute(((DefinitionRef)machineType).Arguments, []);
            if (argument is null || !argument.Type.Equals(fieldType) || matched.Count == 0
                || !Complete(fieldType, [], matched, new HashSet<TypeRef>()))
            { reason = $"捕获字段 {field.Name} 的成员复制不完整或重复"; return null; }
            result.Add(field, argument);
        }
        return result;
    }

    private static (ManagedValue Root, FieldRef[] Fields) Path(ManagedValue value, Dictionary<Variable, ManagedValue>? copies)
    {
        var fields = new List<FieldRef>();
        var seen = new HashSet<Variable>();
        while (true)
        {
            switch (value)
            {
                case AddressValue a: value = a.Target; break;
                case IndirectValue { Address: AddressValue a }: value = a.Target; break;
                case FieldValue f: fields.Insert(0, f.Field); value = f.Receiver; break;
                case LocalValue l when copies is not null && seen.Add(l.Variable) && copies.TryGetValue(l.Variable, out var copy): value = copy; break;
                default: return (value, fields.ToArray());
            }
        }
    }

    private static bool Complete(TypeRef type, FieldRef[] prefix, List<FieldRef[]> paths, HashSet<TypeRef> seen)
    {
        var descendants = paths.Where(p => p.Take(prefix.Length).SequenceEqual(prefix)).ToArray();
        if (descendants.Any(p => p.Length == prefix.Length)) return descendants.Length == 1;
        if (type is not DefinitionRef { Definition.IsValueType: true } definition || !seen.Add(type)) return false;
        var fields = definition.Definition.Fields.Where(f => !f.IsStatic).ToArray();
        var complete = fields.Length > 0 && fields.All(f => Complete(f.Type.Substitute(definition.Arguments, []),
            [.. prefix, new FieldRef(f, definition)], paths, seen));
        seen.Remove(type);
        return complete;
    }
}
