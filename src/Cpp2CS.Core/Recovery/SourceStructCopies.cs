using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>局部结构体的完整字段快照、复制和清零，按值恢复；不跨越其他语句。</summary>
internal static class SourceStructCopies
{
    /// <summary>同一结构体的全部直属字段原样重组，就是该位置的值；只在完整覆盖时折回整体复制。</summary>
    internal static ManagedValue? WholeValue(ComposedValue value)
    {
        if (value.StructType is not DefinitionRef type || value.Leaves.Count == 0) return null;
        var fields = type.Definition.Fields.Where(f => !f.IsStatic).ToHashSet();
        if (fields.Count != value.Leaves.Count) return null;
        ManagedValue? root = null;
        foreach (var (path, leaf) in value.Leaves)
        {
            if (path.Count != 1 || leaf is not FieldValue field || !field.Field.Equals(path[0])
                || !fields.Remove(field.Field.Field)) return null;
            var receiver = field.Receiver is AddressValue address ? address.Target : field.Receiver;
            if (!Stable(receiver) || !receiver.Type.Equals(value.StructType)
                || root is not null && !root.Equals(receiver)) return null;
            root = receiver;
        }
        return root;
    }

    internal static ManagedBody Rewrite(ManagedBody body)
    {
        static LocalValue? Local(ManagedValue value) => value switch
        {
            LocalValue local => local,
            AddressValue { Target: LocalValue local } => local,
            _ => null,
        };
        static ManagedValue? Destination(ManagedValue value) => value is AddressValue { Target: FieldValue { Receiver: LocalValue or ArgumentValue } field }
            ? field : Local(value);
        var uses = body.Blocks.SelectMany(b => b.Statements).SelectMany(s =>
                (s is ManagedAssignment a ? [a.Value] : ManagedValues.Of(s)).Concat(ManagedValues.CopiedValues(s)))
            .SelectMany(ManagedValues.Walk).OfType<LocalValue>().GroupBy(l => l.Variable).ToDictionary(g => g.Key, g => g.Count());
        var next = body.Blocks.SelectMany(b => b.Statements).SelectMany(s => ManagedValues.Of(s)
                .Concat(ManagedValues.CopiedValues(s)).Concat(ManagedValues.Edges(s).SelectMany(e => e.Copies).Select(c => c.Target))
                .Concat(s switch { ManagedCall { Result: { } r } => [r], ManagedAwait { Result: { } r } => [r], _ => Array.Empty<ManagedValue>() }))
            .Concat(body.Regions.Select(r => r.Exception).OfType<ManagedValue>()).SelectMany(ManagedValues.Walk).OfType<LocalValue>()
            .Where(l => l.Variable.Storage.Bank == Bank.Temp).Select(l => l.Variable.Storage.Index).DefaultIfEmpty(0).Max() + 1;
        return body with { Blocks = body.Blocks.Select(block =>
        {
            var statements = block.Statements.ToList();
            // 嵌套结构体按叶子读取后立即完整写入同型位置，仍是一次整值复制。
            for (var i = 0; i < statements.Count; i++)
            {
                if (statements[i] is not ManagedAssignment first || FieldPath(first.Value) is not { } initial
                    || initial.Root.Type is not DefinitionRef type || LeafPaths(type) is not { Count: > 0 } paths) continue;
                var count = paths.Count;
                var reads = statements.Skip(i).Take(count).OfType<ManagedAssignment>().ToArray();
                if (reads.Length != count || reads.Any(r => FieldPath(r.Value) is not { } path || path.Root != initial.Root)
                    || reads.Select(r => r.Target.Variable).Distinct().Count() != count) continue;
                var snapshots = reads.ToDictionary(r => r.Target.Variable, r => FieldPath(r.Value)!.Value.Path);
                if (!SamePaths(paths, snapshots.Values)) continue;
                var destinations = new Dictionary<ManagedValue, List<IReadOnlyList<FieldRef>>>();
                var initialized = new HashSet<LocalValue>();
                var consumed = new Dictionary<Variable, int>();
                var end = i + count;
                while (end < statements.Count)
                {
                    if (statements[end] is ManagedStore { Target: IndirectValue { Address: AddressValue { Target: LocalValue zero } },
                            Value: ComposedValue { Leaves.Count: 0 } } && zero.Type.Equals(type) && zero != initial.Root && !destinations.ContainsKey(zero))
                        initialized.Add(zero);
                    else if (statements[end] is ManagedStore write && FieldPath(write.Target, write: true) is { } target && target.Root.Type.Equals(type)
                        && write.Value is LocalValue local && snapshots.TryGetValue(local.Variable, out var sourcePath) && sourcePath.SequenceEqual(target.Path))
                    {
                        if (!destinations.TryGetValue(target.Root, out var copied)) destinations[target.Root] = copied = [];
                        if (copied.Any(p => p.SequenceEqual(target.Path))) break;
                        copied.Add(target.Path);
                        consumed[local.Variable] = consumed.GetValueOrDefault(local.Variable) + 1;
                    }
                    else break;
                    end++;
                }
                if (destinations.Count == 0 || destinations.Values.Any(copied => !SamePaths(paths, copied))
                    || initialized.Any(d => !destinations.ContainsKey(d))
                    || snapshots.Keys.Any(v => consumed.GetValueOrDefault(v) != uses.GetValueOrDefault(v))
                    || destinations.Count > 1 && (initial.Root is not (LocalValue or ArgumentValue) || destinations.Keys.Any(d => d is not LocalValue))) continue;
                var replacements = new List<ManagedStatement>();
                var source = initial.Root;
                if (destinations.Count > 1)
                {
                    // 多个局部目标可交错写入；先保存整值，避免某个目标覆盖来源后影响后续复制。
                    var snapshot = new LocalValue(new Variable(Storage.Temp(next++), 1), type, 0);
                    replacements.Add(new ManagedAssignment(first.Address, snapshot, source));
                    source = snapshot;
                }
                replacements.AddRange(destinations.Keys.Select(d => d is LocalValue localTarget
                    ? (ManagedStatement)new ManagedAssignment(first.Address, localTarget, source) : new ManagedStore(first.Address, d, source)));
                statements.RemoveRange(i, end - i);
                statements.InsertRange(i, replacements);
                i += replacements.Count - 1;
            }
            // 全部直属字段立即重组到返回值或参数时，在原读取位置保存整个结构体。
            for (var i = 0; i < statements.Count; i++)
            {
                if (statements[i] is not ManagedAssignment { Value: FieldValue { Accessor: null } field } first) continue;
                var root = field.Receiver is AddressValue address ? address.Target : field.Receiver;
                if (root.Type is not DefinitionRef { Definition: { IsValueType: true, IsEnum: false } definition }
                    || !Stable(root) || (definition.Attributes & System.Reflection.TypeAttributes.LayoutMask) == System.Reflection.TypeAttributes.ExplicitLayout) continue;
                var fields = definition.Fields.Where(f => !f.IsStatic).ToHashSet();
                var reads = statements.Skip(i).Take(fields.Count).OfType<ManagedAssignment>().ToArray();
                if (fields.Count == 0 || reads.Length != fields.Count || i + fields.Count >= statements.Count
                    || reads.Any(r => r.Value is not FieldValue { Accessor: null } f || !f.Receiver.Equals(field.Receiver)
                        || !fields.Contains(f.Field.Field) || uses.GetValueOrDefault(r.Target.Variable) != 1)
                    || reads.Select(r => ((FieldValue)r.Value).Field.Field).Distinct().Count() != fields.Count
                    || reads.Select(r => r.Target.Variable).Distinct().Count() != fields.Count) continue;
                var consumer = statements[i + fields.Count];
                if (consumer is not (ManagedReturn or ManagedAssignment or ManagedCall or ManagedStore)) continue;
                var snapshots = reads.ToDictionary(r => r.Target.Variable, r => ((FieldValue)r.Value).Field);
                bool Rebuilt(ComposedValue composed) => composed.Type.Equals(root.Type) && composed.Leaves.Count == fields.Count
                    && composed.Leaves.All(p => p.Path.Count == 1 && p.Value is LocalValue local
                        && snapshots.TryGetValue(local.Variable, out var copied) && copied.Equals(p.Path[0]))
                    && composed.Leaves.Select(p => p.Path[0].Field).Distinct().Count() == fields.Count;
                if (ManagedValues.Of(consumer).SelectMany(ManagedValues.Walk).OfType<ComposedValue>().Count(Rebuilt) != 1) continue;
                statements.RemoveRange(i, fields.Count + 1);
                if (consumer is ManagedReturn { Value: ComposedValue returned } result && Rebuilt(returned))
                    statements.Insert(i, result with { Value = root });
                else
                {
                    var snapshot = new LocalValue(new Variable(Storage.Temp(next++), 1), root.Type, 0);
                    ManagedValue Replace(ManagedValue value) => value is ComposedValue composed && Rebuilt(composed)
                        ? snapshot : ManagedValues.Map(value, Replace);
                    statements.Insert(i, new ManagedAssignment(first.Address, snapshot, root));
                    statements.Insert(++i, ManagedValues.Map(consumer, Replace));
                }
            }
            // 参数或局部值的完整逐字段写入，折回属性后备字段等存储位置的整体赋值。
            for (var i = 0; i < statements.Count; i++)
            {
                if (statements[i] is not ManagedStore { Target: FieldValue { Accessor: null } target,
                        Value: FieldValue { Accessor: null } sourceField } first
                    || Destination(target.Receiver) is not { Type: DefinitionRef { Definition: { IsValueType: true, IsEnum: false } definition } } destination) continue;
                var source = sourceField.Receiver is AddressValue address ? address.Target : sourceField.Receiver;
                if (source is not (LocalValue or ArgumentValue) || !source.Type.Equals(destination.Type)) continue;
                var fields = definition.Fields.Where(f => !f.IsStatic).ToHashSet();
                var writes = statements.Skip(i).Take(fields.Count).OfType<ManagedStore>().ToArray();
                if (fields.Count == 0 || writes.Length != fields.Count || writes.Any(s =>
                    s.Target is not FieldValue { Accessor: null } t || s.Value is not FieldValue { Accessor: null } v
                    || !t.Receiver.Equals(target.Receiver) || !v.Receiver.Equals(sourceField.Receiver) || !t.Field.Equals(v.Field))
                    || !writes.Select(s => ((FieldValue)s.Target).Field.Field).ToHashSet().SetEquals(fields)) continue;
                statements.RemoveRange(i, fields.Count);
                statements.Insert(i, destination is LocalValue local ? new ManagedAssignment(first.Address, local, source)
                    : new ManagedStore(first.Address, destination, source));
            }
            for (var i = 0; i < statements.Count; i++)
            {
                if (statements[i] is not ManagedAssignment { Value: FieldValue field } first
                    || Local(field.Receiver) is not { Type: DefinitionRef { Definition: { IsValueType: true, IsEnum: false } definition } } source) continue;
                var fields = definition.Fields.Where(f => !f.IsStatic).ToHashSet();
                var reads = statements.Skip(i).Take(fields.Count).OfType<ManagedAssignment>().ToArray();
                if (fields.Count < 2 || reads.Length != fields.Count || reads.Any(r => r.Value is not FieldValue f || Local(f.Receiver) != source)
                    || !reads.Select(r => ((FieldValue)r.Value).Field.Field).ToHashSet().SetEquals(fields)
                    || reads.Select(r => r.Target.Variable).Distinct().Count() != fields.Count) continue;
                var snapshots = reads.ToDictionary(r => r.Target.Variable, r => (FieldValue)r.Value);
                var destinations = new Dictionary<ManagedValue, HashSet<FieldDef>>();
                var initialized = new HashSet<LocalValue>();
                var consumed = new Dictionary<Cpp2CS.Ir.Variable, int>();
                var end = i + reads.Length;
                while (end < statements.Count)
                {
                    if (statements[end] is ManagedStore { Target: IndirectValue { Address: AddressValue { Target: LocalValue zero } }, Value: ComposedValue { Leaves.Count: 0 } }
                        && zero.Type.Equals(source.Type) && zero != source && !destinations.ContainsKey(zero)) initialized.Add(zero);
                    else if (statements[end] is ManagedStore { Target: FieldValue target, Value: LocalValue value }
                        && Destination(target.Receiver) is { } destination && destination != source && destination.Type.Equals(source.Type)
                        && snapshots.TryGetValue(value.Variable, out var read) && target.Field.Equals(read.Field))
                    {
                        if (!destinations.TryGetValue(destination, out var copied)) destinations[destination] = copied = [];
                        if (!copied.Add(target.Field.Field)) break;
                        consumed[value.Variable] = consumed.GetValueOrDefault(value.Variable) + 1;
                    }
                    else break;
                    end++;
                }
                // 同一快照可写入多个临时结构体；每个目标都须完整覆盖，字段快照不得流出复制区。
                if (destinations.Count == 0 || initialized.Any(d => !destinations.ContainsKey(d)) || destinations.Values.Any(f => !f.SetEquals(fields))
                    || snapshots.Keys.Any(v => consumed.GetValueOrDefault(v) != uses.GetValueOrDefault(v))) continue;
                statements.RemoveRange(i, end - i);
                statements.InsertRange(i, destinations.Keys.Select(d => d is LocalValue local
                    ? (ManagedStatement)new ManagedAssignment(first.Address, local, source) : new ManagedStore(first.Address, d, source)));
                i += destinations.Count - 1;
            }
            for (var i = 0; i < statements.Count; i++)
            {
                if (statements[i] is not ManagedAssignment { Value: FieldValue { Accessor: null } field } first
                    || Local(field.Receiver) is not { Type: DefinitionRef { Definition: { IsValueType: true, IsEnum: false } definition } } source) continue;
                var fields = definition.Fields.Where(f => !f.IsStatic).ToHashSet();
                var reads = statements.Skip(i).Take(fields.Count).OfType<ManagedAssignment>().ToArray();
                if (fields.Count < 2 || reads.Length != fields.Count || reads.Any(r => r.Value is not FieldValue { Accessor: null } f
                    || Local(f.Receiver) != source || !fields.Contains(f.Field.Field) || uses.GetValueOrDefault(r.Target.Variable) != 1)
                    || reads.Select(r => ((FieldValue)r.Value).Field.Field).Distinct().Count() != fields.Count
                    || reads.Select(r => r.Target.Variable).Distinct().Count() != fields.Count) continue;
                var snapshots = reads.ToDictionary(r => r.Target.Variable, r => (FieldValue)r.Value);
                var copied = new HashSet<FieldDef>();
                var cleared = new HashSet<FieldDef>();
                LocalValue? destination = null;
                var end = i + reads.Length;
                ulong clearAddress = 0;
                while (end < statements.Count && statements[end] is ManagedStore { Target: FieldValue { Accessor: null } target } store)
                {
                    var root = Local(target.Receiver);
                    if (root == source && fields.Contains(target.Field.Field) && store.Value is ConstantValue { Bits: 0 })
                    { cleared.Add(target.Field.Field); clearAddress = store.Address; }
                    else if (root is not null && root != source && root.Type.Equals(source.Type)
                        && (destination is null || root == destination) && store.Value is LocalValue value
                        && snapshots.TryGetValue(value.Variable, out var read) && target.Field.Equals(read.Field)
                        && copied.Add(target.Field.Field)) destination = root;
                    else break;
                    end++;
                }
                if (destination is null || !copied.SetEquals(fields) || cleared.Count != 0 && !cleared.SetEquals(fields)) continue;
                statements.RemoveRange(i, end - i);
                statements.Insert(i, new ManagedAssignment(first.Address, destination, source));
                if (cleared.Count != 0)
                {
                    statements.Insert(i + 1, new ManagedStore(clearAddress, new IndirectValue(new AddressValue(source), source.Type), new ComposedValue(source.Type, [])));
                    i++;
                }
            }
            // 连续清空局部结构体的全部直属字段，包含子结构体的 default，等价于一次 initobj。
            for (var i = 0; i < statements.Count; i++)
            {
                static FieldValue? Storage(ManagedValue value) => value switch
                {
                    FieldValue { Accessor: null } field => field,
                    IndirectValue { Address: AddressValue { Target: FieldValue { Accessor: null } field } } indirect when indirect.Type.Equals(field.Type) => field,
                    _ => null,
                };
                if (statements[i] is not ManagedStore first || Storage(first.Target) is not { } firstField
                    || Local(firstField.Receiver) is not { Type: DefinitionRef { Definition: { IsValueType: true, IsEnum: false } definition } } local
                    || (definition.Attributes & System.Reflection.TypeAttributes.LayoutMask) == System.Reflection.TypeAttributes.ExplicitLayout) continue;
                var fields = definition.Fields.Where(f => !f.IsStatic).ToHashSet();
                var writes = statements.Skip(i).Take(fields.Count).OfType<ManagedStore>().ToArray();
                static bool Zero(ManagedValue value, TypeRef type) => value is ComposedValue { Leaves.Count: 0 } composed && composed.Type.Equals(type)
                    || value is ConstantValue { Bits: 0 } && (ManagedTypes.IsReferenceType(type)
                        || ManagedTypes.PrimitiveName(type) is not null || type is DefinitionRef { Definition.IsEnum: true });
                if (fields.Count == 0 || writes.Length != fields.Count
                    || writes.Any(s => Storage(s.Target) is not { } target || Local(target.Receiver) != local || !Zero(s.Value, target.Type))
                    || !writes.Select(s => Storage(s.Target)!.Field.Field).ToHashSet().SetEquals(fields)) continue;
                statements.RemoveRange(i, fields.Count);
                statements.Insert(i, new ManagedStore(first.Address, new IndirectValue(new AddressValue(local), local.Type), new ComposedValue(local.Type, [])));
            }
            // 引用对象内的结构体字段被完整覆盖时，生成整值写入，供属性 setter 认回。
            for (var i = 0; i < statements.Count; i++)
            {
                if (statements[i] is not ManagedStore { Target: FieldValue { Accessor: null } target } first
                    || Destination(target.Receiver) is not FieldValue { Type: DefinitionRef type } destination
                    || !ManagedTypes.IsReferenceType(destination.Receiver.Type)
                    || LeafPaths(type) is not { Count: > 0 } paths || paths.Any(p => p.Count != 1)) continue;
                var writes = statements.Skip(i).Take(paths.Count).OfType<ManagedStore>().ToArray();
                if (writes.Length != paths.Count || writes.Any(s => s.Target is not FieldValue { Accessor: null } field
                    || !field.Receiver.Equals(target.Receiver) || !Snapshot(s.Value))
                    || !SamePaths(paths, writes.Select(s => (IReadOnlyList<FieldRef>)new[] { ((FieldValue)s.Target).Field }))) continue;
                var leaves = writes.Select(s => ((IReadOnlyList<FieldRef>)new[] { ((FieldValue)s.Target).Field }, s.Value)).ToArray();
                statements.RemoveRange(i, writes.Length);
                statements.Insert(i, new ManagedStore(first.Address, destination, new ComposedValue(type, leaves)));
            }
            // 连续读取值类型局部中某个结构体的全部直属字段，保留一次整值快照，供 getter 认回。
            for (var i = 0; i < statements.Count; i++)
            {
                if (statements[i] is not ManagedAssignment { Value: FieldValue firstField } first
                    || (firstField.Receiver is AddressValue address ? address.Target : firstField.Receiver) is not FieldValue root
                    || root.Type is not DefinitionRef { Definition: { IsValueType: true, IsEnum: false, Keyword: null } } type
                    || (root.Receiver is AddressValue ownerAddress ? ownerAddress.Target : root.Receiver) is not { Type: DefinitionRef { Definition.IsValueType: true } } owner
                    || owner is not (LocalValue or ArgumentValue)
                    || (type.Definition.Attributes & System.Reflection.TypeAttributes.LayoutMask) == System.Reflection.TypeAttributes.ExplicitLayout) continue;
                var fields = type.Definition.Fields.Where(f => !f.IsStatic).ToHashSet();
                var reads = statements.Skip(i).Take(fields.Count).OfType<ManagedAssignment>().ToArray();
                if (fields.Count < 2 || reads.Length != fields.Count
                    || owner is LocalValue ownerLocal && reads.Any(r => r.Target.Variable == ownerLocal.Variable)
                    || reads.Any(r => r.Value is not FieldValue f || !f.Receiver.Equals(firstField.Receiver)
                        || f.Accessor is { } accessor && (accessor.Write || !accessor.Field.Equals(f.Field)))
                    || !reads.Select(r => ((FieldValue)r.Value).Field.Field).ToHashSet().SetEquals(fields)
                    || statements.ElementAtOrDefault(i + fields.Count) is ManagedStore) continue;
                var snapshot = new LocalValue(new Variable(Storage.Temp(next++), 1), type, 0);
                for (var j = 0; j < reads.Length; j++)
                {
                    var field = (FieldValue)reads[j].Value;
                    statements[i + j] = reads[j] with { Value = field with { Receiver = field.Receiver is AddressValue ? new AddressValue(snapshot) : snapshot } };
                }
                statements.Insert(i, new ManagedAssignment(first.Address, snapshot, root));
                i += reads.Length;
            }
            return block with { Statements = statements };
        }).ToArray() };
    }

    private static bool Snapshot(ManagedValue value) => value switch
    {
        LocalValue or ArgumentValue or ConstantValue => true,
        FieldValue { Accessor: null } field when (field.Receiver is AddressValue address ? address.Target : field.Receiver) is var receiver
            && receiver.Type is DefinitionRef { Definition.IsValueType: true } => Snapshot(receiver),
        ConversionValue conversion => Snapshot(conversion.Operand),
        _ => false,
    };

    private static bool Stable(ManagedValue value) => value switch
    {
        LocalValue or ArgumentValue or ConstantValue => true,
        AddressValue address => Stable(address.Target),
        FieldValue { Accessor: null } field => Stable(field.Receiver),
        ArrayElementValue element => Stable(element.Array) && Stable(element.Index),
        ConversionValue conversion => Stable(conversion.Operand),
        BinaryValue { Op: not (Cpp2CS.Ir.BinOp.SDiv or Cpp2CS.Ir.BinOp.UDiv or Cpp2CS.Ir.BinOp.SRem or Cpp2CS.Ir.BinOp.URem) } binary
            => Stable(binary.Left) && Stable(binary.Right),
        _ => false,
    };

    private static (ManagedValue Root, IReadOnlyList<FieldRef> Path)? FieldPath(ManagedValue value, bool write = false)
    {
        var path = new List<FieldRef>();
        // 叶子访问器已证明是原字段的等值读写；中间结构体仍须保留真实存储位置。
        while (value is FieldValue field && (field.Accessor is null || path.Count == 0
            && field.Accessor is { } accessor && accessor.Write == write && accessor.Field.Equals(field.Field)
            && accessor.ValueType.Equals(field.Type) && accessor.Width == field.Width))
        {
            var receiver = field.Receiver is AddressValue address ? address.Target : field.Receiver;
            if (receiver.Type is not DefinitionRef { Definition.IsValueType: true }) break;
            path.Insert(0, field.Field);
            value = receiver;
        }
        return path.Count > 0 && Stable(value) ? (value, path) : null;
    }

    private static List<IReadOnlyList<FieldRef>>? LeafPaths(DefinitionRef type, int depth = 0)
    {
        if (depth > 16 || !type.Definition.IsValueType || type.Definition.IsEnum
            || (type.Definition.Attributes & System.Reflection.TypeAttributes.LayoutMask) == System.Reflection.TypeAttributes.ExplicitLayout) return null;
        var paths = new List<IReadOnlyList<FieldRef>>();
        foreach (var field in type.Definition.Fields.Where(f => !f.IsStatic))
        {
            var reference = new FieldRef(field, type);
            var fieldType = field.Type.Substitute(type.Arguments, []);
            if (fieldType is DefinitionRef { Definition: { IsValueType: true, IsEnum: false, Keyword: null or "decimal" } } nested)
            {
                if (LeafPaths(nested, depth + 1) is not { Count: > 0 } children) return null;
                paths.AddRange(children.Select(p => (IReadOnlyList<FieldRef>)new[] { reference }.Concat(p).ToArray()));
            }
            else paths.Add([reference]);
        }
        return paths;
    }

    private static bool SamePaths(IEnumerable<IReadOnlyList<FieldRef>> expected, IEnumerable<IReadOnlyList<FieldRef>> actual)
    {
        var remaining = actual.ToList();
        foreach (var path in expected)
        {
            var index = remaining.FindIndex(p => p.SequenceEqual(path));
            if (index < 0) return false;
            remaining.RemoveAt(index);
        }
        return remaining.Count == 0;
    }
}
