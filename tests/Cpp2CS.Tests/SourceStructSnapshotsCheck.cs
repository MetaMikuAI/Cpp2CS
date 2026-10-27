using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceStructSnapshotsCheck
{
    [Command("source-struct-snapshots", "完整嵌套结构体快照、跨调用复制与观察边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var integer = new PrimitiveRef("int");
        TypeDef Definition(int index, string name, bool value) => new() { Index = index, Assembly = "Tests", Namespace = "Tests",
            Name = name, Token = 0, Attributes = TypeAttributes.Public | TypeAttributes.SequentialLayout, IsValueType = value, IsEnum = false };
        var child = Definition(1, "Child", true); var record = Definition(2, "Record", true); var holder = Definition(3, "Holder", false);
        var childType = new DefinitionRef(child, []); var type = new DefinitionRef(record, []); var holderType = new DefinitionRef(holder, []);
        FieldDef Field(int index, TypeDef owner, TypeRef fieldType) => new() { Index = index, Owner = owner, Name = "Part" + index,
            Type = fieldType, Attributes = owner.IsValueType ? FieldAttributes.Private | FieldAttributes.InitOnly : FieldAttributes.Public, Offset = index * 4 };
        child.Fields = [Field(0, child, integer), Field(1, child, integer)];
        record.Fields = [Field(2, record, integer), Field(3, record, childType)];
        holder.Fields = [Field(4, holder, type)];
        var array = new ArgumentValue(0, new ArrayRef(type, 1), 64);
        var receiver = new ArgumentValue(1, holderType, 64);
        var element = new ArrayElementValue(array, new ConstantValue(0, integer, 32), type, 0);
        var destination = new FieldValue(receiver, new(holder.Fields[0], holderType), type, 0);
        ManagedValue Leaf(ManagedValue root, int index)
        {
            if (index == 0) return new FieldValue(new AddressValue(root), new(record.Fields[0], type), integer, 32);
            var inner = new FieldValue(new AddressValue(root), new(record.Fields[1], type), childType, 0);
            return new FieldValue(new AddressValue(inner), new(child.Fields[index - 1], childType), integer, 32);
        }
        var locals = Enumerable.Range(0, 3).Select(i => new LocalValue(new(Storage.Temp(i), 1), integer, 32)).ToArray();
        var effect = new ManagedCall(8, new(null!, null, [], false), null, false);
        foreach (var mode in new[] { "valid", "missing-read", "duplicate-read", "other-array-index", "interrupted-read", "escaped", "redefined",
            "missing-write", "duplicate-write", "changed-value", "interrupted-write" })
        {
            var reads = locals.Select((l, i) => (ManagedStatement)new ManagedAssignment((ulong)i, l, Leaf(element, i))).ToList();
            if (mode == "missing-read") reads.RemoveAt(1);
            if (mode == "duplicate-read") reads[1] = ((ManagedAssignment)reads[1]) with { Value = Leaf(element, 0) };
            if (mode == "other-array-index") reads[1] = ((ManagedAssignment)reads[1]) with { Value = Leaf(element with { Index = new ConstantValue(1, integer, 32) }, 1) };
            if (mode == "interrupted-read") reads.Insert(1, effect);
            if (mode == "escaped") reads.Add(effect with { Invocation = effect.Invocation with { Arguments = [new AddressValue(locals[1])] } });
            if (mode == "redefined") reads.Add(new ManagedAssignment(7, locals[1], new ConstantValue(9, integer, 32)));
            reads.Add(effect);
            reads.Add(new ManagedJump(9, new(16, [])));
            var writes = locals.Select((l, i) => (ManagedStatement)new ManagedStore((ulong)(16 + i), Leaf(destination, i), l)).ToList();
            if (mode == "missing-write") writes.RemoveAt(1);
            if (mode == "duplicate-write") writes[1] = writes[0];
            if (mode == "changed-value") writes[1] = ((ManagedStore)writes[1]) with { Value = new ConstantValue(9, integer, 32) };
            if (mode == "interrupted-write") writes.Insert(1, effect);
            writes.Add(new ManagedReturn(20, null));
            var body = new ManagedBody(null!, [new(0, reads), new(16, writes)]);
            var result = SourceStructCopies.SnapshotReads(body);
            var snapshot = mode is "valid" or "missing-write" or "duplicate-write" or "changed-value" or "interrupted-write";
            a.Equal(snapshot ? 1 : 0, result.Blocks[0].Statements.OfType<ManagedAssignment>().Count(s => s.Value == element), "整体快照 " + mode);
            a.Equal(mode == "valid" ? 1 : 0, result.Blocks[1].Statements.OfType<ManagedStore>().Count(s => s.Target == destination), "整体写入 " + mode);
            if (mode != "valid") continue;
            a.True(result.Blocks[0].Statements is [ManagedAssignment, ManagedCall, ManagedJump], "快照仍在原观察调用之前");
            foreach (var values in new[] { new[] { 3, -2, 19 }, new[] { int.MinValue, 0, int.MaxValue } })
                a.Equal(Execute(body, values), Execute(result, values), "源数组被中途调用改写后，目标仍保留原快照");
        }
        return a.Finish("source-struct-snapshots");

        string Execute(ManagedBody body, int[] values)
        {
            Dictionary<FieldDef, object> Record(int[] parts) => new() { [record.Fields[0]] = parts[0],
                [record.Fields[1]] = new Dictionary<FieldDef, object> { [child.Fields[0]] = parts[1], [child.Fields[1]] = parts[2] } };
            var items = new[] { Record(values) };
            var target = new Dictionary<FieldDef, object> { [holder.Fields[0]] = Record([0, 0, 0]) };
            var variables = new Dictionary<Variable, object>();
            object Copy(object value) => value is Dictionary<FieldDef, object> fields
                ? fields.ToDictionary(p => p.Key, p => p.Key.Type is DefinitionRef { Definition.IsValueType: true } ? Copy(p.Value) : p.Value) : value;
            object Read(ManagedValue value) => value switch
            {
                ArgumentValue { Index: 0 } => items, ArgumentValue { Index: 1 } => target,
                ConstantValue c => unchecked((int)c.Bits), LocalValue l => variables[l.Variable], AddressValue p => Read(p.Target),
                ArrayElementValue e => ((Dictionary<FieldDef, object>[])Read(e.Array))[(int)Read(e.Index)],
                FieldValue f => ((Dictionary<FieldDef, object>)Read(f.Receiver))[f.Field.Field],
                _ => throw new NotSupportedException(value.ToString()),
            };
            foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
                switch (statement)
                {
                    case ManagedAssignment s: variables[s.Target.Variable] = Copy(Read(s.Value)); break;
                    case ManagedStore { Target: FieldValue f } s:
                        ((Dictionary<FieldDef, object>)Read(f.Receiver))[f.Field.Field] = Copy(Read(s.Value)); break;
                    case ManagedCall: items[0] = Record([101, 102, 103]); break;
                    case ManagedJump or ManagedReturn: break;
                    default: throw new NotSupportedException(statement.ToString());
                }
            return string.Join(',', Enumerable.Range(0, 3).Select(i => Read(Leaf(destination, i))));
        }
    }
}
