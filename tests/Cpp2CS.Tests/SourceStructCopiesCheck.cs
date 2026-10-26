using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceStructCopiesCheck
{
    [Command("source-struct-copies", "结构体快照夹杂清零的值对照", Gate = Gate.Unit)]
    public static int Run()
    {
        var definition = new TypeDef { Index = 0, Assembly = "Sample", Namespace = "Sample", Name = "Record", Token = 0,
            Attributes = TypeAttributes.SequentialLayout, IsValueType = true, IsEnum = false };
        var integer = new PrimitiveRef("I4");
        definition.Fields = Enumerable.Range(0, 3).Select(i => new FieldDef { Index = i, Owner = definition, Name = "Part" + i,
            Type = integer, Attributes = FieldAttributes.Private | FieldAttributes.InitOnly, Offset = i * 4 }).ToArray();
        var type = new DefinitionRef(definition, []);
        var source = new LocalValue(new(Storage.Temp(-1), 1), type, 0);
        var destination = new LocalValue(new(Storage.Temp(-2), 1), type, 0);
        var snapshots = Enumerable.Range(0, 3).Select(i => new LocalValue(new(Storage.Temp(-3 - i), 1), integer, 32)).ToArray();
        FieldValue Field(LocalValue root, int index) => new(new AddressValue(root), new(definition.Fields[index], type), integer, 32);
        ManagedStore Clear(int index) => new(0, Field(source, index), new ConstantValue(0, integer, 32));
        var statements = snapshots.Select((s, i) => (ManagedStatement)new ManagedAssignment(0, s, Field(source, i))).Concat(new ManagedStatement[]
        {
            Clear(1), Clear(2), new ManagedStore(0, Field(destination, 0), snapshots[0]),
            new ManagedStore(0, Field(destination, 1), snapshots[1]), new ManagedStore(0, Field(destination, 2), snapshots[2]), Clear(0),
        }).ToArray();
        ManagedBody Body(IEnumerable<ManagedStatement> items) => new(null!, [new ManagedBlock(0, items.ToArray())]);
        string Execute(ManagedBody body, int[] input)
        {
            var structs = new Dictionary<Variable, int[]> { [source.Variable] = input.ToArray(), [destination.Variable] = [-1, -1, -1] };
            var scalars = new Dictionary<Variable, int>();
            int Read(ManagedValue value) => value switch
            {
                ConstantValue c => unchecked((int)c.Bits),
                LocalValue local => scalars[local.Variable],
                FieldValue { Receiver: AddressValue { Target: LocalValue root } } field => structs[root.Variable][field.Field.Field.Index],
                _ => throw new NotSupportedException(value.ToString()),
            };
            foreach (var statement in body.Blocks.Single().Statements)
                switch (statement)
                {
                    case ManagedAssignment { Value: LocalValue local } a when local.Type == type: structs[a.Target.Variable] = structs[local.Variable].ToArray(); break;
                    case ManagedAssignment a: scalars[a.Target.Variable] = Read(a.Value); break;
                    case ManagedStore { Target: FieldValue { Receiver: AddressValue { Target: LocalValue root } } field } s:
                        structs[root.Variable][field.Field.Field.Index] = Read(s.Value); break;
                    case ManagedStore { Target: IndirectValue { Address: AddressValue { Target: LocalValue root } }, Value: ComposedValue { Leaves.Count: 0 } }:
                        structs[root.Variable] = new int[3]; break;
                    default: throw new NotSupportedException(statement.ToString());
                }
            return string.Join(',', structs[destination.Variable]) + ";" + string.Join(',', structs[source.Variable]);
        }
        var original = Body(statements);
        var rewritten = SourceStructCopies.Rewrite(original);
        var a = new Assertions();
        a.Equal(2, rewritten.Blocks.Single().Statements.Count, "实际替换为整值复制和清零");
        foreach (var values in new[] { new[] { 0, 0, 0 }, new[] { 7, -3, 991 }, new[] { int.MinValue, int.MaxValue, -1 } })
            a.Equal(Execute(original, values), Execute(rewritten, values), "保留快照值，清零来源，不能复制清零后的值");
        var interrupted = Body(statements.Take(4).Append(new ManagedCall(0, new(null!, null, [], false), null, false)).Concat(statements.Skip(4)));
        a.True(SourceStructCopies.Rewrite(interrupted).Blocks.Single().Statements.SequenceEqual(interrupted.Blocks.Single().Statements), "不能跨过可观察调用");
        var partial = Body(statements.SkipLast(1));
        a.True(SourceStructCopies.Rewrite(partial).Blocks.Single().Statements.SequenceEqual(partial.Blocks.Single().Statements), "部分清零不能扩大为 default");
        var copy = Body(statements.Where(s => s is not ManagedStore { Value: ConstantValue }));
        var copied = SourceStructCopies.Rewrite(copy);
        a.Equal(1, copied.Blocks.Single().Statements.Count, "完整字段复制还原为值赋值，保留来源");
        foreach (var values in new[] { new[] { 0, 0, 0 }, new[] { 7, -3, 991 }, new[] { int.MinValue, int.MaxValue, -1 } })
            a.Equal(Execute(copy, values), Execute(copied, values), "没有清零时不能修改来源");
        var incomplete = Body(copy.Blocks.Single().Statements.SkipLast(1));
        a.True(SourceStructCopies.Rewrite(incomplete).Blocks.Single().Statements.SequenceEqual(incomplete.Blocks.Single().Statements), "部分复制不能扩大成整值赋值");
        var leaves = Enumerable.Range(0, 3).Select(i => ((IReadOnlyList<FieldRef>)new[] { new FieldRef(definition.Fields[i], type) }, (ManagedValue)Field(source, i))).ToArray();
        a.Equal<ManagedValue?>(source, SourceStructCopies.WholeValue(new(type, leaves)), "全字段原样重组保留整体值");
        a.True(SourceStructCopies.WholeValue(new(type, leaves.Take(2).ToArray())) is null, "遗漏字段不能整体复制");
        a.True(SourceStructCopies.WholeValue(new(type, leaves.Take(2).Append((leaves[2].Item1, Field(destination, 2))).ToArray())) is null, "混合来源不能整体复制");
        a.True(SourceStructCopies.WholeValue(new(type, leaves.Take(2).Append((leaves[2].Item1, new ConstantValue(0, integer, 32))).ToArray())) is null, "重置字段不能整体复制");
        var direct = Body(Enumerable.Range(0, 3).Select(i => new ManagedStore(0, Field(destination, i), Field(source, i))));
        a.True(SourceStructCopies.Rewrite(direct).Blocks.Single().Statements is [ManagedAssignment { Value: var directSource }] && directSource == source,
            "完整逐字段写入还原整体赋值");
        var returnedLeaves = Enumerable.Range(0, 3).Select(i => ((IReadOnlyList<FieldRef>)new[] { new FieldRef(definition.Fields[i], type) }, (ManagedValue)snapshots[i])).ToArray();
        var returned = Body(statements.Take(3).Append(new ManagedReturn(0, new ComposedValue(type, returnedLeaves))));
        a.True(SourceStructCopies.Rewrite(returned).Blocks.Single().Statements is [ManagedReturn { Value: var returnedSource }] && returnedSource == source,
            "完整快照立即返回时保留整体值");
        var mixedReturn = Body(statements.Take(3).Append(new ManagedReturn(0, new ComposedValue(type,
            returnedLeaves.Take(2).Append((returnedLeaves[2].Item1, new ConstantValue(0, integer, 32))).ToArray()))));
        a.True(SourceStructCopies.Rewrite(mixedReturn).Blocks.Single().Statements.Count == 4, "返回中更改叶子时不能折为整值");
        return a.Finish("source-struct-copies");
    }
}
