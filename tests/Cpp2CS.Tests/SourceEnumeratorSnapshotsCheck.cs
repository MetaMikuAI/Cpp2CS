using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceEnumeratorSnapshotsCheck
{
    [Command("source-enumerator-snapshots", "原生元素快照与枚举器修改边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var number = new PrimitiveRef("int");
        TypeDef Definition(int index, string name) => new() { Index = index, Assembly = "Tests", Namespace = "Tests", Name = name,
            Token = 0, Attributes = TypeAttributes.SequentialLayout, IsValueType = true, IsEnum = false };
        var item = Definition(1, "Item"); var itemType = new DefinitionRef(item, []);
        var owner = Definition(2, "Cursor"); var type = new DefinitionRef(owner, []);
        FieldDef Field(int index, TypeDef declaring, string name, TypeRef fieldType) => new() { Index = index, Owner = declaring,
            Name = name, Type = fieldType, Offset = index * 4, Attributes = FieldAttributes.Private };
        item.Fields = [Field(0, item, "X", number), Field(1, item, "Y", number)];
        owner.Fields = [Field(2, owner, "Item", itemType)];
        var method = new MethodRef(new MethodDef { Index = 3, Owner = owner, Name = "Observe", Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1 }, [], []);
        LocalValue Local(int index, TypeRef t, int width) => new(new(Storage.Temp(index), 1), t, width);
        var cursor = Local(1, type, 0); var x = Local(2, number, 32); var y = Local(3, number, 32);
        var snapshot = Local(4, itemType, 0);
        var storage = new FieldValue(new AddressValue(cursor), new(owner.Fields[0], type), itemType, 0);
        FieldValue Leaf(ManagedValue root, int index) => new(new AddressValue(root), new(item.Fields[index], itemType), number, 32);
        foreach (var mode in new[] { "same-block", "straight", "with-accessor", "missing-proof", "unknown-accessor", "call", "store", "receiver-write", "escape", "shared", "branch", "branch-copy", "branch-shared", "branch-accessor", "edge-copy", "region", "handler" })
        {
            var current = mode == "with-accessor" ? storage with { Accessor = new FieldAccessor(method, storage.Field, itemType, 0, false) } : storage;
            var first = new ManagedAssignment(1, x, Leaf(current, 0));
            var second = new ManagedAssignment(3, y, Leaf(current, 1));
            if (mode == "unknown-accessor") second = second with { Value = ((FieldValue)second.Value) with
                { Accessor = new FieldAccessor(method, new(item.Fields[1], itemType), number, 32, false) } };
            var statements = new List<ManagedStatement> { first };
            if (mode == "call") statements.Add(new ManagedCall(2, new(method, new AddressValue(cursor), [], false), null, false));
            if (mode == "store") statements.Add(new ManagedStore(2, Leaf(storage, 1), new ConstantValue(9, number, 32)));
            if (mode == "receiver-write") statements.Add(new ManagedAssignment(2, cursor, cursor));
            if (mode == "escape") statements.Add(new ManagedAssignment(2, Local(5, new ByRefRef(type), 64), new AddressValue(cursor)));
            var blocks = new List<ManagedBlock>();
            if (mode == "same-block") { statements.Add(second); statements.Add(new ManagedReturn(4, y)); blocks.Add(new(0, statements)); }
            else
            {
                ManagedValue condition = mode == "branch-accessor" ? new ComparisonValue(Cond.Ne,
                    Leaf(new ArgumentValue(0, itemType, 0), 0) with { Accessor = new FieldAccessor(method, new(item.Fields[0], itemType), number, 32, false) },
                    new ConstantValue(0, number, 32), new PrimitiveRef("Boolean"))
                    : new ComparisonValue(Cond.Ne, x, new ConstantValue(0, number, 32), new PrimitiveRef("Boolean"));
                statements.Add(mode.StartsWith("branch", StringComparison.Ordinal) ? new ManagedBranch(2, condition,
                    new(16, mode == "branch-copy" ? [new(x, y)] : []), new(32, []))
                    : new ManagedJump(2, new(16, mode == "edge-copy" ? [new(x, y)] : [])));
                blocks.Add(new(0, statements)); blocks.Add(new(16, [second, new ManagedReturn(17, y)]));
            }
            if (mode == "shared") blocks.Add(new(32, [new ManagedJump(32, new(16, []))]));
            if (mode.StartsWith("branch", StringComparison.Ordinal)) blocks.Add(new(32, mode == "branch-shared"
                ? [new ManagedJump(32, new(16, []))] : [new ManagedReturn(32, x)]));
            var input = new ManagedBody(method, blocks);
            if (mode == "region") input = input with { Regions = [new([16], 32, [32], null, ManagedRegionKind.Catch)] };
            if (mode == "handler") input = input with { Regions = [new([], 16, [16], null, ManagedRegionKind.Catch)] };
            var output = SourceEnumeratorSnapshots.Rewrite(input, f => mode != "missing-proof" && f.Field.Equals(storage.Field),
                f => f.Accessor is not { Write: true } && f.Field.Equals(storage.Field), _ => snapshot);
            var folds = mode is "same-block" or "straight" or "with-accessor" or "branch";
            a.Equal(folds ? 1 : 0, output.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().Count(s => s.Target == snapshot), "快照数量：" + mode);
            a.Equal(folds ? 1 : 2, output.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>()
                .SelectMany(s => ManagedValues.Walk(s.Value)).OfType<FieldValue>().Count(f => f.Field.Equals(storage.Field)), "真实读取次数：" + mode);
            if (!folds) continue;
            a.True(output.Blocks[0].Statements[0] is ManagedAssignment read && read.Target == snapshot && read.Value == current, "快照在首次字段读取处");
            var reads = output.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().Where(s => s.Target == x || s.Target == y).ToArray();
            a.True(reads[0].Value == Leaf(snapshot, 0) && reads[1].Value == Leaf(snapshot, 1), "两个成员来自同一元素副本");
        }
        foreach (var edgeCopy in new[] { false, true })
        {
            var input = new ManagedBody(method, [
                new(0, [new ManagedBranch(1, new ComparisonValue(Cond.Ne, Leaf(storage, 0), x, new PrimitiveRef("Boolean")), new(32, []), new(16, []))]),
                new(16, edgeCopy ? [new ManagedJump(17, new(32, [new(y, Leaf(storage, 1))]))]
                    : [new ManagedAssignment(17, y, Leaf(storage, 1)), new ManagedJump(18, new(32, []))]),
                new(32, [new ManagedReturn(32, y)])]);
            var output = SourceEnumeratorSnapshots.Rewrite(input, f => f.Field == storage.Field, _ => true, _ => snapshot);
            a.True(output.Blocks[0].Statements[0] is ManagedAssignment read && read.Target == snapshot && read.Value == storage,
                "条件中的首次读取建立快照");
            a.Equal(1, output.Blocks.SelectMany(b => b.Statements).SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
                .SelectMany(ManagedValues.Walk).OfType<FieldValue>().Count(f => f.Field == storage.Field), "条件与末端边复制使用同一快照");
        }
        return a.Finish("source-enumerator-snapshots");
    }
}
