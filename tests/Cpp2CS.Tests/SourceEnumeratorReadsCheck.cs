using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceEnumeratorReadsCheck
{
    [Command("source-enumerator-reads", "原生枚举元素读取的直线路径与副作用边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var number = new PrimitiveRef("int");
        var owner = new TypeDef { Index = 1, Assembly = "Tests", Namespace = "Tests", Name = "Cursor", Token = 0,
            Attributes = TypeAttributes.SequentialLayout, IsValueType = true, IsEnum = false };
        var type = new DefinitionRef(owner, []);
        var field = new FieldDef { Index = 2, Owner = owner, Name = "Item", Type = number, Offset = 0, Attributes = FieldAttributes.Private };
        var method = new MethodRef(new MethodDef { Index = 3, Owner = owner, Name = "Observe", Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1 }, [], []);
        LocalValue Local(int index, TypeRef localType, int width) => new(new(Storage.Temp(index), 1), localType, width);
        var cursor = Local(1, type, 0); var result = Local(2, number, 32); var saved = Local(3, number, 32);
        var storage = new FieldValue(new AddressValue(cursor), new(field, type), number, 32);
        foreach (var mode in new[] { "same-block", "straight", "with-accessor", "missing-proof", "call", "store", "read-result", "assign-receiver", "assign-result", "shared", "edge-copy", "region", "handler", "handler-observe" })
        {
            var prefix = new ManagedAssignment(1, saved, new ConstantValue(7, number, 32));
            var read = new ManagedAssignment(3, result, mode == "with-accessor" ? storage with
                { Accessor = new FieldAccessor(method, storage.Field, number, 32, false) } : storage);
            var statements = new List<ManagedStatement> { prefix };
            if (mode == "call") statements.Insert(0, new ManagedCall(0, new(method, new AddressValue(cursor), [], false), null, false));
            if (mode == "store") statements.Insert(0, new ManagedStore(0, storage, new ConstantValue(9, number, 32)));
            if (mode == "read-result") statements[0] = new ManagedAssignment(1, saved, result);
            if (mode == "assign-receiver") statements[0] = new ManagedAssignment(1, cursor, cursor);
            if (mode == "assign-result") statements[0] = new ManagedAssignment(1, result, new ConstantValue(7, number, 32));
            var blocks = new List<ManagedBlock>();
            if (mode == "same-block") { statements.Add(read); statements.Add(new ManagedReturn(4, result)); blocks.Add(new(0, statements)); }
            else
            {
                statements.Add(new ManagedJump(2, new(8, mode == "edge-copy" ? [new(saved, result)] : [])));
                blocks.Add(new(0, statements));
                blocks.Add(new(8, [new ManagedJump(8, new(16, []))]));
                blocks.Add(new(16, [read, new ManagedReturn(17, result)]));
            }
            if (mode == "shared") blocks.Add(new(24, [new ManagedJump(24, new(8, []))]));
            var input = new ManagedBody(method, blocks);
            if (mode == "region") input = input with { Regions = [new([8, 16], 32, [32], null, ManagedRegionKind.Catch)] };
            if (mode == "handler") input = input with { Regions = [new([], 8, [8, 16], null, ManagedRegionKind.Catch)] };
            if (mode == "handler-observe")
            {
                blocks.Add(new(32, [new ManagedReturn(32, result)]));
                input = input with { Regions = [new([0, 8, 16], 32, [32], null, ManagedRegionKind.Catch)] };
            }
            var output = SourceEnumeratorReads.Rewrite(input, f => mode != "missing-proof" && f.Field.Equals(storage.Field));
            var first = output.Blocks[0].Statements;
            a.Equal(mode is "same-block" or "straight" or "with-accessor", first[0] == read, "只有无阻碍直线路径可到块首：" + mode);
            a.Equal(1, output.Blocks.SelectMany(b => b.Statements).Count(s => s == read), "保留一次实际读取：" + mode);
            if (mode is "call" or "store")
                a.True(first[0] == statements[0] && first[1] == read && first[2] == prefix, "读移动到副作用之后，之前的副作用保持先执行");
            if (mode is "same-block" or "straight")
                a.True(first[1] == prefix, "其他读取仍保留结果");
        }
        return a.Finish("source-enumerator-reads");
    }
}
