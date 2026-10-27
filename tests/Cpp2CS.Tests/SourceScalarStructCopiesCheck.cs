using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceScalarStructCopiesCheck
{
    [Command("source-scalar-struct-copies", "单字段结构体的分支复制与数值使用边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var integer = new DefinitionRef(new TypeDef { Index = 1, Assembly = "Sample", Namespace = "System", Name = "UInt64", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false }, []);
        var definition = new TypeDef { Index = 2, Assembly = "Sample", Namespace = "Sample", Name = "Value", Token = 0,
            Attributes = TypeAttributes.Public | TypeAttributes.SequentialLayout, IsValueType = true, IsEnum = false };
        definition.Fields = [new FieldDef { Index = 2, Owner = definition, Name = "bits", Type = integer, Offset = 16, Attributes = FieldAttributes.Private | FieldAttributes.InitOnly }];
        var type = new DefinitionRef(definition, []);
        var field = new FieldRef(definition.Fields[0], type);
        var source = new ArgumentValue(0, type, 0);
        var temporary = new LocalValue(new(Storage.Gpr(1), 1), integer, 64);
        var selected = new LocalValue(new(Storage.Gpr(2), 1), integer, 64);
        ManagedValue Read() => new FieldValue(new AddressValue(source), field, integer, 64);
        ManagedValue Rebuild() => new ComposedValue(type, [([field], selected)]);
        ManagedBody Body(ulong alternate = 0, bool arithmetic = false, bool escape = false, bool takeAddress = false)
        {
            var statements = new List<ManagedStatement> { new ManagedAssignment(0, temporary, Read()),
                new ManagedBranch(4, new ConstantValue(1, integer, 64), new(16, [new(selected, temporary)]),
                    new(16, [new(selected, new ConstantValue(alternate, integer, 64))])) };
            if (escape) statements.Insert(1, new ManagedStore(2, new ArgumentValue(1, integer, 64), temporary));
            if (takeAddress) statements.Insert(1, new ManagedStore(2, new AddressValue(temporary), new ConstantValue(0, integer, 64)));
            var output = arithmetic ? (ManagedValue)new BinaryValue(BinOp.Add, selected, new ConstantValue(1, integer, 64), integer, 64) : Rebuild();
            return new(null!, [new ManagedBlock(0, statements), new ManagedBlock(16, [new ManagedReturn(16, output)])]);
        }
        var a = new Assertions();
        var converted = SourceScalarStructCopies.Rewrite(Body());
        a.True(converted.Blocks[0].Statements[0] is ManagedAssignment { Target.Type: var target, Value: var value }
            && target.Equals(type) && value == source, "首个读取直接保留结构体快照");
        var branch = (ManagedBranch)converted.Blocks[0].Statements[^1];
        a.True(branch.Taken.Copies[0].Target.Type.Equals(type) && branch.Taken.Copies[0].Value.Type.Equals(type), "分支复制两端同步恢复结构体类型");
        a.True(branch.Fallthrough.Copies[0].Value is ComposedValue { Leaves.Count: 0 }, "零种子还原为 default");
        a.True(converted.Blocks[1].Statements[0] is ManagedReturn { Value: LocalValue local } && local.Type.Equals(type), "重组直接返回结构体局部");
        foreach (var invalid in new[] { Body(alternate: 1), Body(arithmetic: true), Body(escape: true), Body(takeAddress: true) })
            a.True(ReferenceEquals(invalid, SourceScalarStructCopies.Rewrite(invalid)), "存在非复制用途时保留原类型");
        return a.Finish("source-scalar-struct-copies");
    }
}
