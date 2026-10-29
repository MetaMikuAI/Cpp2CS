using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceValueConstructorCheck
{
    [Command("source-value-constructor", "完整值类型构造的字段、参数和常量绑定", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var integer = new PrimitiveRef("int");
        var definition = new TypeDef { Index = 0, Assembly = "Test", Namespace = "Test", Name = "Record", Token = 0,
            Attributes = TypeAttributes.SequentialLayout, IsValueType = true, IsEnum = false };
        var type = new DefinitionRef(definition, []);
        definition.Fields = Enumerable.Range(0, 3).Select(i => new FieldDef { Index = i, Owner = definition, Name = "Part" + i,
            Type = integer, Attributes = FieldAttributes.Private, Offset = i * 4 }).ToArray();
        var method = new MethodRef(new MethodDef { Index = 0, Owner = definition, Name = ".ctor", Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = MethodImplAttributes.IL, Slot = -1,
            Parameters = [new("first", integer, 0, null, false), new("second", integer, 0, null, false)] }, [], []);
        var receiver = new ArgumentValue(-1, new ByRefRef(type), 64);
        FieldRef Field(int i) => new(definition.Fields[i], type);
        ManagedStore Store(int i, ManagedValue value) => new(0, new FieldValue(receiver, Field(i), integer, 32), value);
        var first = new LocalValue(new(Storage.Temp(0), 1), integer, 32);
        var second = new LocalValue(new(Storage.Temp(1), 1), integer, 32);
        var constant = new ConstantValue(7, integer, 32);
        ManagedStore[] stores = [Store(0, new ArgumentValue(1, integer, 32)), Store(1, constant), Store(2, new ArgumentValue(0, integer, 32))];
        var pattern = SourceValueConstructor.Create(method, stores);
        a.True(pattern is not null, "完整字段写入形成构造证据");
        ComposedValue Value(ManagedValue middle) => new(type, [([Field(2)], first), ([Field(0)], second), ([Field(1)], middle)]);
        a.True(pattern!.Build(Value(constant)) is { Arguments: [var actualFirst, var actualSecond], Transparent: true }
            && actualFirst == first && actualSecond == second, "按真实参数映射绑定，字段顺序可不同");
        a.True(pattern.Build(Value(new ConstantValue(8, integer, 32))) is null, "固定字段必须与构造常量相同");
        a.True(pattern.Build(new(type, Value(constant).Leaves.Take(2).ToArray())) is null, "缺少字段不能补值");
        a.True(SourceValueConstructor.Create(method, stores.Take(2).ToArray()) is null, "构造证据必须覆盖全部字段");
        a.True(SourceValueConstructor.Create(method, [stores[0], stores[0], stores[2]]) is null, "重复字段不能冒充完整覆盖");
        a.True(SourceValueConstructor.Create(method, [Store(0, new ArgumentValue(-1, integer, 32)), stores[1], stores[2]]) is null,
            "不能把接收者作为调用参数");
        a.True(SourceValueConstructor.Create(method, [Store(0, new BinaryValue(BinOp.Add, first, constant, integer, 32)), stores[1], stores[2]]) is null,
            "不反求包含计算的初始化");
        var unused = SourceValueConstructor.Create(method, [Store(0, new ArgumentValue(0, integer, 32)), stores[1], stores[2]]);
        a.True(unused!.Build(new(type, [([Field(0)], first), ([Field(1)], constant), ([Field(2)], first)])) is null,
            "未使用的构造参数不能凭空补齐");
        a.True(pattern.Build(new(type, [([Field(0)], second), ([Field(1)], constant), ([Field(2)], new FieldValue(receiver, Field(0), integer, 32))])) is null,
            "可变内存读取不能因参数次序而移动");
        a.True(pattern.Expand([first, second]) is { Leaves: var expanded } && expanded[0].Value == second
            && expanded[1].Value == constant && expanded[2].Value == first, "构造按已证实字段映射展开");
        a.True(pattern.Expand([first]) is null, "构造参数必须齐全");
        var destination = new LocalValue(new(Storage.Temp(10), 1), type, 0);
        var localField = new FieldValue(new AddressValue(destination), Field(0), integer, 32);
        a.True(pattern.Build(new(type, [([Field(0)], second), ([Field(1)], constant), ([Field(2)], localField)])) is not null,
            "值类型局部的纯字段读取可作为构造参数");
        a.True(pattern.Build(new(type, [([Field(0)], second), ([Field(1)], constant),
            ([Field(2)], new BinaryValue(BinOp.SDiv, first, second, integer, 32))])) is null, "可能抛错的整数除法不重排");
        foreach (var mode in new[] { "valid", "missing", "duplicate", "other-target", "self-read", "interrupted" })
        {
            var writes = Value(constant).Leaves.Select(p => (ManagedStatement)new ManagedStore(1,
                new FieldValue(new AddressValue(destination), p.Path[0], integer, 32), p.Value)).ToList();
            if (mode == "missing") writes.RemoveAt(1);
            if (mode == "duplicate") writes[1] = writes[0];
            if (mode == "other-target") writes[1] = ((ManagedStore)writes[1]) with { Target = new FieldValue(receiver, Field(0), integer, 32) };
            if (mode == "self-read") writes[1] = ((ManagedStore)writes[1]) with { Value = new FieldValue(new AddressValue(destination), Field(0), integer, 32) };
            if (mode == "interrupted") writes.Insert(1, new ManagedCall(2, new(method, null, [], false), null, false));
            writes.Add(new ManagedReturn(3, destination));
            var body = new ManagedBody(method, [new(0, writes)]);
            var result = SourceConstructorWrites.Rewrite(body, _ => [pattern], (_, _) => { });
            a.Equal(mode == "valid" ? 1 : 0, result.Blocks[0].Statements.OfType<ManagedAssignment>()
                .Count(s => s.Value is NewObjectValue), "连续构造写入 " + mode);
        }
        var outerDefinition = new TypeDef { Index = 1, Assembly = "Test", Namespace = "Test", Name = "Outer", Token = 0,
            Attributes = TypeAttributes.SequentialLayout, IsValueType = true, IsEnum = false };
        var outerType = new DefinitionRef(outerDefinition, []);
        var outerField = new FieldDef { Index = 3, Owner = outerDefinition, Name = "Data", Type = type, Attributes = FieldAttributes.Private, Offset = 0 };
        outerDefinition.Fields = [outerField];
        var outerMethod = new MethodRef(new MethodDef { Index = 1, Owner = outerDefinition, Name = ".ctor", Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1, Parameters = [new("data", type, 0, null, false)] }, [], []);
        var member = new FieldRef(outerField, outerType);
        var outerPattern = SourceValueConstructor.Create(outerMethod, [new(0,
            new FieldValue(new ArgumentValue(-1, new ByRefRef(outerType), 64), member, type, 0), new ArgumentValue(0, type, 0))])!;
        var outerLocal = new LocalValue(new(Storage.Temp(11), 1), outerType, 0);
        var nestedTarget = new FieldValue(new AddressValue(outerLocal), member, type, 0);
        var nestedWrites = Value(constant).Leaves.Select(p => (ManagedStatement)new ManagedStore(0,
            new FieldValue(new AddressValue(nestedTarget), p.Path[0], integer, 32), p.Value)).ToArray();
        var nestedBody = new ManagedBody(method, [new(0, [.. nestedWrites, new ManagedReturn(1, outerLocal)])]);
        var nestedOutput = SourceConstructorWrites.Rewrite(nestedBody, t => t == type ? [pattern] : t == outerType ? [outerPattern] : [], (_, _) => { });
        a.True(nestedOutput.Blocks[0].Statements is [ManagedAssignment { Value: NewObjectValue { Arguments: [NewObjectValue] } }, ManagedReturn],
            "交错叶子写入从内到外按已证明构造还原");
        return a.Finish("source-value-constructor");
    }
}
