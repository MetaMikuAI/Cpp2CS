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
        return a.Finish("source-value-constructor");
    }
}
