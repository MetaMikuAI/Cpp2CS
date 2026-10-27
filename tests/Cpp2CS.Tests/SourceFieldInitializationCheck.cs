using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceFieldInitializationCheck
{
    [Command("source-field-initialization", "结构体完整初始化与中途观察边界", Gate = Gate.Unit)]
    public static int Run()
    {
        TypeDef Definition(int index, string name) => new() { Index = index, Assembly = "Tests", Namespace = "Tests", Name = name,
            Token = 0, Attributes = TypeAttributes.SequentialLayout, IsValueType = true, IsEnum = false };
        var number = new PrimitiveRef("int"); var text = new PrimitiveRef("string");
        var part = Definition(1, "Part"); var partType = new DefinitionRef(part, []);
        var owner = Definition(2, "Record"); var type = new DefinitionRef(owner, []);
        FieldDef Field(int index, TypeDef declaring, string name, TypeRef fieldType) => new() { Index = index, Owner = declaring,
            Name = name, Type = fieldType, Offset = index * 4, Attributes = FieldAttributes.Private };
        part.Fields = [Field(0, part, "X", number), Field(1, part, "Y", number)];
        owner.Fields = [Field(2, owner, "A", number), Field(3, owner, "B", partType), Field(4, owner, "C", text)];
        var local = new LocalValue(new(Storage.Temp(1), 1), type, 0);
        FieldValue At(ManagedValue receiver, FieldDef field) => new(new AddressValue(receiver), new(field, receiver.Type), field.Type, field.Type == number ? 32 : 64);
        var alpha = At(local, owner.Fields[0]); var nested = At(local, owner.Fields[1]);
        var x = At(nested, part.Fields[0]); var y = At(nested, part.Fields[1]);
        var setter = new MethodRef(new MethodDef { Index = 1, Owner = owner, Name = "SetText", Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1 }, [], []);
        ManagedStore Store(FieldValue field, ulong bits) => new(0, field, new ConstantValue(bits, number, 32));
        ManagedCall SetText(ManagedValue value) => new(0, new(setter, new AddressValue(local), [value], false), null, false);
        var a = new Assertions();
        foreach (var mode in new[] { "complete", "incomplete", "unknown-call", "observer", "late-zero", "self-read" })
        {
            var items = new List<ManagedStatement> { Store(alpha, 0), Store(x, 0), SetText(new ConstantValue(0, text, 64)) };
            if (mode == "self-read") items.Insert(1, new ManagedStore(0, x, alpha));
            if (mode == "observer") items.Add(new ManagedCall(0, new(setter, null, [], false), null, false));
            if (mode != "incomplete") items.Add(Store(y, 0));
            items.Add(Store(alpha, 7));
            items.Add(SetText(new StringValue("message", text)));
            if (mode == "late-zero") items.Add(Store(alpha, 0));
            var original = new ManagedBody(setter, [new(0, items)]);
            var rewritten = SourceFieldInitialization.Rewrite(original, m => mode != "unknown-call" && m == setter ? new(owner.Fields[2], type) : null);
            var result = rewritten.Blocks[0].Statements;
            var folds = mode is "complete" or "late-zero";
            a.Equal(folds, result[0] is ManagedStore { Target: IndirectValue, Value: ComposedValue { Leaves.Count: 0 } }, mode);
            if (!folds) continue;
            a.True(result.OfType<ManagedCall>().Single().Invocation.Arguments.Single() is StringValue { Text: "message" }, "只保留实际非零设置");
            a.True(result.OfType<ManagedStore>().Any(s => s.Target == alpha && s.Value is ConstantValue { Bits: 7 }), "保留实际数值设置");
            if (mode == "late-zero") a.True(result.Last() is ManagedStore { Value: ConstantValue { Bits: 0 } }, "后写零不能被移到之前的非零设置前");
        }
        return a.Finish("source-field-initialization");
    }
}
