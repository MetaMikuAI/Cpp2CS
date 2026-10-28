using System.Reflection;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceListCallsCheck
{
    [Command("source-list-calls", "List 添加的旧长度与异常状态边界", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var list = types.CorlibDefinition("System.Collections.Generic.List")!;
        var owner = new DefinitionRef(list, [types.Object]);
        var subject = new TypeDef { Index = -1, Assembly = "Tests.dll", Namespace = "Tests", Name = "Subject", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var method = new MethodRef(new MethodDef { Index = -1, Owner = subject, Name = "Append", Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1 }, [], []);
        var receiver = new ArgumentValue(0, owner, 64);
        var item = new ArgumentValue(1, types.Object, 64);
        LocalValue Local(int id, TypeRef type, int width) => new(new(Storage.Temp(id), 1), type, width);
        var count = Local(0, types.Int32, 32); var array = Local(1, new ArrayRef(types.Object, 1), 64);
        var state = Local(2, types.Object, 64);
        var other = new ArgumentValue(2, new DefinitionRef(subject, []), 64);
        var otherField = new FieldValue(other, new(new FieldDef { Index = -1, Owner = subject, Name = "Count",
            Type = types.Int32, Attributes = FieldAttributes.Public, Offset = 16 }, other.Type), types.Int32, 32);
        FieldValue Field(string name) => new(receiver, new(list.Fields.Single(f => f.Name == name), owner),
            name == "_items" ? array.Type : types.Int32, name == "_items" ? 64 : 32);
        ManagedValue Increment(ManagedValue value) => new BinaryValue(BinOp.Add, value, new ConstantValue(1, types.Int32, 32), types.Int32, 32);
        ManagedAssignment State(ulong address, ulong bits = 0) => new(address, state, new ConstantValue(bits, types.Object, 64));
        var resize = new MethodRef(list.Methods.Single(m => m.Name == "AddWithResize"), owner.Arguments, []);
        var a = new Assertions();
        foreach (var mode in new[] { "valid", "mutated-count", "changed-state", "late-state", "different-handler" })
        {
            var prefix = new List<ManagedStatement> { new ManagedAssignment(0, count, Field("_size")),
                new ManagedStore(1, otherField, count) };
            if (mode == "mutated-count") prefix.Add(new ManagedStore(2, Field("_size"), new ConstantValue(0, types.Int32, 32)));
            prefix.Add(new ManagedAssignment(3, array, Field("_items")));
            prefix.Add(new ManagedStore(4, Field("_version"), Increment(Field("_version"))));
            if (mode != "late-state") prefix.Add(State(5));
            prefix.Add(new ManagedBranch(6, new ComparisonValue(Cond.Ult, count, new ArrayLengthValue(array, types.Int32, 32), types.Boolean), new(16, []), new(32, [])));
            var original = new ManagedBody(method, [new(0, prefix), new(16, [
                new ManagedStore(16, Field("_size"), Increment(count)), new ManagedStore(17, new ArrayElementValue(array, count, types.Object, 64), item),
                State(18), new ManagedJump(19, new(48, []))]), new(32, [State(32, mode == "changed-state" ? 1UL : 0UL),
                new ManagedCall(33, new(resize, receiver, [item], false), null, false), new ManagedJump(34, new(48, []))]),
                new(48, [new ManagedReturn(48, null)]), new(64, [new ManagedReturn(64, state)])])
            { Regions = [new(mode == "different-handler" ? [0, 16] : [0, 16, 32], 64, [64], null, ManagedRegionKind.Catch)] };
            var rewritten = SourceListCalls.Rewrite(original, types, (_, _) => { });
            var calls = rewritten.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Where(c => c.Invocation.Method.Method.Name == "Add").ToArray();
            a.Equal(mode == "valid" ? 1 : 0, calls.Length, mode);
            if (mode != "valid") continue;
            var statements = rewritten.Blocks[0].Statements;
            a.True(statements.OfType<ManagedAssignment>().Any(s => s.Target == count) && statements.Contains(prefix[1]), "旧长度及其他对象的写入保留");
            a.True(statements.TakeWhile(s => s != calls[0]).OfType<ManagedAssignment>().Any(s => s.Target == state), "异常状态先于添加调用写入");
            a.True(rewritten.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().Count(s => s.Target == state) == 2,
                "保留正常路径状态拷贝，未执行的慢分支被删除");
        }
        CheckStructItems(a, types, list, method);
        CheckFastRegions(a, types, list, method);
        return a.Finish("source-list-calls");
    }

    private static void CheckFastRegions(Assertions a, ManagedTypes types, TypeDef list, MethodRef method)
    {
        foreach (var mode in new[] { "inside", "outside", "reference", "slow-outside", "handler", "new-try", "call", "wrong-index" })
        {
            var type = mode == "reference" ? types.Object : types.Int32;
            var owner = new DefinitionRef(list, [type]);
            var receiver = new ArgumentValue(0, owner, 64);
            var item = new ArgumentValue(1, type, mode == "reference" ? 64 : 32);
            var array = new LocalValue(new(Storage.Temp(30), 1), new ArrayRef(type, 1), 64);
            var count = new LocalValue(new(Storage.Temp(31), 1), types.Int32, 32);
            FieldValue Field(string name) => new(receiver, new(list.Fields.Single(f => f.Name == name), owner),
                name == "_items" ? array.Type : types.Int32, name == "_items" ? 64 : 32);
            ManagedValue Increment(ManagedValue value) => new BinaryValue(BinOp.Add, value, new ConstantValue(1, types.Int32, 32), types.Int32, 32);
            var resize = new MethodRef(list.Methods.Single(m => m.Name == "AddWithResize"), owner.Arguments, []);
            var fast = new List<ManagedStatement> { new ManagedStore(16, Field("_size"), Increment(count)),
                new ManagedStore(17, new ArrayElementValue(array, mode == "wrong-index" ? Increment(count) : count, type, item.Width), item) };
            if (mode == "call") fast.Add(new ManagedCall(18, new(method, null, [], false), null, false));
            fast.Add(new ManagedJump(19, new(48, [])));
            var original = new ManagedBody(method, [new(0, [new ManagedAssignment(0, array, Field("_items")),
                new ManagedStore(1, Field("_version"), Increment(Field("_version"))), new ManagedAssignment(2, count, Field("_size")),
                new ManagedBranch(3, new ComparisonValue(Cond.Ult, count, new ArrayLengthValue(array, types.Int32, 32), types.Boolean), new(16, []), new(32, []))]),
                new(16, fast), new(32, [new ManagedCall(32, new(resize, receiver, [item], false), null, false), new ManagedJump(33, new(48, []))]),
                new(48, [new ManagedReturn(48, null)]), new(64, [new ManagedReturn(64, null)])])
            { Regions = [new(mode == "inside" ? [0, 16, 32] : mode == "slow-outside" ? [0, 16] : mode == "new-try" ? [16] : [0, 32],
                64, mode == "handler" ? [16, 64] : [64], null, ManagedRegionKind.Catch)] };
            var rewritten = SourceListCalls.Rewrite(original, types, (_, _) => { });
            a.Equal(mode is "inside" or "outside" ? 1 : 0, rewritten.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>()
                .Count(c => c.Invocation.Method.Method.Name == "Add"), "快速路径保护区 " + mode);
        }
    }

    private static void CheckStructItems(Assertions a, ManagedTypes types, TypeDef list, MethodRef method)
    {
        foreach (var mode in new[] { "complete", "missing", "duplicate", "slow-duplicate", "other-index", "other-value", "interrupted", "explicit-layout",
            "constructor", "constructor-no-proof", "constructor-other-value", "constructor-result" })
        {
            var nested = new TypeDef { Index = -10, Assembly = "Tests.dll", Namespace = "Tests", Name = "Part", Token = 0,
                Attributes = TypeAttributes.Public | TypeAttributes.SequentialLayout, IsValueType = true, IsEnum = false };
            var nestedType = new DefinitionRef(nested, []);
            nested.Fields = [new() { Index = -11, Owner = nested, Name = "Value", Type = types.Int32, Attributes = FieldAttributes.Private, Offset = 16 }];
            var ctor = new MethodRef(new() { Index = -12, Owner = nested, Name = ".ctor", Token = 0,
                Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1,
                Parameters = [new("value", types.Int32, 0, null, false)] }, [], []);
            var proof = SourceValueConstructor.Create(ctor, [new(0,
                new FieldValue(new ArgumentValue(-1, new ByRefRef(nestedType), 64), new(nested.Fields[0], nestedType), types.Int32, 32),
                new ArgumentValue(0, types.Int32, 32))]);
            var constructed = mode.StartsWith("constructor", StringComparison.Ordinal);
            var record = new TypeDef { Index = -2, Assembly = "Tests.dll", Namespace = "Tests", Name = "Item", Token = 0,
                Attributes = TypeAttributes.Public | (mode == "explicit-layout" ? TypeAttributes.ExplicitLayout : TypeAttributes.SequentialLayout),
                IsValueType = true, IsEnum = false };
            record.Fields = Enumerable.Range(0, 2).Select(i => new FieldDef { Index = -3 - i, Owner = record,
                Name = "Part" + i, Type = constructed && i == 1 ? nestedType : types.Int32,
                Attributes = FieldAttributes.Public, Offset = 16 + 4 * i }).ToArray();
            var type = new DefinitionRef(record, []);
            var owner = new DefinitionRef(list, [type]);
            var receiver = new ArgumentValue(0, owner, 64);
            var array = new LocalValue(new(Storage.Temp(20), 1), new ArrayRef(type, 1), 64);
            var count = new LocalValue(new(Storage.Temp(21), 1), types.Int32, 32);
            FieldValue ListField(string name) => new(receiver, new(list.Fields.Single(f => f.Name == name), owner),
                name == "_items" ? array.Type : types.Int32, name == "_items" ? 64 : 32);
            ManagedValue Number(ulong value) => new ConstantValue(value, types.Int32, 32);
            ManagedValue Increment(ManagedValue value) => new BinaryValue(BinOp.Add, value, Number(1), types.Int32, 32);
            var element = new ArrayElementValue(array, count, type, 0);
            FieldValue Field(int index, ArrayElementValue target) => new(new AddressValue(target), new(record.Fields[index], type), record.Fields[index].Type, 32);
            var fast = new List<ManagedStatement> { new ManagedStore(16, ListField("_size"), Increment(count)),
                new ManagedStore(17, Field(0, element), Number(4)) };
            if (mode == "interrupted") fast.Add(new ManagedCall(18, new(method, null, [], false), null, false));
            if (constructed) fast.Add(new ManagedCall(19, new(ctor, new AddressValue(Field(1, element)), [Number(5)], false),
                mode == "constructor-result" ? count : null, false));
            else if (mode != "missing") fast.Add(new ManagedStore(19, Field(mode == "duplicate" ? 0 : 1,
                mode == "other-index" ? element with { Index = Number(0) } : element), Number(5)));
            fast.Add(new ManagedReturn(20, null));
            var value = new ComposedValue(type, record.Fields.Select((field, i) =>
                ((IReadOnlyList<FieldRef>)new[] { new FieldRef(mode == "slow-duplicate" ? record.Fields[0] : field, type) },
                    constructed && i == 1 ? new NewObjectValue(ctor, [Number(mode == "constructor-other-value" ? 6UL : 5UL)])
                        : Number(mode == "slow-duplicate" ? 4 : (ulong)(4 + i + (mode == "other-value" ? 1 : 0))))).ToArray());
            var resize = new MethodRef(list.Methods.Single(m => m.Name == "AddWithResize"), owner.Arguments, []);
            var original = new ManagedBody(method, [new(0, [new ManagedAssignment(0, array, ListField("_items")),
                new ManagedStore(1, ListField("_version"), Increment(ListField("_version"))),
                new ManagedAssignment(2, count, ListField("_size")),
                new ManagedBranch(3, new ComparisonValue(Cond.Ult, count, new ArrayLengthValue(array, types.Int32, 32), types.Boolean), new(16, []), new(32, []))]),
                new(16, fast), new(32, [new ManagedCall(32, new(resize, receiver, [value], false), null, false), new ManagedReturn(33, null)])]);
            var rewritten = SourceListCalls.Rewrite(original, types, (_, _) => { },
                candidate => mode != "constructor-no-proof" && candidate.Equals(ctor) ? proof : null);
            a.Equal(mode is "complete" or "constructor" ? 1 : 0, rewritten.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>()
                .Count(c => c.Invocation.Method.Method.Name == "Add"), "结构体元素 " + mode);
        }
    }
}
