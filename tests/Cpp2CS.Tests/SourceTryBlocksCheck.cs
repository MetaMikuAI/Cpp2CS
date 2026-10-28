using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceTryBlocksCheck
{
    [Command("source-try-blocks", "保护区局部运算合并及抛出、入口和嵌套边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var owner = new TypeDef { Index = 0, Assembly = "Sample", Namespace = "", Name = "Subject", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var method = new MethodRef(new MethodDef { Index = 0, Owner = owner, Name = "Visit", Token = 0, Attributes = MethodAttributes.Public,
            ImplAttributes = 0, Slot = -1, ReturnType = new PrimitiveRef("Void") }, [], []);
        var integer = new PrimitiveRef("Int32");
        var local = new LocalValue(new(Storage.Temp(1), 1), integer, 32);
        var caught = new LocalValue(new(Storage.Temp(2), 1), new PrimitiveRef("Object"), 64);
        ManagedJump Jump(ulong from, ulong target) => new(from, new(target, []));
        var a = new Assertions();
        foreach (var mode in new[] { "valid", "call", "divide", "external-entry", "entry-prefix", "handler", "nested-try", "nested-handler", "copies" })
        {
            ManagedStatement value = mode == "call" ? new ManagedCall(3, new(method, null, [], false), local, false)
                : new ManagedAssignment(3, local, new BinaryValue(mode == "divide" ? BinOp.SDiv : BinOp.Or,
                    local, new ConstantValue(2, integer, 32), integer, 32));
            var body = new ManagedBody(method, [new(0, [mode == "external-entry"
                ? new ManagedBranch(0, local, new(1, []), new(3, [])) : Jump(0, mode == "entry-prefix" ? 3UL : 1UL)]),
                new(1, [new ManagedCall(1, new(method, null, [], false), local, false), Jump(1, 3)]),
                new(2, [new ManagedRethrow(2)]), new(3, [value, mode == "copies"
                    ? new ManagedJump(3, new(1, [new(local, new ConstantValue(1, integer, 32))])) : Jump(3, 1)]),
                new(4, [new ManagedReturn(4, null)])])
                { Regions = [new([1], 2, mode == "handler" ? [2, 3] : [2], caught, ManagedRegionKind.Catch)] };
            if (mode == "nested-try") body = body with { Regions = [.. body.Regions, new([3], 4, [4], caught, ManagedRegionKind.Catch)] };
            if (mode == "nested-handler") body = body with { Regions = [.. body.Regions, new([4], 3, [3], caught, ManagedRegionKind.Catch)] };
            var result = SourceTryBlocks.Rewrite(body);
            var expected = mode is "valid" or "copies" or "entry-prefix";
            a.Equal(expected, result.Regions[0].Try.Contains(3UL), $"{mode} 的区域边界");
            a.Equal(body.Blocks.Single(b => b.Address == 3), result.Blocks.Single(b => b.Address == 3), "语句和边复制原样保留");
            a.Equal(1, body.Regions[0].Try.Count, "输入区域不变");
            if (expected) a.True(result.Blocks.Select(b => b.Address).SequenceEqual(mode == "entry-prefix"
                ? new ulong[] { 0, 3, 1, 2, 4 } : new ulong[] { 0, 1, 3, 2, 4 }), "合并后保护区连续且保留唯一入口");
        }
        var receiverType = new DefinitionRef(owner, []);
        var receiver = new LocalValue(new(Storage.Temp(3), 1), receiverType, 64);
        var alias = new LocalValue(new(Storage.Temp(4), 1), receiverType, 64);
        var readMethod = new MethodRef(new MethodDef { Index = 1, Owner = owner, Name = "get_Value", Token = 0, Attributes = MethodAttributes.Public,
            ImplAttributes = 0, Slot = -1, ReturnType = integer }, [], []);
        var field = new FieldRef(new FieldDef { Index = 0, Owner = owner, Name = "value", Type = integer, Attributes = FieldAttributes.Public, Offset = 16 }, receiverType);
        foreach (var mode in new[] { "getter", "field", "alias", "unknown", "reset", "addressed", "conditional", "mixed", "virtual", "virtual-reset", "check", "check-reset", "check-ne" })
        {
            var fieldRead = new FieldValue(receiver, field, integer, 32);
            ManagedStatement first = mode.StartsWith("check", StringComparison.Ordinal)
                ? new ManagedCheck(1, new ComparisonValue(mode == "check-ne" ? Cond.Ne : Cond.Eq, receiver,
                    new ConstantValue(0, receiverType, 64), new PrimitiveRef("Boolean")), method)
                : mode is "field" or "conditional"
                ? new ManagedAssignment(1, local, mode == "conditional" ? new ChoiceValue(local, fieldRead, new ConstantValue(0, integer, 32), integer, 32) : fieldRead)
                : new ManagedCall(1, new(mode is "unknown" or "virtual" or "virtual-reset" ? method : readMethod, receiver, [], mode.StartsWith("virtual")), local, false);
            var middle = new List<ManagedStatement> { first };
            if (mode is "reset" or "virtual-reset" or "check-reset") middle.Add(new ManagedAssignment(1, receiver, new ConstantValue(0, receiverType, 64)));
            if (mode == "alias") middle.Add(new ManagedAssignment(1, alias, receiver));
            middle.Add(Jump(1, 3));
            var second = new ManagedCall(3, new(readMethod, mode == "alias" ? alias : receiver, [], false), local, false);
            var start = new List<ManagedStatement> { new ManagedAssignment(0, receiver, new ArgumentValue(0, receiverType, 64)) };
            if (mode == "addressed") start.Add(new ManagedCall(0, new(method, null, [new AddressValue(receiver)], false), null, false));
            start.Add(mode == "mixed" ? new ManagedBranch(0, local, new(1, []), new(4, [])) : Jump(0, 1));
            var body = new ManagedBody(method, [new(0, start), new(1, middle), new(2, [new ManagedRethrow(2)]),
                new(3, [second, new ManagedReturn(3, null)]), new(4, [Jump(4, 3)])])
                { Regions = [new([1], 2, [2], caught, ManagedRegionKind.Catch)] };
            if (mode != "mixed") body = body with { Blocks = body.Blocks.Where(b => b.Address != 4).ToArray() };
            var expected = mode is "getter" or "field" or "alias" or "virtual" or "check";
            var facts = SourceNonNullReceivers.Read(body, m => m.Equals(readMethod));
            a.Equal(expected, facts[second].Contains(second.Invocation.Receiver!), $"{mode} 的接收者非空证据");
            a.Equal(expected, SourceTryBlocks.Rewrite(body, m => m.Equals(readMethod)).Regions[0].Try.Contains(3UL), $"{mode} 的纯 getter 区域合并");
            if (mode == "check-ne") a.True(SourceNonNullReceivers.ReadNull(body)[second].Contains(receiver), "反向检查通过后为空，不误证非空");
        }
        foreach (var mode in new[] { "field", "comparison", "copy", "getter", "unknown-getter", "unchecked", "reset", "addressed", "nested", "static" })
        {
            var start = new List<ManagedStatement> { new ManagedAssignment(0, receiver, new ArgumentValue(0, receiverType, 64)) };
            if (mode == "addressed") start.Add(new ManagedCall(0, new(method, null, [new AddressValue(receiver)], false), null, false));
            start.Add(Jump(0, 1));
            var middle = new List<ManagedStatement>();
            if (mode != "unchecked") middle.Add(new ManagedCheck(1, new ComparisonValue(Cond.Eq, receiver,
                new ConstantValue(0, receiverType, 64), new PrimitiveRef("Boolean")), method));
            if (mode == "reset") middle.Add(new ManagedAssignment(1, receiver, new ConstantValue(0, receiverType, 64)));
            middle.Add(Jump(1, 3));
            var fieldRead = new FieldValue(receiver, field, integer, 32);
            ManagedValue read = mode switch
            {
                "getter" or "unknown-getter" => fieldRead with { Accessor = new(mode == "getter" ? readMethod : method, field, integer, 32, false) },
                "nested" => fieldRead with { Receiver = new FieldValue(receiver, field, receiverType, 64) },
                "static" => new StaticFieldValue(field, integer, 32),
                _ => fieldRead,
            };
            ManagedStatement second = mode == "comparison"
                ? new ManagedBranch(3, new ComparisonValue(Cond.Eq, read, local, new PrimitiveRef("Boolean")), new(1, []), new(4, []))
                : mode == "copy" ? new ManagedJump(3, new(1, [new(local, read)])) : new ManagedAssignment(3, local, read);
            var body = new ManagedBody(method, [new(0, start), new(1, middle), new(2, [new ManagedRethrow(2)]),
                new(3, mode is "comparison" or "copy" ? [second] : [second, Jump(3, 1)]), new(4, [new ManagedReturn(4, null)])])
                { Regions = [new([1], 2, [2], caught, ManagedRegionKind.Catch)] };
            var result = SourceTryBlocks.Rewrite(body, mode is "getter" or "unknown-getter" ? m => m.Equals(readMethod) : null);
            a.Equal(mode is "field" or "comparison" or "copy" or "getter", result.Regions[0].Try.Contains(3UL), $"{mode} 的非空字段读取合并");
            a.Equal(body.Blocks.Single(b => b.Address == 3), result.Blocks.Single(b => b.Address == 3), "字段读取不提前、不复制、不修改");
        }
        var record = new TypeDef { Index = 2, Assembly = "Sample", Namespace = "", Name = "Record", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false };
        var recordType = new DefinitionRef(record, []);
        var recordRead = new MethodRef(new MethodDef { Index = 2, Owner = record, Name = "get_Part", Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1, ReturnType = integer }, [], []);
        var stored = new LocalValue(new(Storage.Temp(5), 1), recordType, 0);
        var component = new FieldRef(new FieldDef { Index = 1, Owner = record, Name = "part", Type = integer,
            Attributes = FieldAttributes.Public, Offset = 16 }, recordType);
        var embedded = new FieldRef(new FieldDef { Index = 2, Owner = owner, Name = "record", Type = recordType,
            Attributes = FieldAttributes.Public, Offset = 24 }, receiverType);
        foreach (var mode in new[] { "value", "address", "getter", "embedded", "unchecked", "unknown-getter", "ref", "array" })
        {
            ManagedValue target = mode switch
            {
                "embedded" or "unchecked" => new FieldValue(receiver, embedded, recordType, 0),
                "ref" => new ArgumentValue(1, new ByRefRef(recordType), 64),
                "array" => new ArrayElementValue(new ArgumentValue(1, new ArrayRef(recordType, 1), 64), local, recordType, 0),
                _ => stored,
            };
            ManagedValue location = mode is "value" or "ref" ? target : new AddressValue(target);
            ManagedStatement read = mode is "value" or "address" ? new ManagedAssignment(3, local, new FieldValue(location, component, integer, 32))
                : new ManagedCall(3, new(recordRead, location, [], false), local, false);
            var prefix = new List<ManagedStatement>();
            if (mode == "embedded") prefix.Add(new ManagedCheck(1, new ComparisonValue(Cond.Eq, receiver,
                new ConstantValue(0, receiverType, 64), new PrimitiveRef("Boolean")), method));
            prefix.Add(Jump(1, 3));
            var body = new ManagedBody(method, [new(0, [Jump(0, 1)]), new(1, prefix), new(2, [new ManagedRethrow(2)]),
                new(3, [read, Jump(3, 1)])]) { Regions = [new([1], 2, [2], caught, ManagedRegionKind.Catch)] };
            var result = SourceTryBlocks.Rewrite(body, candidate => mode != "unknown-getter" && candidate.Equals(recordRead));
            a.Equal(mode is "value" or "address" or "getter" or "embedded", result.Regions[0].Try.Contains(3UL), "值类型接收者 " + mode);
            a.Equal(body.Blocks[3], result.Blocks.Single(b => b.Address == 3), "值类型读取与调用保留原顺序");
        }
        var boolean = new DefinitionRef(new TypeDef { Index = 8, Assembly = "mscorlib.dll", Namespace = "System", Name = "Boolean",
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false }, []);
        var flagField = new FieldRef(new FieldDef { Index = 8, Owner = owner, Name = "flag", Type = boolean,
            Attributes = FieldAttributes.Public, Offset = 32 }, receiverType);
        var enumeration = new TypeDef { Index = 10, Assembly = "Sample", Namespace = "", Name = "State", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = true };
        var int32 = new DefinitionRef(new TypeDef { Index = 11, Assembly = "mscorlib.dll", Namespace = "System", Name = "Int32",
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false }, []);
        enumeration.Fields = [new FieldDef { Index = 10, Owner = enumeration, Name = "value__", Type = int32,
            Attributes = FieldAttributes.Public, Offset = 0 }];
        foreach (var mode in new[] { "checked", "this", "enum", "unchecked", "reset", "addressed", "accessor", "static", "array", "reference", "throwing-value" })
        {
            var prefix = new List<ManagedStatement>();
            if (mode is not ("unchecked" or "this")) prefix.Add(new ManagedCheck(1, new ComparisonValue(Cond.Eq, receiver,
                new ConstantValue(0, receiverType, 64), new PrimitiveRef("Boolean")), method));
            if (mode == "reset") prefix.Add(new ManagedAssignment(1, receiver, new ConstantValue(0, receiverType, 64)));
            if (mode == "addressed") prefix.Add(new ManagedCall(1, new(method, null, [new AddressValue(receiver)], false), null, false));
            prefix.Add(Jump(1, 3));
            var target = new FieldValue(receiver, flagField, boolean, 8);
            ManagedValue storedAt = mode switch
            {
                "accessor" => target with { Accessor = new(method, flagField, boolean, 8, true) },
                "static" => new StaticFieldValue(flagField, boolean, 8),
                "array" => new ArrayElementValue(new ArgumentValue(0, new ArrayRef(boolean, 1), 64), local, boolean, 8),
                "this" => target with { Receiver = new ArgumentValue(-1, receiverType, 64) },
                "enum" => new FieldValue(receiver, new(new FieldDef { Index = 12, Owner = owner, Name = "state", Type = new DefinitionRef(enumeration, []),
                    Attributes = FieldAttributes.Public, Offset = 36 }, receiverType), new DefinitionRef(enumeration, []), 32),
                "reference" => new FieldValue(receiver, new(new FieldDef { Index = 9, Owner = owner, Name = "link", Type = receiverType,
                    Attributes = FieldAttributes.Public, Offset = 40 }, receiverType), receiverType, 64),
                _ => target,
            };
            var store = new ManagedStore(3, storedAt, mode == "throwing-value"
                ? new FieldValue(alias, flagField, boolean, 8) : new ConstantValue(1, storedAt.Type, 8));
            var body = new ManagedBody(method, [new(0, [Jump(0, 1)]), new(1, prefix), new(2, [new ManagedRethrow(2)]),
                new(3, [store, Jump(3, 1)])]) { Regions = [new([1], 2, [2], caught, ManagedRegionKind.Catch)] };
            var result = SourceTryBlocks.Rewrite(body);
            a.Equal(mode is "checked" or "this" or "enum", result.Regions[0].Try.Contains(3UL), "基础值字段写入 " + mode);
            a.Equal(body.Blocks[3], result.Blocks.Single(b => b.Address == 3), "写入内容与顺序不变");
        }
        return a.Finish("source-try-blocks");
    }
}
