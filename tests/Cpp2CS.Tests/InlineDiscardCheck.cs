using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class InlineDiscardCheck
{
    [Command("inline-discard", "内联包装丢弃返回值及逃逸边界", Gate = Gate.Unit)]
    public static int Run()
    {
        TypeDef Type(int index, string name, bool value = false) => new() { Index = index, Assembly = "Inline.Tests.dll", Namespace = value ? "System" : "Sample", Name = name,
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = value, IsEnum = false };
        var owner = Type(1, "Owner");
        var ownerType = new DefinitionRef(owner, []);
        var worker = Type(2, "Worker");
        var workerType = new DefinitionRef(worker, []);
        var boolean = new DefinitionRef(Type(3, "Boolean", true), []);
        var field = new FieldRef(new FieldDef { Index = 1, Owner = owner, Name = "worker", Type = workerType, Offset = 16,
            Attributes = FieldAttributes.Private }, ownerType);
        MethodRef Method(int index, TypeDef type, string name, TypeRef returned) => new(new MethodDef { Index = index, Owner = type, Name = name,
            Token = 0, Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1, ReturnType = returned }, [], []);
        var operation = Method(1, worker, "Run", boolean);
        var wrapper = Method(2, owner, "Forward", new PrimitiveRef("void"));
        var receiver = new ArgumentValue(-1, ownerType, 64);
        var loaded = new LocalValue(new(Storage.Gpr(1), 1), workerType, 64);
        var result = new LocalValue(new(Storage.Gpr(0), 2), boolean, 8);
        var pattern = new ManagedBody(wrapper, [new ManagedBlock(0, [new ManagedAssignment(0, loaded, new FieldValue(receiver, field, workerType, 64)),
            new ManagedCall(4, new(operation, loaded, [], false), null, false), new ManagedReturn(8, null)])]);
        ManagedBody Caller(bool escaped = false, bool extraCall = false)
        {
            var statements = new List<ManagedStatement> { new ManagedAssignment(100, loaded, new FieldValue(receiver, field, workerType, 64)),
                new ManagedCall(104, new(operation, loaded, [], false), result, false) };
            if (extraCall) statements.Add(new ManagedCall(108, new(operation, loaded, [], false), null, false));
            statements.Add(new ManagedJump(112, new(200, [])));
            return new(Method(3, owner, "Caller", escaped ? boolean : new PrimitiveRef("void")),
                [new ManagedBlock(100, statements), new ManagedBlock(200, [new ManagedReturn(200, escaped ? result : null)])]);
        }
        ManagedBody Rewrite(ManagedBody body) => InlineRecognition.Rewrite(body, [new(wrapper, pattern, false)], boolean, v => v is FieldValue);
        var a = new Assertions();
        var rewritten = Rewrite(Caller());
        a.True(rewritten.Blocks[0].Statements is [ManagedCall { Inlined: true, Result: null } call, ManagedJump]
            && call.Invocation.Method == wrapper, "未使用的内部结果允许认回 void 包装");
        foreach (var rejected in new[] { Caller(escaped: true), Caller(extraCall: true) })
            a.True(ReferenceEquals(rejected, Rewrite(rejected)), "结果逃逸或额外可观察调用时保持原体");

        var unsigned = new DefinitionRef(Type(4, "UInt64", true), []);
        var argument = new ArgumentValue(0, boolean, 8);
        var forwarded = new LocalValue(new(Storage.Gpr(20), 1), unsigned, 64);
        ManagedValue Widen(ManagedValue value) => new ConversionValue(ConvKind.ZeroExtend, value, unsigned, 64);
        ManagedValue Narrow(ManagedValue value) => new ConversionValue(ConvKind.Truncate, value, boolean, 8);
        ManagedValue Masked(ManagedValue value, ulong mask) => new BinaryValue(BinOp.And, Widen(value), new ConstantValue(mask, unsigned, 64), unsigned, 64);
        wrapper.Method.Parameters = [new("flag", boolean, 0, null, false)];
        operation.Method.Parameters = wrapper.Method.Parameters;
        var booleanPattern = pattern with { Blocks = [pattern.Blocks[0] with { Statements = [pattern.Blocks[0].Statements[0],
            new ManagedCall(4, new(operation, loaded, [Narrow(Masked(argument, 1))], false), null, false), new ManagedReturn(8, null)] }] };
        foreach (var mask in new ulong[] { 1, 2 })
        {
            var booleanCaller = Caller();
            booleanCaller.Method.Method.Parameters = wrapper.Method.Parameters;
            booleanCaller = booleanCaller with { Blocks = [new ManagedBlock(90, [new ManagedAssignment(90, forwarded, Masked(argument, mask)), new ManagedJump(94, new(100, []))]),
                booleanCaller.Blocks[0] with { Statements = [booleanCaller.Blocks[0].Statements[0],
                    new ManagedCall(104, new(operation, loaded, [Narrow(forwarded)], false), result, false), new ManagedJump(112, new(200, []))] }, booleanCaller.Blocks[1]] };
            var actual = InlineRecognition.Rewrite(booleanCaller, [new(wrapper, booleanPattern, false)], boolean, v => v is FieldValue);
            a.Equal(mask == 1, actual.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Any(c => c.Inlined), "只统一来自 bool 参数的恒等位复制");
        }
        var single = new DefinitionRef(Type(5, "Single", true), []);
        var numericField = new FieldRef(new FieldDef { Index = 2, Owner = owner, Name = "number", Type = single, Offset = 24,
            Attributes = FieldAttributes.Private }, ownerType);
        var number = new FieldValue(receiver, numericField, single, 32);
        var secondField = new FieldRef(new FieldDef { Index = 4, Owner = owner, Name = "second", Type = single, Offset = 32,
            Attributes = FieldAttributes.Private }, ownerType);
        var second = new FieldValue(receiver, secondField, single, 32);
        var zero = new ConstantValue(0, single, 32);
        var yes = new ConstantValue(1, boolean, 8);
        var no = new ConstantValue(0, boolean, 8);
        var predicate = Method(4, owner, "IsZero", boolean);
        var predicateBody = new ManagedBody(predicate, [new(0, [new ManagedBranch(0,
            new ComparisonValue(Cond.FEq, number, zero, boolean), new(4, []), new(8, []))]),
            new(4, [new ManagedReturn(4, new ComparisonValue(Cond.FEq, second, zero, boolean))]), new(8, [new ManagedReturn(8, no)])]);
        foreach (var condition in new[] { Cond.FUne, Cond.FNe })
        {
            var body = new ManagedBody(Method(5, owner, "ReadZero", boolean), [new(100, [new ManagedBranch(100,
                new ComparisonValue(condition, number, zero with { Bits = 0x80000000 }, boolean), new(300, []), new(104, []))]),
                new(104, [new ManagedBranch(104, new ComparisonValue(Cond.FUne, second, zero, boolean), new(300, []), new(200, []))]),
                new(200, [new ManagedReturn(200, yes)]), new(300, [new ManagedReturn(300, no)])]);
            var actual = InlineRecognition.Rewrite(body, [new(predicate, predicateBody, true)], boolean, v => v is FieldValue);
            a.Equal(condition == Cond.FUne, actual.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Any(c => c.Inlined),
                "浮点反向分支保持正负零相等，且不能把 NaN 的有序不等当作无序不等");
        }
        var stateField = new FieldRef(new FieldDef { Index = 3, Owner = owner, Name = "state", Type = boolean, Offset = 28,
            Attributes = FieldAttributes.Private }, ownerType);
        var state = new FieldValue(receiver, stateField, boolean, 8);
        var activeField = new FieldRef(new FieldDef { Index = 5, Owner = owner, Name = "active", Type = boolean, Offset = 29,
            Attributes = FieldAttributes.Private }, ownerType);
        var active = new FieldValue(receiver, activeField, boolean, 8);
        var configure = Method(6, owner, "Configure", new PrimitiveRef("void"));
        configure.Method.Parameters = [new("enabled", boolean, 0, null, false)];
        var byteType = new DefinitionRef(Type(6, "Byte", true), []);
        var byteFlag = new ConversionValue(ConvKind.Truncate, Masked(argument, 1), byteType, 8);
        var configBody = new ManagedBody(configure, [new(0, [new ManagedBranch(0, argument, new(4, []), new(8, []))]),
            new(4, [new ManagedStore(4, number, zero with { Bits = 0x40000000 }), new ManagedJump(6, new(12, []))]),
            new(8, [new ManagedStore(8, number, zero with { Bits = 0x3f800000 }), new ManagedJump(10, new(12, []))]),
            new(12, [new ManagedStore(12, state, byteFlag), new ManagedStore(14, active, yes), new ManagedReturn(16, null)])]);
        foreach (var stored in new[] { no, yes })
        {
            var body = new ManagedBody(Method(7, owner, "SetFixed", new PrimitiveRef("void")), [new(100,
                [new ManagedStore(100, number, zero with { Bits = 0x3f800000 }), new ManagedStore(102, active, yes),
                    new ManagedStore(104, state, stored), new ManagedJump(108, new(200, []))]),
                new(200, [new ManagedReturn(200, null)])]);
            var actual = InlineRecognition.Rewrite(body, [new(configure, configBody, false)], boolean, v => v is FieldValue);
            a.Equal(stored == no, actual.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Any(c => c.Inlined),
                "同对象的独立 bool 写入交换后仍须核对常量分支及全部字段值");
        }
        var ready = Method(8, worker, "IsReady", boolean);
        var inspect = Method(9, owner, "Inspect", boolean);
        var inspectBody = new ManagedBody(inspect, [new(0, [new ManagedAssignment(0, loaded, new FieldValue(receiver, field, workerType, 64)),
            new ManagedCall(4, new(ready, loaded, [], false), result, false), new ManagedReturn(8, result)])]);
        var later = new LocalValue(new(Storage.Gpr(3), 1), workerType, 64);
        var following = new ManagedBlock(200, [new ManagedAssignment(200, later, new FieldValue(receiver, field, workerType, 64)),
            new ManagedBranch(204, new ComparisonValue(Cond.Eq, later, new ConstantValue(0, workerType, 64), boolean), new(400, []), new(500, []))]);
        var inspecting = new ManagedBody(Method(10, owner, "InspectThenRead", boolean),
            [new(100, [new ManagedAssignment(100, loaded, new FieldValue(receiver, field, workerType, 64)),
                new ManagedCall(104, new(ready, loaded, [], false), result, false), new ManagedBranch(108, result, new(200, []), new(300, []))]),
                following, new(300, [new ManagedReturn(300, no)]), new(400, [new ManagedReturn(400, no)]), new(500, [new ManagedReturn(500, yes)])]);
        var inspected = InlineRecognition.Rewrite(inspecting, [new(inspect, inspectBody, true)], boolean, v => v is FieldValue);
        a.True(inspected.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Any(c => c.Inlined && c.Invocation.Method == inspect)
            && inspected.Blocks.Contains(following), "有调用的 bool 包装在返回分支处结束，不吞并调用者后续同字段条件");
        return a.Finish("inline-discard");
    }
}
