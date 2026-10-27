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
        return a.Finish("inline-discard");
    }
}
