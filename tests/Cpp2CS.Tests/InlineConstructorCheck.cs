using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class InlineConstructorCheck
{
    [Command("inline-constructors", "内联构造的尾部写屏障与字段实参匹配", Gate = Gate.Unit)]
    public static int Run()
    {
        var type = new TypeDef { Index = -1, Assembly = "Constructors.Tests.dll", Namespace = "Tests", Name = "Subject",
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var reference = new DefinitionRef(type, []);
        var method = new MethodRef(new MethodDef { Index = -1, Owner = type, Name = ".ctor", Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1 }, [], []);
        var self = new Use(new(Storage.Gpr(0), 0), 64);
        var argument = new Use(new(Storage.Gpr(1), 0), 64);
        var signature = new AbiSignature(new(reference, Passing.Registers, [new(Storage.Gpr(0), 64, 0)]),
            [new(reference, Passing.Registers, [new(Storage.Gpr(1), 64, 0)])], null, null);
        Call Base(Expr receiver) => new(4, CallKind.Direct, Expr.C(200, 64))
            { Sources = [Storage.Gpr(0)], Arguments = [receiver] };
        Store Field(Expr receiver, Expr value) => new(8, new Binary(BinOp.Add, receiver, Expr.C(16, 64), 64), value);
        MachineFunction Function(params Stmt[] statements) => new() { Entry = 0,
            Range = new(0, 32, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [new(0) { Statements = statements.ToList() }] };
        var tail = new Call(12, CallKind.Tail, Expr.C(300, 64)) { Op = new(OpKind.WriteBarrier, null) };
        var pattern = InlineConstructors.Create(method, signature, Function(Base(self), Field(self, argument), tail));
        var a = new Assertions();
        a.True(pattern is { Effects.Count: 2 }, "尾部写屏障结束构造模板，不重复要求普通调用形态");
        var created = new Variable(Storage.Gpr(0), 1);
        var value = Expr.C(64, 64);
        var caller = Function(new Call(0, CallKind.Direct, Expr.C(100, 64)), Base(new Use(created, 64)), Field(new Use(created, 64), value), tail);
        var match = InlineConstructors.Find(pattern!, caller, caller.EntryBlock, 0, created);
        a.True(match is { Statements.Count: 2 } && match.Arguments.SequenceEqual([value]), "字段值绑定成构造实参");
        a.True(!match!.Statements.Contains(tail), "调用点的尾部屏障保留返回语义");
        a.True(InlineConstructors.Create(method, signature, Function(Base(self), Field(self, argument), tail with { Op = null })) is null,
            "未知尾调用不能当成构造结束");
        a.True(InlineConstructors.Create(method, signature, Function(Base(self), Field(self, argument))) is null,
            "缺少已证明终结点时不生成模板");
        caller.EntryBlock.Statements[2] = Field(new Use(created, 64), new Load(value, 64));
        a.True(InlineConstructors.Find(pattern!, caller, caller.EntryBlock, 0, created) is null,
            "不能把有访存的实参提前到对象分配点");
        var guarded = Function(new Call(0, CallKind.Direct, Expr.C(100, 64)), Base(new Use(created, 64)), new Jump(8, 16));
        var writes = new Block(16) { Statements = [Field(new Use(created, 64), value), new Return(20)] };
        var handler = new Block(24) { IsLandingPad = true, Statements = [new Return(28)] };
        MachineFunction.AddEdge(guarded.EntryBlock, writes);
        MachineFunction.AddEdge(guarded.EntryBlock, handler);
        guarded.EntryBlock.Handler = handler;
        guarded.Blocks.AddRange([writes, handler]);
        guarded.Renumber();
        a.True(InlineConstructors.Find(pattern!, guarded, guarded.EntryBlock, 0, created) is not null,
            "新对象直接字段写入可位于保护调用之后的无异常边块");
        guarded.EntryBlock.Statements.RemoveAt(1);
        writes.Statements.Insert(0, Base(new Use(created, 64)));
        a.True(InlineConstructors.Find(pattern!, guarded, guarded.EntryBlock, 0, created) is null,
            "基类调用不能跨越分配的异常去向");
        return a.Finish("inline-constructors");
    }
}
