using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

internal static class ClassInitializationCheck
{
    [Command("class-initialization", "类初始化支配关系、旧标志快照和高位保留", Gate = Gate.Unit)]
    public static int Run()
    {
        var definition = new TypeDef { Index = 1, Assembly = "Classes.Tests.dll", Namespace = "Tests", Name = "Subject", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var type = new DefinitionRef(definition, []); var klass = new Symbol(SymbolKind.Class, type);
        var flags = new Variable(Storage.Gpr(9), 1); var result = new Variable(Storage.Gpr(0), 1);
        Call Init(ulong address) => new(address, CallKind.Direct, Expr.C(0, 64)) { Op = new(OpKind.InitClass, type), Arguments = [klass] };
        Expr Load() => new Load(new Binary(BinOp.Add, klass, Expr.C(RuntimeLayout.ClassBitflags1, 64), 64), 16);
        var read = new Define(8, flags, new Cpp2CS.Ir.Convert(ConvKind.ZeroExtend, Load(), 64));
        Branch Test(ulong mask) => new(16, new Compare(Cond.Ne, new Binary(BinOp.And, new Use(flags, 64), Expr.C(mask, 64), 64), Expr.C(0, 64)), 32, 48);
        MachineFunction Function(params Block[] blocks)
        {
            var function = new MachineFunction { Entry = blocks[0].Start, Range = new(0, 0x100, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [.. blocks] };
            function.Renumber(); return function;
        }
        var a = new Assertions();
        var block = new Block(0) { End = 24, Statements = [Init(4), read, Init(12) with { Defines = [result] }, Test(1)] };
        a.True(ClassInitializationFacts.Run(Function(block)), "初始化之后的 16 位读取只按低位折叠");
        a.True(block.Statements[^1] is Branch { Condition: Const { Value: 1 } }, "低位已置位");
        a.True(block.Statements[2] is Define { Target: var target, Value: Symbol } && target == result, "重复初始化的返回类指针仍保留");
        block.Statements = [read, Init(12), Test(1)];
        a.True(!ClassInitializationFacts.Run(Function(block)), "初始化之前的旧标志快照不可折叠");
        block.Statements = [Init(4), read, Test(0x100)];
        a.True(!ClassInitializationFacts.Run(Function(block)), "16 位读取的其他标志位保留");
        block.Statements = [read, Test(1)];
        a.True(!ClassInitializationFacts.Run(Function(block)), "没有初始化证据时保留判断");
        var start = new Block(0) { Statements = [new Branch(0, Expr.C(1, 1), 32, 48)] };
        var left = new Block(32) { Statements = [Init(32), new Jump(36, 64)] };
        var right = new Block(48) { Statements = [new Jump(48, 64)] };
        var merge = new Block(64) { Statements = [read, Test(1)] };
        MachineFunction.AddEdge(start, left); MachineFunction.AddEdge(start, right); MachineFunction.AddEdge(left, merge); MachineFunction.AddEdge(right, merge);
        a.True(!ClassInitializationFacts.Run(Function(start, left, right, merge)), "只有一条入边初始化不满足支配关系");
        return a.Finish("class-initialization");
    }
}
