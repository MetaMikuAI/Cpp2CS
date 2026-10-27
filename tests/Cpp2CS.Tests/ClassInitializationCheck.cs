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

        MachineFunction ReloadGuard(bool checkedBefore = true, bool changedField = false, bool sideEffect = false, bool reverse = false)
        {
            var oldValue = new Variable(Storage.Gpr(1), 1);
            var newValue = oldValue with { Version = 2 };
            var subject = new Use(new(Storage.Gpr(0), 0), 64);
            Expr Field(ulong offset) => new Load(new Binary(BinOp.Add, subject, Expr.C(offset, 64), 64), 64);
            Call Check(Variable value) => new(8, CallKind.Direct, Expr.C(0, 64)) { Op = new(OpKind.NullCheck, null), Arguments = [new Use(value, 64)] };
            var guard = new Block(0) { Statements = [new Define(4, oldValue, Field(16))] };
            if (checkedBefore) guard.Statements.Add(Check(oldValue));
            if (sideEffect) guard.Statements.Add(new Store(10, Expr.C(128, 64), Expr.C(1, 64)));
            var load = new Load(new Binary(BinOp.Add, klass, Expr.C(RuntimeLayout.ClassCctorFinishedOrNoCctor, 64), 64), 32);
            guard.Statements.Add(new Branch(12, new Compare(reverse ? Cond.Eq : Cond.Ne, load, Expr.C(0, 32)), reverse ? 16UL : 32UL, reverse ? 32UL : 16UL));
            var initialize = new Block(16) { Statements = [new Call(16, CallKind.Direct, Expr.C(0, 64))
                { Op = new(OpKind.RunClassConstructor, type), Arguments = [klass] },
                new Define(20, newValue, Field(changedField ? 24UL : 16UL)), Check(newValue), new Jump(28, 32)] };
            var done = new Block(32) { Statements = [new Phi(32, new(Storage.Gpr(1), 3), [oldValue, newValue]), new Return(36)] };
            MachineFunction.AddEdge(guard, done); MachineFunction.AddEdge(guard, initialize); MachineFunction.AddEdge(initialize, done);
            return Function(guard, initialize, done);
        }
        var guarded = ReloadGuard();
        a.True(ClassInitializationReloads.Run(guarded), "已有快照和判空时保留初始化后的同字段重读");
        a.True(guarded.EntryBlock.Statements[^1] is Jump { Target: 16 }, "统一执行幂等类构造检查");
        a.True(guarded.Blocks[2].Statements[0] is Phi { Sources.Length: 1 }, "汇合只保留重新读取的输入");
        a.True(ClassInitializationReloads.Run(ReloadGuard(reverse: true)), "反向条件同样识别");
        a.True(!ClassInitializationReloads.Run(ReloadGuard(checkedBefore: false)), "缺少原先判空不能增加抛出点");
        a.True(!ClassInitializationReloads.Run(ReloadGuard(changedField: true)), "不能重读不同字段");
        a.True(!ClassInitializationReloads.Run(ReloadGuard(sideEffect: true)), "字段快照与守卫之间有写入时拒绝");
        MachineFunction SharedGuard(bool differentValue = false, bool effect = false, bool otherType = false, bool handler = false)
        {
            var one = new Variable(Storage.Gpr(1), 0);
            var two = new Variable(Storage.Gpr(2), 0);
            var selected = new Variable(Storage.Gpr(3), 1);
            var final = new Variable(Storage.Gpr(4), 1);
            var flag = new Load(new Binary(BinOp.Add, klass, Expr.C(RuntimeLayout.ClassCctorFinishedOrNoCctor, 64), 64), 32);
            var entry = new Block(0) { Statements = [new Branch(0, Expr.C(1, 1), 16, 32)] };
            var first = new Block(16) { Statements = [new Branch(16, new Compare(Cond.Ne, flag, Expr.C(0, 32)), 64, 48)] };
            var second = new Block(32) { Statements = [new Branch(32, new Compare(Cond.Ne, flag, Expr.C(0, 32)), 64, 48)] };
            var initializer = new Block(48) { Statements = [new Phi(48, selected, differentValue ? [two, one] : [one, two]),
                new Call(52, CallKind.Direct, Expr.C(0, 64)) { Op = new(OpKind.RunClassConstructor, otherType ? null : type), Arguments = [klass] }, new Jump(56, 64)] };
            var done = new Block(64) { Statements = [new Phi(64, final, [one, two, selected]), new Return(68) { Value = new Use(final, 64) }] };
            MachineFunction.AddEdge(entry, first); MachineFunction.AddEdge(entry, second);
            MachineFunction.AddEdge(first, done); MachineFunction.AddEdge(first, initializer);
            MachineFunction.AddEdge(second, done); MachineFunction.AddEdge(second, initializer);
            MachineFunction.AddEdge(initializer, done);
            if (effect) initializer.Statements.Insert(1, new Store(50, Expr.C(128, 64), Expr.C(1, 64)));
            if (handler) initializer.Handler = done;
            return Function(entry, first, second, initializer, done);
        }
        var shared = SharedGuard();
        a.True(ClassInitializationReloads.Run(shared), "同型初始化尾部可由多条业务路径共用");
        a.True(ClassInitializationReloads.Run(shared), "另一条入口也保留自身的合流参数");
        a.True(!ClassInitializationReloads.Run(SharedGuard(differentValue: true)), "初始化分支更改业务值时不能强制执行");
        a.True(!ClassInitializationReloads.Run(SharedGuard(effect: true)), "共用尾部有写入时拒绝");
        a.True(!ClassInitializationReloads.Run(SharedGuard(otherType: true)), "初始化目标必须与守卫一致");
        a.True(!ClassInitializationReloads.Run(SharedGuard(handler: true)), "共用尾部不能跨异常区域");
        return a.Finish("class-initialization");
    }
}
