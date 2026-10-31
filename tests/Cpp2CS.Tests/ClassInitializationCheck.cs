using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Image;
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
        var wide = (Load)Load();
        var extended = new Cpp2CS.Ir.Convert(ConvKind.ZeroExtend, wide, 64);
        Expr Bit(Expr value, ulong mask = 1) => new Compare(Cond.Ne, new Binary(BinOp.And, value, Expr.C(mask, value.Width), value.Width), Expr.C(0, value.Width));
        a.True(ClassInitializationFlags.IsBitTest(Bit(extended), wide), "16 位读取只检查初始化低位");
        a.True(ClassInitializationFlags.IsBitTest(Bit(new Extract(extended, 0, 32)), wide), "寄存器截取仍保留低位");
        a.True(!ClassInitializationFlags.IsBitTest(Bit(extended, 2), wide), "其他标志位不能作为初始化证据");
        a.True(!ClassInitializationFlags.IsBitTest(new Compare(Cond.Ne, extended, Expr.C(0, 64)), wide), "整个标志字非零不能作为初始化证据");
        a.True(ClassInitializationFlags.IsReload(extended, wide), "重读保留零扩展");
        a.True(!ClassInitializationFlags.IsReload(new Cpp2CS.Ir.Convert(ConvKind.SignExtend, wide, 64), wide), "不能将符号扩展替换为零扩展");
        a.True(!ClassInitializationFlags.IsReload(new Load(Expr.C(0, 64), 16), wide), "重读必须来自同一字段");
        var block = new Block(0) { End = 24, Statements = [Init(4), read, Init(12) with { Defines = [result] }, Test(1)] };
        a.True(ClassInitializationFacts.Run(Function(block)), "初始化之后的 16 位读取只按低位折叠");
        a.True(block.Statements[^1] is Branch { Condition: Const { Value: 1 } }, "低位已置位");
        a.True(block.Statements[2] is Define { Target: var target, Value: Symbol } && target == result, "重复初始化的返回类指针仍保留");
        block.Statements = [Init(4), Init(8), new Call(12, CallKind.Direct, Expr.C(0, 64))
            { Op = new(OpKind.RunClassConstructor, type), Arguments = [klass] },
            new Define(16, flags, new Load(new Binary(BinOp.Add, klass, Expr.C(RuntimeLayout.ClassCctorFinishedOrNoCctor, 64), 64), 32))];
        a.True(ClassInitializationFacts.Run(Function(block), constructorFacts: false), "静态构造内部仍可消除重复布局初始化");
        a.True(block.Statements[1] is Nop && block.Statements[3] is Define { Value: Cpp2CS.Ir.Load }, "布局初始化不代表静态构造已经完成");
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
        foreach (var mode in new[] { "disjoint", "overlap", "unknown" })
        {
            var fieldWrite = ReloadGuard();
            var subject = new Use(new(Storage.Gpr(0), 0), 64);
            fieldWrite.EntryBlock.Statements.Insert(1, new Store(6,
                new Binary(BinOp.Add, subject, Expr.C(mode == "overlap" ? 20UL : 24UL, 64), 64), Expr.C(1, 32)));
            a.Equal(mode == "disjoint", ClassInitializationReloads.Run(fieldWrite, e => mode != "unknown" && e == subject ? type : null),
                $"托管字段写入与重读的范围证明 {mode}");
        }
        var fastCalculation = ReloadGuard();
        var fastHead = fastCalculation.EntryBlock;
        var fastMerge = fastCalculation.Blocks[2];
        var fastPhi = (Phi)fastMerge.Statements[0];
        MachineFunction.RemoveEdge(fastHead, fastMerge);
        var fastComputed = new Variable(Storage.Gpr(1), 4);
        var fastBlock = new Block(64) { Statements = [new Define(64, fastComputed, new Use(fastPhi.Sources[0], 64)), new Jump(68, fastMerge.Start)] };
        MachineFunction.AddEdge(fastHead, fastBlock);
        MachineFunction.AddEdge(fastBlock, fastMerge);
        fastMerge.Statements[0] = ((Phi)fastMerge.Statements[0]) with { Sources = [fastPhi.Sources[1], fastComputed] };
        fastHead.Statements[^1] = ((Branch)fastHead.Statements[^1]) with { Target = fastBlock.Start };
        fastCalculation.Blocks.Add(fastBlock);
        fastCalculation.Renumber();
        a.True(ClassInitializationReloads.Run(fastCalculation), "快路径经过纯计算后仍可比较最终汇合值");
        foreach (var mode in new[] { "same", "different", "repeat", "write", "other-write" })
        {
            var input = new Use(new(Storage.Vec(0), 0), 32);
            Expr Rounded(ulong fallback) => new Select(new Compare(Cond.FEq, new Unary(UnOp.FCeil, input, 32), Expr.C(0x7f800000, 32)),
                Expr.C(fallback, 32), new Cpp2CS.Ir.Convert(ConvKind.FloatToSInt, new Unary(UnOp.FCeil, input, 32), 32), 32);
            var flag = new Load(new Binary(BinOp.Add, klass, Expr.C(RuntimeLayout.ClassCctorFinishedOrNoCctor, 64), 64), 32);
            var fast = new Variable(Storage.Gpr(1), 1);
            var slow = fast with { Version = 2 };
            var merged = fast with { Version = 3 };
            var guard = new Block(0) { Statements = [new Branch(0, new Compare(Cond.Eq, flag, Expr.C(0, 32)), 16, 32)] };
            var initialize = new Block(16) { Statements = [new Call(16, CallKind.Direct, Expr.C(0, 64))
                { Op = new(OpKind.RunClassConstructor, type), Arguments = [klass] }, new Define(20, slow, Rounded(mode == "different" ? 0UL : 0x80000000)), new Jump(24, 48)] };
            var skip = new Block(32) { Statements = [new Define(32, fast, Rounded(0x80000000)), new Jump(36, 48)] };
            var done = new Block(48) { Statements = [new Phi(48, merged, [slow, fast]), new Return(52) { Value = new Use(merged, 32) }] };
            MachineFunction.AddEdge(guard, initialize); MachineFunction.AddEdge(guard, skip);
            MachineFunction.AddEdge(initialize, done); MachineFunction.AddEdge(skip, done);
            if (mode == "repeat") initialize.Statements.Insert(2, initialize.Statements[0] with { Address = 22 });
            if (mode is "write" or "other-write")
            {
                initialize.Statements.Insert(2, new Store(22, Expr.C(128, 64), new Use(slow, 32)));
                skip.Statements.Insert(1, new Store(34, Expr.C(mode == "other-write" ? 132UL : 128UL, 64), new Use(fast, 32)));
            }
            a.Equal(mode is not ("different" or "other-write"), ClassInitializationReloads.Run(Function(guard, initialize, skip, done)),
                "取整、重复初始化及写入逐项核对，保留无穷值分支和目标地址");
        }
        foreach (var same in new[] { true, false })
        {
            var first = new Variable(Storage.Gpr(10), 1);
            var other = new Variable(Storage.Gpr(11), 1);
            var alias = first with { Version = 2 };
            var copied = first with { Version = 3 };
            var merged = first with { Version = 4 };
            var input = new Block(0) { Statements = [new Define(0, first, new Use(new(Storage.Gpr(1), 0), 64)),
                new Define(4, other, new Use(new(Storage.Gpr(2), 0), 64)), new Jump(8, 16)] };
            var guard = new Block(16) { Statements = [new Phi(16, alias, [same ? first : other]),
                new Branch(20, new Compare(Cond.Ne, new Load(new Binary(BinOp.Add, klass, Expr.C(RuntimeLayout.ClassCctorFinishedOrNoCctor, 64), 64), 32), Expr.C(0, 32)), 48, 32)] };
            var initialize = new Block(32) { Statements = [new Define(32, copied, new Cpp2CS.Ir.Convert(ConvKind.ZeroExtend, new Use(alias, 32), 64)),
                new Call(36, CallKind.Direct, Expr.C(0, 64)) { Op = new(OpKind.RunClassConstructor, type), Arguments = [klass] }, new Jump(40, 48)] };
            var done = new Block(48) { Statements = [new Phi(48, merged, [first, copied]), new Return(52) { Value = new Use(merged, 32) }] };
            MachineFunction.AddEdge(input, guard); MachineFunction.AddEdge(guard, done); MachineFunction.AddEdge(guard, initialize); MachineFunction.AddEdge(initialize, done);
            a.Equal(same, ClassInitializationReloads.Run(Function(input, guard, initialize, done)), "单来源合流仍须证明观察位上的值相同");
        }
        MachineFunction ExtendedReload(bool changedField = false, bool sideEffect = false, string? stored = null)
        {
            var oldValue = new Variable(Storage.Gpr(1), 1);
            var newValue = oldValue with { Version = 2 };
            var statics = new Symbol(SymbolKind.StaticFields, type);
            Expr Read(ulong offset) => new Cpp2CS.Ir.Convert(ConvKind.ZeroExtend,
                new Load(new Binary(BinOp.Add, statics, Expr.C(offset, 64), 64), 32), 64);
            var flag = new Load(new Binary(BinOp.Add, klass, Expr.C(RuntimeLayout.ClassCctorFinishedOrNoCctor, 64), 64), 32);
            var guard = new Block(0) { Statements = [new Define(4, oldValue, Read(4))] };
            var fastValue = oldValue;
            if (stored is not null)
            {
                var incremented = new Variable(Storage.Gpr(2), 1);
                guard.Statements.Add(new Define(6, incremented, new Cpp2CS.Ir.Convert(ConvKind.ZeroExtend,
                    new Binary(BinOp.Add, new Use(oldValue, 32), Expr.C(1, 32), 32), 64)));
                guard.Statements.Add(new Store(7, new Binary(BinOp.Add, statics, Expr.C(stored == "field" ? 8UL : 4UL, 64), 64),
                    new Use(incremented, stored == "width" ? 64 : 32)));
                if (stored != "value") fastValue = incremented;
            }
            if (sideEffect) guard.Statements.Add(new Store(8, statics, Expr.C(1, 32)));
            guard.Statements.Add(new Branch(12, new Compare(Cond.Eq, flag, Expr.C(0, 32)), 16, 32));
            var initialize = new Block(16) { Statements = [new Call(16, CallKind.Direct, Expr.C(0, 64))
                { Op = new(OpKind.RunClassConstructor, type), Arguments = [klass] },
                new Define(20, newValue, Read(changedField ? 8UL : 4UL)), new Jump(24, 32)] };
            var merged = new Variable(Storage.Gpr(1), 3);
            var done = new Block(32) { Statements = [new Phi(32, merged, [fastValue, newValue]), new Return(36) { Value = new Use(merged, 64) }] };
            MachineFunction.AddEdge(guard, done); MachineFunction.AddEdge(guard, initialize); MachineFunction.AddEdge(initialize, done);
            return Function(guard, initialize, done);
        }
        a.True(ClassInitializationReloads.Run(ExtendedReload()), "扩展到寄存器的同字段加载仍是已读取的快照");
        a.True(!ClassInitializationReloads.Run(ExtendedReload(changedField: true)), "扩展加载不能证明不同字段已读取");
        a.True(!ClassInitializationReloads.Run(ExtendedReload(sideEffect: true)), "扩展加载与守卫之间仍禁止写入");
        a.True(ClassInitializationReloads.Run(ExtendedReload(stored: "exact")), "同字段同宽度写入后的重读与快路径写入值一致");
        a.True(!ClassInitializationReloads.Run(ExtendedReload(stored: "field")), "写入其他字段不能证明重读值");
        a.True(ClassInitializationReloads.Run(ExtendedReload(stored: "width")), "整值写入覆盖低位字段时可提供重读快照");
        a.True(!ClassInitializationReloads.Run(ExtendedReload(stored: "value")), "已有同字段写入仍须核对快慢路径的合流值");
        a.True(!ClassInitializationReloads.Run(ExtendedReload(stored: "exact", sideEffect: true)), "写入见证与守卫之间不能有其他写入");
        foreach (var width in new[] { 32, 64 })
        {
            var narrowed = ExtendedReload();
            var old = (Define)narrowed.EntryBlock.Statements[0];
            var address = ((Load)((Cpp2CS.Ir.Convert)old.Value).Operand).Address;
            narrowed.EntryBlock.Statements[0] = old with { Value = new Use(new(Storage.Gpr(0), 0), 64) };
            narrowed.EntryBlock.Statements.Insert(1, new Store(6, address, new Use(old.Target, 32)));
            var done = narrowed.Blocks[^1];
            var returned = (Return)done.Statements[^1];
            done.Statements[^1] = returned with { Value = new Use(((Use)returned.Value!).Variable, width) };
            a.Equal(width == 32, ClassInitializationReloads.Run(narrowed), "仅观察低位时允许与窄字段重读合流");
        }
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
