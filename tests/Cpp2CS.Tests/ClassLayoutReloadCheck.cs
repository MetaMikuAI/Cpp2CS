using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

internal static class ClassLayoutReloadCheck
{
    [Command("class-layout-reload", "开放泛型布局重读、返回别名与拒绝边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var type = new GenericParameterRef("T", true, 0);
        var klass = new Symbol(SymbolKind.Class, type);
        MachineFunction Function(int offset = RuntimeLayout.ClassStackSlotSize, bool write = false, bool other = false, bool handler = false, bool reverse = false)
        {
            Variable V(int register, int version) => new(Storage.Gpr(register), version);
            Expr Size(Expr subject, int field) => new Load(new Binary(BinOp.Add, subject, Expr.C((ulong)field, 64), 64), 32);
            var prior = V(8, 1); var returned = V(0, 1); var updated = V(8, 2); var skipped = V(8, 3);
            var flags = new Load(new Binary(BinOp.Add, klass, Expr.C(RuntimeLayout.ClassBitflags1, 64), 64), 8);
            var head = new Block(0) { Statements = [new Define(0, prior, Size(klass, RuntimeLayout.ClassStackSlotSize)),
                new Branch(4, new Compare(reverse ? Cond.Eq : Cond.Ne, new Binary(BinOp.And, flags, Expr.C(1, 8), 8), Expr.C(0, 8)), reverse ? 16UL : 32UL, reverse ? 32UL : 16UL)] };
            var initialize = new Block(16) { Statements = [new Call(16, CallKind.Direct, Expr.C(0, 64))
                { Op = new(OpKind.InitClass, other ? new GenericParameterRef("U", true, 1) : type), Arguments = [klass], Defines = [returned] },
                new Define(20, updated, Size(new Use(returned, 64), offset)), new Jump(24, 48)] };
            var skip = new Block(32) { Statements = [new Define(32, skipped, new Use(prior, 32)), new Jump(36, 48)] };
            var merge = new Block(48) { Statements = [new Phi(48, V(8, 4), [updated, skipped]), new Return(52)] };
            if (write) initialize.Statements.Insert(2, new Store(22, Expr.C(128, 64), Expr.C(1, 32)));
            MachineFunction.AddEdge(head, reverse ? initialize : skip); MachineFunction.AddEdge(head, reverse ? skip : initialize);
            MachineFunction.AddEdge(initialize, merge); MachineFunction.AddEdge(skip, merge);
            if (handler) initialize.Handler = merge;
            var function = new MachineFunction { Entry = 0, Range = new(0, 64, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [head, initialize, skip, merge] };
            function.Renumber(); return function;
        }
        var a = new Assertions();
        foreach (var reverse in new[] {false, true})
        {
            var function = Function(reverse: reverse);
            a.True(ClassLayoutReloads.Run(function), "初始化后同字段读取可统一");
            a.True(function.EntryBlock.Statements[^1] is Jump {Target:16}, "保留初始化与新读取");
        }
        a.True(!ClassLayoutReloads.Run(Function(offset: 0xf8)), "不同布局字段不合并");
        a.True(!ClassLayoutReloads.Run(Function(write:true)), "初始化区域的业务写入保留");
        a.True(!ClassLayoutReloads.Run(Function(other:true)), "不能初始化另一类型");
        a.True(!ClassLayoutReloads.Run(Function(handler:true)), "不跨异常处理范围");
        return a.Finish("class-layout-reload");
    }
}
