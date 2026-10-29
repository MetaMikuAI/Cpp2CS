using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class MergedAllocationCheck
{
    [Command("merged-allocation", "合流构造的分配时序、对象别名与纯路径边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var type = new DefinitionRef(new TypeDef { Index = -1, Assembly = "Allocation.Tests.dll", Namespace = "Tests",
            Name = "Subject", Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false }, []);
        var leftObject = new Variable(Storage.Gpr(0), 1);
        var rightObject = new Variable(Storage.Gpr(0), 2);
        var merged = new Variable(Storage.Gpr(0), 3);
        var alias = new Variable(Storage.Gpr(20), 1);
        var input = new Use(new(Storage.Gpr(4), 0), 64);
        bool Apply(MachineFunction f) => MergedAllocations.Run(f, (call, t) => call.Target == Expr.C(200, 64) && t == type);
        MachineFunction Example()
        {
            Call Allocate(int address, Variable value) => new((ulong)address, CallKind.Direct, Expr.C(100, 64))
                { Op = new(OpKind.NewObject, type), Defines = [value], Arguments = [new Symbol(SymbolKind.Class, type)] };
            var entry = new Block(0) { Statements = [new Branch(0, new Compare(Cond.Eq, input, Expr.C(0, 64)), 4, 12)] };
            var left = new Block(4) { Statements = [Allocate(4, leftObject), new Jump(8, 20)] };
            var right = new Block(12) { Statements = [Allocate(12, rightObject), new Jump(16, 20)] };
            var join = new Block(20) { Statements = [new Phi(20, merged, [leftObject, rightObject]),
                new Phi(20, alias, [leftObject, rightObject]),
                new Call(24, CallKind.Direct, Expr.C(200, 64)) { Sources = [Storage.Gpr(0)], Arguments = [new Use(merged, 64)] },
                new Return(28) { Value = new Use(alias, 64) }] };
            MachineFunction.AddEdge(entry, left); MachineFunction.AddEdge(entry, right);
            MachineFunction.AddEdge(left, join); MachineFunction.AddEdge(right, join);
            var f = new MachineFunction { Entry = 0, Range = new(0, 80, CodeRegion.Managed, BoundaryEvidence.EhFrame),
                Blocks = [entry, left, right, join] };
            f.Renumber();
            return f;
        }
        Block At(MachineFunction f, ulong address) => f.Blocks.Single(b => b.Start == address);
        var simple = Example();
        a.True(Apply(simple) && simple.Blocks.SelectMany(b => b.Statements).OfType<Call>().Count(c => c.Op?.Kind == OpKind.NewObject) == 1,
            "互斥分支同类型分配在公共构造前合并一次");
        a.True(At(simple, 20).Statements is [Call { Op.Kind: OpKind.NewObject }, Call { Op: null }, Return { Value: Use u }]
            && u.Variable == merged, "重复对象 phi 替换为公共对象，构造和后续使用顺序不变");
        var nested = Example();
        var right = At(nested, 12);
        MachineFunction.RemoveEdge(right, At(nested, 20));
        right.Statements[^1] = new Branch(16, new Compare(Cond.Eq, input, Expr.C(1, 64)), 32, 40);
        var first = new Block(32) { Statements = [new Define(32, new(Storage.Gpr(3), 1), Expr.C(6, 64)), new Jump(36, 48)] };
        var second = new Block(40) { Statements = [new Define(40, new(Storage.Gpr(3), 2), Expr.C(7, 64)), new Jump(44, 48)] };
        var choice = new Block(48) { Statements = [new Phi(48, new(Storage.Gpr(3), 3), [new(Storage.Gpr(3), 1), new(Storage.Gpr(3), 2)]), new Jump(52, 20)] };
        MachineFunction.AddEdge(right, first); MachineFunction.AddEdge(right, second);
        MachineFunction.AddEdge(first, choice); MachineFunction.AddEdge(second, choice); MachineFunction.AddEdge(choice, At(nested, 20));
        At(nested, 20).Statements[0] = new Phi(20, merged, [leftObject, rightObject]);
        At(nested, 20).Statements[1] = new Phi(20, alias, [leftObject, rightObject]);
        nested.Blocks.AddRange([first, second, choice]); nested.Renumber();
        a.True(Apply(nested) && choice.Statements.OfType<Phi>().Count() == 1, "分配后纯分支选择参数可保留原 phi 后合并");

        foreach (var statement in new Stmt[] {
            new Define(6, new(Storage.Gpr(2), 1), new Load(input, 64)),
            new Call(6, CallKind.Direct, Expr.C(300, 64)),
            new Store(6, input, Expr.C(0, 64)),
            new Define(6, new(Storage.Gpr(2), 1), new Use(leftObject, 64)),
            new Return(6),
        })
        {
            var rejected = Example(); At(rejected, 4).Statements.Insert(1, statement);
            a.True(!Apply(rejected), $"拒绝分配后有 {statement.GetType().Name} 副作用、逃逸或提前退出");
        }
        var loop = Example();
        MachineFunction.AddEdge(At(loop, 4), At(loop, 4));
        a.True(!Apply(loop), "存在不能保证到达构造的循环时拒绝");
        var mismatch = Example();
        At(mismatch, 20).Statements[1] = new Phi(20, alias, [rightObject, leftObject]);
        a.True(!Apply(mismatch), "其他对象 phi 的入边对应不同，不冒充同一别名");
        var wrongTarget = Example();
        var target = (Call)At(wrongTarget, 20).Statements[2];
        At(wrongTarget, 20).Statements[2] = target with { Target = Expr.C(201, 64) };
        a.True(!Apply(wrongTarget), "公共调用必须是已证明的同类型构造");
        var guarded = Example();
        At(guarded, 4).Handler = new Block(64) { IsLandingPad = true };
        a.True(!Apply(guarded), "受保护分配不可挪到不同异常去向");
        return a.Finish("merged-allocation");
    }
}
