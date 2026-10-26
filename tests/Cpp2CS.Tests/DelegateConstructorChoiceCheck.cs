using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class DelegateConstructorChoiceCheck
{
    [Command("delegate-constructor-choices", "分支方法身份与接收者的委托构造配对", Gate = Gate.Unit)]
    public static int Run()
    {
        var owner = new TypeDef { Index = -1, Assembly = "Choices.Tests.dll", Namespace = "Tests", Name = "Subject", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        MethodRef Method(string name) => new(new MethodDef { Index = -1, Owner = owner, Name = name, Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1 }, [], []);
        var identity = new Variable(Storage.Gpr(2), 3);
        var receiver = new Variable(Storage.Gpr(1), 3);
        var firstMethod = identity with { Version = 1 };
        var secondMethod = identity with { Version = 2 };
        var methods = new Dictionary<Variable, Expr> { [firstMethod] = new Symbol(SymbolKind.Method, Method("First")),
            [secondMethod] = new Symbol(SymbolKind.Method, Method("Second")) };
        var constructor = new Call(20, CallKind.Direct, Expr.C(200, 64))
            { Arguments = [new Use(new(Storage.Gpr(0), 1), 64), new Use(receiver, 64), new Use(identity, 64)] };
        MachineFunction Diamond(bool effects = false, bool handler = false, bool extraPredecessor = false)
        {
            var entry = new Block(0);
            var left = new Block(4) { Statements = [new Jump(4, 16)] };
            var right = new Block(8);
            var join = new Block(16) { Statements = [new Phi(16, identity, [firstMethod, secondMethod]),
                new Phi(16, receiver, [new(Storage.Gpr(10), 0), new(Storage.Gpr(11), 0)]), constructor, new Return(24)] };
            if (effects) join.Statements.Insert(2, new Call(18, CallKind.Direct, Expr.C(300, 64)));
            MachineFunction.AddEdge(entry, left); MachineFunction.AddEdge(entry, right);
            MachineFunction.AddEdge(left, join); MachineFunction.AddEdge(right, join);
            if (extraPredecessor) MachineFunction.AddEdge(entry, left);
            return new() { Entry = 0, Range = new(0, 28, CodeRegion.Managed, BoundaryEvidence.EhFrame)
                { ExceptionRegions = handler ? [new(0, 24, 32)] : [] }, Blocks = [entry, left, right, join] };
        }
        bool Split(MachineFunction function) => DelegateConstructorChoices.Split(function, c => c.Target == constructor.Target,
            e => e is Use u && methods.TryGetValue(u.Variable, out var value) ? value : e);
        var a = new Assertions();
        var sample = Diamond();
        a.True(Split(sample), "方法与接收者在同一组前驱上选择时拆分");
        a.True(!sample.Blocks[3].Statements.Contains(constructor), "共用构造被移回两臂");
        a.True(sample.Blocks[1].Statements[0] is Call { Arguments: [_, Use { Variable.Storage.Index: 10 }, Use method] } && method.Variable == firstMethod,
            "第一臂保持自身的接收者与方法配对");
        a.True(sample.Blocks[2].Statements[0] is Call { Arguments: [_, Use { Variable.Storage.Index: 11 }, Use otherMethod] } && otherMethod.Variable == secondMethod,
            "第二臂保持自身的接收者与方法配对");
        a.True(!Split(Diamond(effects: true)), "不跨越构造前的其他调用");
        a.True(!Split(Diamond(handler: true)), "异常区域尚未证明时不移动调用");
        a.True(!Split(Diamond(extraPredecessor: true)), "分支带其他入口时不复制构造");
        methods.Remove(secondMethod);
        a.True(!Split(Diamond()), "任一方法身份不明时保留原状");
        return a.Finish("delegate-constructor-choices");
    }
}
