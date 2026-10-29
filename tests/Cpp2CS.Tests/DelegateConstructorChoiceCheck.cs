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
        bool Split(MachineFunction function) => CallIdentityChoices.Split(function, c => c.Target == constructor.Target,
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
        var allocated = Diamond();
        var result = ((Use)constructor.Arguments[0]).Variable;
        var allocation = new Call(18, CallKind.Direct, Expr.C(400, 64))
            { Op = new(OpKind.NewObject, new DefinitionRef(owner, [])), Defines = [result], Results = [result.Storage] };
        allocated.Blocks[3].Statements.Insert(2, allocation);
        a.True(Split(allocated), "紧邻的分配与委托构造一起移到原入边");
        var resultPhi = allocated.Blocks[3].Statements.OfType<Phi>().Single(p => p.Target == result);
        for (var side = 0; side < 2; side++)
        {
            var calls = allocated.Blocks[side + 1].Statements.OfType<Call>().ToArray();
            a.True(calls is [var create, var construct] && create.Defines[0] == resultPhi.Sources[side]
                && construct.Arguments[0] == new Use(create.Defines[0], 64), "每条入边只构造自己分配的委托，结果按同一入边汇合");
        }
        var generic = Diamond();
        generic.Blocks[3].Statements.Remove(constructor);
        var resultVariable = new Variable(Storage.Gpr(0), 9);
        var sharedCall = constructor with { Defines = [resultVariable], Results = [resultVariable.Storage] };
        generic.Blocks[3].Statements.Insert(2, sharedCall);
        bool SplitGeneric(MachineFunction function, bool proven = true) => CallIdentityChoices.SplitGeneric(function, (c, i, m) => proven && i == 2,
            e => e is Use u && methods.TryGetValue(u.Variable, out var value) ? value : e);
        a.True(!SplitGeneric(generic, false), "MethodInfo 的 ABI 位置与原生入口尚未核对时不拆分");
        a.True(SplitGeneric(generic), "有返回值的分支方法调用沿原入边拆分");
        var merged = generic.Blocks[3].Statements.OfType<Phi>().Single(p => p.Target == resultVariable);
        for (var side = 0; side < 2; side++)
        {
            var branchCall = generic.Blocks[side + 1].Statements.OfType<Call>().Single();
            a.True(branchCall.Defines.Single() == merged.Sources[side]
                && branchCall.Arguments[1] == new Use(new(Storage.Gpr(side + 10), 0), 64), "返回值与调用接收者沿同一条边汇合");
        }
        a.True(!SplitGeneric(Diamond(effects: true)), "泛型调用不跨越其他副作用");
        a.True(!SplitGeneric(Diamond(handler: true)), "泛型调用不跨越异常区域");
        var absentResult = Diamond();
        absentResult.Blocks[3].Statements[2] = constructor with { Defines = [null!] };
        a.True(!SplitGeneric(absentResult), "缺失结果定义时保留调用，不生成无效 phi");
        methods.Remove(secondMethod);
        a.True(!Split(Diamond()), "任一方法身份不明时保留原状");
        return a.Finish("delegate-constructor-choices");
    }
}
