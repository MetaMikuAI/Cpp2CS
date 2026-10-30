using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Image;
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
        MachineFunction Indirect(bool effects = false, bool handler = false)
        {
            var function = Diamond(effects, handler);
            var shared = function.Blocks[3];
            var info = new Variable(Storage.Gpr(3), 1);
            var call = constructor with { Kind = CallKind.Indirect, Target = new Use(identity, 64),
                Arguments = [new Use(receiver, 64), new Use(info, 64)], Defines = [resultVariable], Results = [resultVariable.Storage] };
            shared.Statements[shared.Statements.IndexOf(constructor)] = call;
            shared.Statements.Insert(shared.Statements.IndexOf(call), new Define(19, info,
                new Load(new Binary(BinOp.Add, new Use(receiver, 64), Expr.C(0x28, 64), 64), 64)));
            return function;
        }
        var indirect = Indirect();
        a.True(CallIdentityChoices.SplitIndirect(indirect), "不同函数指针的共用间接调用沿原入边拆分");
        var returned = indirect.Blocks[3].Statements.OfType<Phi>().Single(p => p.Target == resultVariable);
        for (var side = 0; side < 2; side++)
        {
            var load = indirect.Blocks[side + 1].Statements.OfType<Define>().Single();
            var call = indirect.Blocks[side + 1].Statements.OfType<Call>().Single();
            a.True(call.Target == new Use(side == 0 ? firstMethod : secondMethod, 64)
                && call.Arguments[0] == new Use(new(Storage.Gpr(side + 10), 0), 64)
                && call.Arguments[1] == new Use(load.Target, 64)
                && call.Defines.Single() == returned.Sources[side], "每条入边的函数、实例、元数据与返回值不混用");
            a.True(load.Value is Load { Address: Binary { Left: Use input } } && input.Variable.Storage.Index == side + 10,
                "元数据只在原调用路径读取对应实例");
        }
        a.True(!CallIdentityChoices.SplitIndirect(Indirect(effects: true)), "间接调用不越过共享块中的其他调用");
        a.True(!CallIdentityChoices.SplitIndirect(Indirect(handler: true)), "间接调用不跨异常区域");
        var branching = Indirect();
        MachineFunction.AddEdge(branching.Blocks[1], branching.Blocks[2]);
        a.True(!CallIdentityChoices.SplitIndirect(branching), "前驱有其他出口时不能提前执行间接调用");
        var fieldFunction = Diamond();
        var fieldJoin = fieldFunction.Blocks[3];
        fieldJoin.Statements.Remove(constructor);
        var fieldRead = new Define(20, resultVariable, new Ir.Convert(ConvKind.ZeroExtend,
            new Load(new Binary(BinOp.Add, new Use(receiver, 64), Expr.C(16, 64), 64), 32), 64));
        fieldJoin.Statements.Insert(2, fieldRead);
        var conditional = fieldFunction.Blocks[1];
        var unrelated = fieldFunction.Blocks[2];
        MachineFunction.AddEdge(conditional, unrelated);
        conditional.Statements[^1] = new Branch(4, Expr.C(1, 32), fieldJoin.Start, unrelated.Start);
        a.True(!JoinedFieldReads.Run(fieldFunction, _ => false), "缺少异型引用证据时不展开字段读取");
        a.True(JoinedFieldReads.Run(fieldFunction, p => p.Target == receiver), "异型引用上的共用读取按原入边展开");
        var fieldPhi = fieldJoin.Statements.OfType<Phi>().Single(p => p.Target == resultVariable);
        a.True(conditional.Statements.All(s => s is not Define)
            && conditional.Successors.Contains(unrelated), "条件前驱的其他路径不提前读取字段");
        for (var side = 0; side < 2; side++)
        {
            var edge = fieldJoin.Predecessors[side];
            a.True(edge.Statements[0] is Define d && d.Target == fieldPhi.Sources[side]
                && ExprMap.Walk(d.Value).OfType<Use>().Single().Variable.Storage.Index == side + 10,
                "字段结果与所选对象保持同一入边");
        }
        foreach (var guarded in new[] { true, false })
        {
            var delayed = Diamond();
            var mergedBlock = delayed.Blocks[3];
            mergedBlock.Statements.Remove(constructor);
            mergedBlock.Statements.RemoveAll(s => s is Return);
            var check = new Call(18, CallKind.Direct, Expr.C(400, 64))
                { Op = guarded ? new(OpKind.NullCheck, null) : null, Arguments = [new Use(receiver, 64)] };
            mergedBlock.Statements.Add(check);
            var next = new Block(20) { Statements = [fieldRead, new Return(24)] };
            MachineFunction.AddEdge(mergedBlock, next);
            delayed.Blocks.Add(next);
            a.Equal(guarded, JoinedFieldReads.Run(delayed, p => p.Target == receiver), "只跨唯一直线链的判空，不跨其他调用");
            if (guarded)
                a.True(mergedBlock.Predecessors.All(p => p.Statements is [Call { Op.Kind: OpKind.NullCheck }, Define, Jump]),
                    "每条原入边均先判空再读取字段");
        }
        var addressFunction = Diamond();
        var addressJoin = addressFunction.Blocks[3];
        addressJoin.Statements.Remove(constructor);
        addressJoin.Statements.Insert(2, fieldRead with { Value = new Load(new Use(receiver, 64), 32) });
        a.True(JoinedFieldReads.Run(addressFunction, p => p.Target == receiver), "已证明的字段地址合流保持原分支来源");
        a.True(addressJoin.Predecessors.SelectMany(p => p.Statements).OfType<Define>().All(d => d.Value is Load { Address: Use u }
            && u.Variable.Storage.Index is 10 or 11), "共享地址读取沿原入边替换，未提前读取其他路径");
        foreach (var nested in new[] { "constant", "dynamic", "narrow" })
        {
            var nestedFunction = Diamond();
            var nestedJoin = nestedFunction.Blocks[3];
            nestedJoin.Statements.Remove(constructor);
            var width = nested == "narrow" ? 32 : 64;
            Expr displacement = nested == "dynamic" ? new Use(identity, width) : Expr.C(4, width);
            var inner = new Binary(BinOp.Add, new Use(receiver, width), Expr.C(28, width), width);
            nestedJoin.Statements.Insert(2, fieldRead with { Value = new Load(new Binary(BinOp.Add, inner, displacement, width), 32) });
            a.Equal(nested == "constant", JoinedFieldReads.Run(nestedFunction, p => p.Target == receiver), "只展开等宽常量字段地址链");
            if (nested == "constant")
                a.True(nestedJoin.Predecessors.SelectMany(p => p.Statements).OfType<Define>().All(d => d.Value is Load
                    { Address: Binary { Left: Binary { Left: Use u, Right: Const { Value: 28 } }, Right: Const { Value: 4 } } }
                    && u.Variable.Storage.Index is 10 or 11), "每条入边保留原地址运算与字节偏移");
        }
        foreach (var effects in new[] { false, true })
        {
            var writing = Diamond(effects);
            var shared = writing.Blocks[3];
            var store = new Store(20, new Use(receiver, 64), new Use(identity, 64));
            shared.Statements[shared.Statements.IndexOf(constructor)] = store;
            a.Equal(!effects, CallIdentityChoices.SplitStores(writing), "共享写入只在没有前置副作用时按地址入边展开");
            if (!effects)
                for (var side = 0; side < 2; side++)
                    a.True(writing.Blocks[side + 1].Statements.OfType<Store>().Single() is
                        { Target: Use address, Value: Use value } && address.Variable.Storage.Index == side + 10
                        && value.Variable == (side == 0 ? firstMethod : secondMethod), "写入地址与值沿同一原入边配对");
        }
        return a.Finish("delegate-constructor-choices");
    }
}
