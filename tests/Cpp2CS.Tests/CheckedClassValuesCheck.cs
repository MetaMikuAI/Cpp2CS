using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Image;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

internal static class CheckedClassValuesCheck
{
    [Command("checked-class-values", "类指针检查后的类型细化与入边边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        foreach (var mode in new[] { "valid", "unused", "open-class", "wrong-exception", "equal-test", "not-class-load" })
        {
            var type = new TypeDef { Index = 1, Assembly = "Test", Namespace = "Test", Name = "Item", Token = 1,
                Attributes = TypeAttributes.Public | (mode == "open-class" ? 0 : TypeAttributes.Sealed), IsValueType = false, IsEnum = false };
            var value = new Variable(Storage.Gpr(0), 0); var klass = new Variable(Storage.Gpr(8), 1);
            var cast = new Variable(Storage.Temp(1), 1); var merged = new Variable(Storage.Gpr(0), 2);
            Use Value() => new(value, 64);
            var entry = new Block(0x100) { Statements = [new Branch(0x100, Expr.C(1, 1), 0x110, 0x120)] };
            var checkedBlock = new Block(0x110) { Statements = [
                new Define(0x110, klass, new Load(Value(), 64)),
                new Call(0x114, CallKind.Direct, Expr.C(0, 64)) { Op = new(OpKind.ThrowIf, mode == "wrong-exception" ? "System.Exception" : "System.InvalidCastException"),
                    Arguments = [new Compare(mode == "equal-test" ? Cond.Eq : Cond.Ne, new Use(klass, 64), new Symbol(SymbolKind.Class, new DefinitionRef(type, [])))] },
                new Call(0x118, CallKind.Direct, Expr.C(0x200, 64)) { Arguments = [Value()] }, new Jump(0x11c, 0x130) ] };
            var bypass = new Block(0x120) { Statements = [new Jump(0x120, 0x130)] };
            var exit = new Block(0x130) { Statements = [new Phi(0x130, merged, [value, value]), new Return(0x134) { Value = new Use(merged, 64) }] };
            if (mode == "unused")
            {
                checkedBlock.Statements.RemoveAt(2);
                exit.Statements = [new Return(0x134)];
            }
            MachineFunction.AddEdge(entry, checkedBlock); MachineFunction.AddEdge(entry, bypass);
            MachineFunction.AddEdge(checkedBlock, exit); MachineFunction.AddEdge(bypass, exit);
            var function = new MachineFunction { Entry = entry.Start, Range = new(0x100, 0x140, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [entry, checkedBlock, bypass, exit] };
            function.Renumber();
            Expr Definition(Use use) => mode == "not-class-load" ? Expr.C(0, 64) : new Load(Value(), 64);
            a.Equal(mode == "valid", CheckedClassValues.Run(function, Definition, () => cast), $"{mode} 的类型证据");
            if (mode == "valid")
            {
                a.True(checkedBlock.Statements.OfType<Call>().Single(c => c.Op is null).Arguments is [Use actual] && actual.Variable == cast, "检查后的接收者使用细化值");
                a.True(exit.Statements[0] is Phi { Sources: var sources } && sources[0] == cast && sources[1] == value, "只细化经过检查的入边");
                a.True(checkedBlock.Statements[0] is Define { Value: Load { Address: Use original } } && original.Variable == value, "检查之前的类指针读取保持原值");
            }
        }
        foreach (var mode in new[] { "equal", "not-equal", "wrong-object", "bypass" })
        {
            var type = new DefinitionRef(new TypeDef { Index = 2, Assembly = "Test", Namespace = "Test", Name = "Value", Token = 2,
                Attributes = TypeAttributes.Public | TypeAttributes.Sealed, IsValueType = true, IsEnum = false }, []);
            var value = new Use(new Variable(Storage.Gpr(0), 0), 64);
            var klass = new Use(new Variable(Storage.Gpr(8), 1), 64);
            var unequal = mode == "not-equal";
            var entry = new Block(0x200) { Statements = [new Branch(0x204,
                new Compare(unequal ? Cond.Ne : Cond.Eq, klass, new Symbol(SymbolKind.Class, type)), unequal ? 0x220UL : 0x210UL, unequal ? 0x210UL : 0x220UL)] };
            var success = new Block(0x210) { Statements = [new Call(0x210, CallKind.Direct, Expr.C(0, 64)) { Op = new(OpKind.Unbox, null),
                Arguments = [mode == "wrong-object" ? new Use(new Variable(Storage.Gpr(1), 0), 64) : value] }, new Return(0x214)] };
            var failure = new Block(0x220) { Statements = [new Return(0x220)] };
            MachineFunction.AddEdge(entry, success); MachineFunction.AddEdge(entry, failure);
            if (mode == "bypass") MachineFunction.AddEdge(failure, success);
            var function = new MachineFunction { Entry = entry.Start, Range = new(0x200, 0x224, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [entry, success, failure] };
            function.Renumber();
            var expected = mode is "equal" or "not-equal";
            a.Equal(expected, CheckedClassValues.Run(function, _ => new Load(value, 64), () => new Variable(Storage.Temp(0), 1)), $"{mode} 的拆箱类型来源");
            a.Equal(expected, Equals(((Call)success.Statements[0]).Op?.Operand, type), "仅成功入边的同一对象获得拆箱类型");
        }
        foreach (var mode in new[] { "masked", "wrong-mask", "wrong-object" })
        {
            var type = new DefinitionRef(new TypeDef { Index = 3, Assembly = "Test", Namespace = "Test", Name = "Derived", Token = 3,
                Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false }, []);
            var obj = new Use(new(Storage.Gpr(0), 0), 64);
            var klass = new Variable(Storage.Gpr(8), 1);
            var flag = new Variable(Storage.Gpr(9), 1);
            var masked = new Variable(Storage.Gpr(10), 1);
            var result = new Variable(Storage.Gpr(11), 1);
            var block = new Block(0x300) { Statements = [
                new Define(0x300, klass, new Load(obj, 64)),
                new Call(0x304, CallKind.Direct, Expr.C(0, 64)) { Op = new(OpKind.TypeCheck, type), Arguments = [new Use(klass, 64)], Results = [flag.Storage], Defines = [flag] },
                new Define(0x308, masked, new Binary(BinOp.And, new Use(flag, 64), Expr.C(mode == "wrong-mask" ? 2UL : 1UL, 64), 64)),
                new Define(0x30c, result, new Select(new Compare(Cond.Ne, new Use(masked, 64), Expr.C(0, 64)), mode == "wrong-object" ? new Use(new(Storage.Gpr(1), 0), 64) : obj, Expr.C(0, 64), 64)),
                new Return(0x310) { Value = new Use(result, 64) }] };
            var function = new MachineFunction { Entry = block.Start, Range = new(0x300, 0x314, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [block] };
            function.Renumber();
            var definitions = block.Statements.OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
            a.Equal(mode == "masked", SuccessfulTypeCheckValuesPass.Run(function, u => definitions.GetValueOrDefault(u.Variable), () => new(Storage.Temp(0), 1)), $"{mode} 的对象选择");
            if (mode == "masked") a.True(block.Statements[3] is Call { Op.Kind: OpKind.IsInst, Defines: [var defined] } && defined == result, "选择结果保留变量身份并获得派生类型");
        }
        return a.Finish("checked-class-values");
    }
}
