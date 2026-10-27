using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
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
        return a.Finish("checked-class-values");
    }
}
