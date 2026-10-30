using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class CheckedObjectAliasesCheck
{
    [Command("checked-object-aliases", "继承检查与判空后的对象类型及路径边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var type = new DefinitionRef(new TypeDef { Index = -1, Assembly = "Checks.Tests.dll", Namespace = "Tests", Name = "Derived",
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false }, []);
        foreach (var mode in new[] { "checked", "nullable", "bypass", "observed-flag", "handler" })
        {
            var original = new Use(new Variable(Storage.Gpr(0), 0), 64);
            var flag = new Variable(Storage.Temp(0), 1);
            var check = new Call(8, CallKind.Direct, Expr.C(0, 64))
                { Op = new(OpKind.TypeCheck, type), Arguments = [new Use(new(Storage.Gpr(9), 1), 64)], Defines = [flag] };
            var entry = new Block(0);
            if (mode != "nullable") entry.Statements.Add(new Call(4, CallKind.Direct, Expr.C(0, 64))
                { Op = new(OpKind.NullCheck, null), Arguments = [original] });
            entry.Statements.Add(check);
            var guard = new Block(12) { Statements = [new Call(12, CallKind.Direct, Expr.C(0, 64))
                { Op = new(OpKind.NullCheck, null), Arguments = [new Use(flag, 64)] }] };
            var read = new Define(16, new(Storage.Gpr(1), 1), new Load(new Binary(BinOp.Add, original, Expr.C(24, 64), 64), 32));
            var done = new Block(16) { Statements = [read] };
            if (mode == "observed-flag") done.Statements.Add(new Return(20) { Value = new Use(flag, 64) });
            MachineFunction.AddEdge(entry, guard); MachineFunction.AddEdge(guard, done);
            if (mode == "bypass") MachineFunction.AddEdge(entry, done);
            var function = new MachineFunction { Entry = 0, Range = new(0, 24, CodeRegion.Managed, default)
                { ExceptionRegions = mode == "handler" ? [new(0, 20, 28)] : [] }, Blocks = [entry, guard, done] };
            function.Renumber();
            var changes = CheckedObjectAliases.Read(function, c => c == check ? original : null);
            a.Equal(mode == "checked" ? 2 : mode == "bypass" ? 1 : 0, changes.Count, mode);
            if (mode == "checked")
                a.True(changes[check] is Call { Op.Kind: OpKind.IsInst, Arguments: [var value] } && value == original
                    && changes[read] is Define field && ExprMap.Walk(field.Value).OfType<Use>().Single().Variable == flag,
                    "保留原检查点，后续字段读取使用已通过判空的同一对象");
        }
        return a.Finish("checked-object-aliases");
    }
}
