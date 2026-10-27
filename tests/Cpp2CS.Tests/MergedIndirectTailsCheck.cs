using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using System.Reflection;

namespace Cpp2CS.Tests;

internal static class MergedIndirectTailsCheck
{
    [Command("merged-indirect-tails", "间接尾调用的参数来源与控制流边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var pointer = new Variable(Storage.Gpr(8), 3);
        var argument = new Variable(Storage.Gpr(0), 3);
        MachineFunction Sample(bool conditional = false, bool handler = false, bool extra = false)
        {
            var first = new Block(0x1010) { Statements = [new Jump(0x1010, 0x1030)] };
            var second = new Block(0x1020) { Statements = [new Jump(0x1020, 0x1030)] };
            var merge = new Block(0x1030) { Statements = [new Phi(0x1030, pointer, [pointer with { Version = 1 }, pointer with { Version = 2 }]),
                new Phi(0x1030, argument, [argument with { Version = 1 }, argument with { Version = 2 }]),
                new Call(0x1034, CallKind.TailIndirect, new Use(pointer, 64)) { Arguments = [new Use(argument, 64)], Sources = [Storage.Gpr(0)] }] };
            var entry = new Block(0x1000) { Statements = [new Branch(0x1000, Expr.C(1, 1), first.Start, second.Start)] };
            var exit = new Block(0x1040) { Statements = [new Return(0x1040)] };
            MachineFunction.AddEdge(entry, first);
            MachineFunction.AddEdge(entry, second);
            MachineFunction.AddEdge(first, merge);
            MachineFunction.AddEdge(second, merge);
            if (conditional)
            {
                first.Statements[^1] = new Branch(0x1010, Expr.C(1, 1), merge.Start, exit.Start);
                MachineFunction.AddEdge(first, exit);
            }
            if (handler) first.Handler = exit;
            if (extra) merge.Statements.Insert(2, new Store(0x1032, Expr.C(0, 64), Expr.C(1, 64)));
            var function = new MachineFunction { Entry = entry.Start, Range = new(0x1000, 0x1044, CodeRegion.Managed, BoundaryEvidence.EhFrame),
                Blocks = [entry, first, second, merge, exit] };
            function.Renumber();
            return function;
        }
        var a = new Assertions();
        var valid = Sample();
        a.True(MergedIndirectTails.Run(valid), "间接尾调用拆入各分支");
        foreach (var (address, version) in new[] { (0x1010UL, 1), (0x1020UL, 2) })
        {
            var block = valid.Blocks.Single(b => b.Start == address);
            a.True(block.Statements is [Call { Kind: CallKind.TailIndirect, Target: Use target, Arguments: [Use receiver] }]
                && target.Variable.Version == version && receiver.Variable.Version == version && !block.NormalSuccessors.Any(), "函数指针与实参来自同一入边");
        }
        a.True(valid.Blocks.All(b => b.Start != 0x1030), "原合流块删除");
        a.True(!MergedIndirectTails.Run(Sample(conditional: true)), "不在额外出口上执行尾调用");
        a.True(!MergedIndirectTails.Run(Sample(handler: true)), "不跨异常区域");
        a.True(!MergedIndirectTails.Run(Sample(extra: true)), "带其他操作的尾部保持原状");
        foreach (var mode in new[] { "valid", "unknown", "different-method", "not-generic", "escape" })
        {
            var function = Sample();
            var owner = new TypeDef { Index = 1, Assembly = "Test", Namespace = "Test", Name = "Container`1", Token = 1,
                Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
            MethodDef Method(int index) => new() { Index = index, Owner = owner, Name = "Remove", Token = (uint)index,
                Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1 };
            var definition = Method(1);
            foreach (var (address, version) in new[] { (0x1010UL, 1), (0x1020UL, 2) })
            {
                var block = function.Blocks.Single(b => b.Start == address);
                Expr symbol = new Symbol(SymbolKind.Method, new MethodRef(mode == "different-method" && version == 2 ? Method(2) : definition,
                    mode == "not-generic" ? [] : [new PrimitiveRef(version == 1 ? "First" : "Second")], []));
                if (mode == "unknown" && version == 2) symbol = new Unknown("未解析", 64);
                block.Statements.Insert(0, new Define(address, pointer with { Version = version }, symbol));
            }
            var merge = function.Blocks.Single(b => b.Start == 0x1030);
            merge.Statements[^1] = new Call(0x1034, CallKind.Tail, Expr.C(0x2000, 64)) {
                Arguments = [new Use(argument, 64), new Use(pointer, 64)], Sources = [Storage.Gpr(0), Storage.Gpr(1)] };
            if (mode == "escape") function.Blocks.First().Statements.Insert(0, new Define(0x1000, new Variable(Storage.Gpr(9), 1), new Use(pointer, 64)));
            a.Equal(mode == "valid", MergedIndirectTails.Run(function), $"{mode} 的泛型尾部边界");
            if (mode == "valid") foreach (var call in function.Blocks.SelectMany(b => b.Statements).OfType<Call>())
                a.True(call.Kind == CallKind.Tail && call.Arguments is [Use receiver, Use info] && receiver.Variable.Version == info.Variable.Version,
                    "具体接收者与 MethodInfo 保持同源");
        }
        return a.Finish("merged-indirect-tails");
    }
}
