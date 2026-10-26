using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;

namespace Cpp2CS.Tests;

internal static class SharedInterfaceTailsCheck
{
    [Command("interface-tails", "接口调用共享尾部的分支实参与拒绝边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        foreach (var mode in new[] { "split", "escaping", "handler", "unknown" })
        {
            var version = 0;
            Variable Fresh() => new(Storage.Gpr(8), ++version);
            var leftData = Fresh(); var rightData = Fresh(); var leftPointer = Fresh(); var rightPointer = Fresh();
            var target = Fresh(); var receiver = Fresh(); var argument = Fresh(); var result = Fresh();
            var leftReceiver = Fresh(); var rightReceiver = Fresh(); var leftArgument = Fresh(); var rightArgument = Fresh();
            Expr Use(Variable v) => new Use(v, v.Width);
            var start = new Block(0x1000) { End = 0x1010, Statements = [new Branch(0x1000, Expr.C(1, 1), 0x1020, 0x1040)] };
            var left = new Block(0x1020) { End = 0x1040, Statements = [
                new Call(0x1020, CallKind.Direct, Expr.C(0, 64)) { Op = new(OpKind.InterfaceInvokeData, 2), Defines = [leftData] },
                new Define(0x1024, leftPointer, new Load(Use(leftData), 64)), new Jump(0x1028, 0x1060)] };
            var right = new Block(0x1040) { End = 0x1060, Statements = [
                new Call(0x1040, CallKind.Direct, Expr.C(0, 64)) { Op = new(mode == "unknown" ? OpKind.NewObject : OpKind.InterfaceInvokeData, 3), Defines = [rightData] },
                new Define(0x1044, rightPointer, new Load(Use(rightData), 64)), new Jump(0x1048, 0x1060)] };
            var merge = new Block(0x1060) { End = 0x1080, Statements = [
                new Phi(0x1060, target, [leftPointer, rightPointer]), new Phi(0x1060, receiver, [leftReceiver, rightReceiver]),
                new Phi(0x1060, argument, [leftArgument, rightArgument]),
                new Call(0x1064, CallKind.Indirect, Use(target)) { Arguments = [Use(receiver), Use(argument)], Defines = [result] }, new Jump(0x1068, 0x1080)] };
            var done = new Block(0x1080) { End = 0x1090, Statements = [new Return(0x1080)] };
            MachineFunction.AddEdge(start, left); MachineFunction.AddEdge(start, right);
            MachineFunction.AddEdge(left, merge); MachineFunction.AddEdge(right, merge); MachineFunction.AddEdge(merge, done);
            if (mode == "escaping") done.Statements.Insert(0, new Define(0x1080, Fresh(), Use(result)));
            if (mode == "handler") left.Handler = merge;
            var function = new MachineFunction { Entry = start.Start, Range = new(start.Start, 0x1090, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [start, left, right, merge, done] };
            var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
            var changed = SharedInterfaceTails.SplitInvokes(function, e => e is Use u ? definitions.GetValueOrDefault(u.Variable, e) : e, Fresh);
            a.Equal(mode == "split", changed, $"共享接口尾部 {mode}");
            if (!changed) continue;
            var leftCall = left.Statements.OfType<Call>().Single(c => c.Kind == CallKind.Indirect);
            var rightCall = right.Statements.OfType<Call>().Single(c => c.Kind == CallKind.Indirect);
            a.True(leftCall.Target == Use(leftPointer) && leftCall.Arguments.SequenceEqual([Use(leftReceiver), Use(leftArgument)]), "左分支保留自身接口槽位、接收者和实参");
            a.True(rightCall.Target == Use(rightPointer) && rightCall.Arguments.SequenceEqual([Use(rightReceiver), Use(rightArgument)]), "右分支保留自身接口槽位、接收者和实参");
            a.True(!function.Blocks.Contains(merge) && done.Predecessors.Count == 2, "共享尾部移出并保留两条出口边");
        }
        return a.Finish("interface-tails");
    }
}
