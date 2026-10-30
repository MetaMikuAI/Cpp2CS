using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Image;
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
        foreach (var mode in new[] { "grouped", "different-input", "slot", "return-value" })
        {
            var version = 0;
            Variable Fresh() => new(Storage.Temp(version++), 1);
            Expr Use(Variable value) => new Use(value, value.Width);
            var left = Fresh(); var right = Fresh(); var other = Fresh();
            var slowReceiver = Fresh(); var hitReceiver = Fresh(); var mergedReceiver = Fresh();
            var slowData = Fresh(); var hitData = Fresh(); var pointer = Fresh(); var state = Fresh();
            Block Block(ulong address, params Stmt[] statements) => new(address) { End = address + 16, Statements = statements.ToList() };
            var start = Block(0, new Branch(0, Expr.C(1, 1), 32, 128));
            var leftCheck = Block(32, new Branch(32, Expr.C(1, 1), 224, 64));
            var leftScan = Block(64, new Branch(64, Expr.C(1, 1), 256, 96));
            var leftFallback = Block(96, new Jump(96, 224));
            var rightCheck = Block(128, new Branch(128, Expr.C(1, 1), 224, 160));
            var rightScan = Block(160, new Branch(160, Expr.C(1, 1), 256, 192));
            var rightFallback = Block(192, new Jump(192, 224));
            var slow = Block(224, new Phi(224, slowReceiver, [left, left, right, right]),
                new Phi(224, state, [left, mode == "different-input" ? other : left, right, right]),
                new Call(228, CallKind.Direct, Expr.C(512, 64)) { Arguments = [Use(slowReceiver), Expr.C(0, 64), Expr.C(mode == "slot" ? 99UL : 1UL, 64)], Defines = [slowData] },
                new Jump(232, 288));
            var hit = Block(256, new Phi(256, hitReceiver, [left, right]), new Define(260, hitData, Expr.C(768, 64)), new Jump(264, 288));
            var merge = Block(288, new Phi(288, mergedReceiver, [slowReceiver, hitReceiver]), new Phi(288, pointer, [slowData, hitData]),
                new Call(292, CallKind.Indirect, Use(pointer)) { Arguments = [Use(mergedReceiver)] },
                new Return(300) { Value = mode == "return-value" ? Use(pointer) : null });
            MachineFunction.AddEdge(start, leftCheck); MachineFunction.AddEdge(start, rightCheck);
            MachineFunction.AddEdge(leftCheck, slow); MachineFunction.AddEdge(leftCheck, leftScan);
            MachineFunction.AddEdge(leftScan, hit); MachineFunction.AddEdge(leftScan, leftFallback); MachineFunction.AddEdge(leftFallback, slow);
            MachineFunction.AddEdge(rightCheck, slow); MachineFunction.AddEdge(rightCheck, rightScan);
            MachineFunction.AddEdge(rightScan, hit); MachineFunction.AddEdge(rightScan, rightFallback); MachineFunction.AddEdge(rightFallback, slow);
            MachineFunction.AddEdge(slow, merge); MachineFunction.AddEdge(hit, merge);
            var function = new MachineFunction { Entry = 0, Range = new(0, 320, CodeRegion.Managed, BoundaryEvidence.EhFrame),
                Blocks = [start, leftCheck, leftScan, leftFallback, rightCheck, rightScan, rightFallback, slow, hit, merge] };
            var changed = SharedInterfaceTails.Run(function, c => c.Target is Const { Value: 512 }, Fresh);
            a.Equal(mode == "grouped", changed, $"查找入边按接收者分组 {mode}");
            if (!changed) continue;
            var lookups = function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => c.Kind == CallKind.Direct).ToArray();
            a.True(lookups.Select(c => c.Arguments[0]).SequenceEqual([Use(right), Use(left)])
                || lookups.Select(c => c.Arguments[0]).SequenceEqual([Use(left), Use(right)]), "两个查找分别保留接收者");
            a.True(leftCheck.Successors[0] == leftFallback.Successors[0] && rightCheck.Successors[0] == rightFallback.Successors[0]
                && leftCheck.Successors[0] != rightCheck.Successors[0], "每个接收者的失败边汇入自身副本");
            a.True(new[] { leftCheck, leftScan, rightCheck, rightScan }.All(b => b.Statements[^1] is Branch branch
                && branch.Target == b.Successors[0].Start && branch.Fallthrough == b.Successors[1].Start), "保留条件分支的后继位置");
            a.Equal(2, function.Blocks.SelectMany(b => b.Statements).OfType<Return>().Count(), "两个调用各自返回 void");
        }
        return a.Finish("interface-tails");
    }
}
