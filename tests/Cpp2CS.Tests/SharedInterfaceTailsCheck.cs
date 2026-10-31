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
        foreach (var mode in new[] { "split", "merged-result", "virtual", "escaping", "handler", "unknown" })
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
            if (mode == "virtual")
            {
                left.Statements[1] = new Define(0x1024, leftPointer, new Load(new Binary(BinOp.Add, new Load(Use(leftReceiver), 64), Expr.C(RuntimeLayout.ClassVtable, 64), 64), 64));
                right.Statements[1] = new Define(0x1044, rightPointer, new Load(new Binary(BinOp.Add, new Load(Use(rightReceiver), 64), Expr.C(RuntimeLayout.ClassVtable + RuntimeLayout.VirtualInvokeDataSize, 64), 64), 64));
                merge.Statements.Insert(4, new Call(0x1066, CallKind.Direct, Expr.C(0x2000, 64)) { Arguments = [Use(result)] });
            }
            MachineFunction.AddEdge(start, left); MachineFunction.AddEdge(start, right);
            MachineFunction.AddEdge(left, merge); MachineFunction.AddEdge(right, merge); MachineFunction.AddEdge(merge, done);
            var returned = Fresh();
            if (mode == "merged-result") done.Statements = [new Phi(done.Start, returned, [result]), new Return(done.Start + 4) { Value = Use(returned) }];
            if (mode == "escaping") done.Statements.Insert(0, new Define(0x1080, Fresh(), Use(result)));
            if (mode == "handler") left.Handler = merge;
            var function = new MachineFunction { Entry = start.Start, Range = new(start.Start, 0x1090, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [start, left, right, merge, done] };
            var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
            var changed = SharedInterfaceTails.SplitInvokes(function, e => e is Use u ? definitions.GetValueOrDefault(u.Variable, e) : e);
            a.Equal(mode is "split" or "merged-result" or "virtual", changed, $"共享接口尾部 {mode}");
            if (!changed) continue;
            var leftCall = left.Statements.OfType<Call>().Single(c => c.Kind == CallKind.Indirect);
            var rightCall = right.Statements.OfType<Call>().Single(c => c.Kind == CallKind.Indirect);
            a.True(leftCall.Target == Use(leftPointer) && leftCall.Arguments.SequenceEqual([Use(leftReceiver), Use(leftArgument)]), "左分支保留自身接口槽位、接收者和实参");
            a.True(rightCall.Target == Use(rightPointer) && rightCall.Arguments.SequenceEqual([Use(rightReceiver), Use(rightArgument)]), "右分支保留自身接口槽位、接收者和实参");
            a.True(!function.Blocks.Contains(merge) && done.Predecessors.Count == 2, "共享尾部移出并保留两条出口边");
            if (mode == "merged-result")
                a.True(done.Statements[0] is Phi exit && exit.Sources.SequenceEqual(done.Predecessors.Select(p => p.Statements.OfType<Call>().Last().Defines[0])), "出口按实际前驱汇合各副本的返回值");
        }
        foreach (var offset in new[] { RuntimeLayout.ClassVtable, RuntimeLayout.ClassVtable + 8 })
        {
            var leftClass = new Variable(Storage.Gpr(8), 1);
            var rightClass = leftClass with { Version = 2 };
            var joinedClass = leftClass with { Version = 3 };
            var receiver = new Use(new Variable(Storage.Gpr(0), 0), 64);
            var left = new Block(0x2000) { End = 0x2010, Statements = [new Define(0x2000, leftClass, new Load(receiver, 64)), new Jump(0x2004, 0x2040)] };
            var right = new Block(0x2020) { End = 0x2030, Statements = [new Define(0x2020, rightClass, new Load(receiver, 64)), new Jump(0x2024, 0x2040)] };
            var merge = new Block(0x2040) { End = 0x2050, Statements = [new Phi(0x2040, joinedClass, [leftClass, rightClass]),
                new Call(0x2044, CallKind.TailIndirect, new Load(new Binary(BinOp.Add, new Use(joinedClass, 64), Expr.C((ulong)offset, 64), 64), 64)) { Arguments = [receiver] }] };
            var start = new Block(0x1ff0) { End = 0x2000, Statements = [new Branch(0x1ff0, Expr.C(1, 1), left.Start, right.Start)] };
            MachineFunction.AddEdge(start, left); MachineFunction.AddEdge(start, right);
            MachineFunction.AddEdge(left, merge); MachineFunction.AddEdge(right, merge);
            var function = new MachineFunction { Entry = start.Start, Range = new(start.Start, 0x2050, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [start, left, right, merge] };
            var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
            var changed = SharedInterfaceTails.SplitInvokes(function, e => e is Use u ? definitions.GetValueOrDefault(u.Variable, e) : e);
            a.Equal(offset == RuntimeLayout.ClassVtable, changed, "类指针合流只按虚表方法指针槽拆分，不把 MethodInfo 槽当目标");
            if (changed)
                a.True(left.Statements[^1] is Call { Target: Load { Address: Binary { Left: Use klass } } } && klass.Variable == leftClass,
                    "分支调用使用本路径已读取的类指针");
        }
        foreach (var mode in new[] { "grouped", "different-input", "slot", "return-value", "slot-grouped", "slot-tail", "slot-mismatch" })
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
            var leftSlot = Fresh(); var rightSlot = Fresh();
            if (mode.StartsWith("slot-", StringComparison.Ordinal))
            {
                var selectedSlot = Fresh(); var leftOffset = Fresh(); var rightOffset = Fresh(); var mergedOffset = Fresh();
                leftCheck.Statements.Insert(0, new Define(32, leftSlot, Expr.C(6, 64)));
                rightCheck.Statements.Insert(0, new Define(128, rightSlot, Expr.C(4, 64)));
                leftScan.Statements.Insert(0, new Define(64, leftOffset, new Binary(BinOp.Add, new Use(other, 32), Expr.C(6, 32), 32)));
                rightScan.Statements.Insert(0, new Define(160, rightOffset, new Binary(BinOp.Add, new Use(other, 32), Expr.C(mode == "slot-mismatch" ? 5UL : 4UL, 32), 32)));
                slow.Statements[0] = new Phi(224, selectedSlot, [leftSlot, leftSlot, rightSlot, rightSlot]);
                slow.Statements[2] = ((Call)slow.Statements[2]) with { Arguments = [Use(left), Expr.C(0, 64), Use(selectedSlot)] };
                hit.Statements[0] = new Phi(256, mergedOffset, [leftOffset, rightOffset]);
                merge.Statements.RemoveAt(0);
                merge.Statements[1] = ((Call)merge.Statements[1]) with { Arguments = [Use(left)] };
                if (mode == "slot-tail")
                {
                    merge.Statements[1] = ((Call)merge.Statements[1]) with { Kind = CallKind.TailIndirect };
                    merge.Statements.RemoveAt(2);
                }
            }
            MachineFunction.AddEdge(start, leftCheck); MachineFunction.AddEdge(start, rightCheck);
            MachineFunction.AddEdge(leftCheck, slow); MachineFunction.AddEdge(leftCheck, leftScan);
            MachineFunction.AddEdge(leftScan, hit); MachineFunction.AddEdge(leftScan, leftFallback); MachineFunction.AddEdge(leftFallback, slow);
            MachineFunction.AddEdge(rightCheck, slow); MachineFunction.AddEdge(rightCheck, rightScan);
            MachineFunction.AddEdge(rightScan, hit); MachineFunction.AddEdge(rightScan, rightFallback); MachineFunction.AddEdge(rightFallback, slow);
            MachineFunction.AddEdge(slow, merge); MachineFunction.AddEdge(hit, merge);
            var function = new MachineFunction { Entry = 0, Range = new(0, 320, CodeRegion.Managed, BoundaryEvidence.EhFrame),
                Blocks = [start, leftCheck, leftScan, leftFallback, rightCheck, rightScan, rightFallback, slow, hit, merge] };
            var changed = SharedInterfaceTails.Run(function, c => c.Target is Const { Value: 512 }, Fresh);
            a.Equal(mode is "grouped" or "slot-grouped" or "slot-tail", changed, $"查找入边按接收者或槽位分组 {mode}");
            if (!changed) continue;
            var lookups = function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => c.Kind == CallKind.Direct).ToArray();
            if (mode is "slot-grouped" or "slot-tail")
                a.True(lookups.All(c => c.Arguments[0] == Use(left)) && lookups.Select(c => c.Arguments[2]).ToHashSet().SetEquals([Use(leftSlot), Use(rightSlot)]),
                    "同一接收者的两个查找保留各自槽位");
            else a.True(lookups.Select(c => c.Arguments[0]).SequenceEqual([Use(right), Use(left)])
                || lookups.Select(c => c.Arguments[0]).SequenceEqual([Use(left), Use(right)]), "两个查找分别保留接收者");
            a.True(leftCheck.Successors[0] == leftFallback.Successors[0] && rightCheck.Successors[0] == rightFallback.Successors[0]
                && leftCheck.Successors[0] != rightCheck.Successors[0], "每个接收者的失败边汇入自身副本");
            a.True(new[] { leftCheck, leftScan, rightCheck, rightScan }.All(b => b.Statements[^1] is Branch branch
                && branch.Target == b.Successors[0].Start && branch.Fallthrough == b.Successors[1].Start), "保留条件分支的后继位置");
            a.Equal(2, function.Blocks.SelectMany(b => b.Statements).Count(s => mode == "slot-tail" ? s is Call { Kind: CallKind.TailIndirect } : s is Return), "两个调用各自保留返回方式");
        }
        foreach (var following in new[] { false, true })
        {
            var leftAddress = new Variable(Storage.Gpr(1), 1);
            var rightAddress = leftAddress with { Version = 2 };
            var selected = leftAddress with { Version = 3 };
            var vector = new Variable(Storage.Vec(0), 1);
            var start = new Block(0) { End = 16, Statements = [new Branch(0, Expr.C(1, 1), 16, 32)] };
            var left = new Block(16) { End = 32, Statements = [new Define(16, leftAddress, new FrameAddress(-32)), new Jump(20, 48)] };
            var right = new Block(32) { End = 48, Statements = [new Define(32, rightAddress, new FrameAddress(-64)), new Jump(36, 48)] };
            var merge = new Block(48) { End = 80, Statements = [new Phi(48, selected, [leftAddress, rightAddress]),
                new Define(52, vector, new Load(new Use(selected, 64), 128)), new Store(56, new FrameAddress(-16), new Use(vector, 128)),
                new Return(60) { Value = new Use(vector, 32) }] };
            MachineFunction.AddEdge(start, left); MachineFunction.AddEdge(start, right);
            MachineFunction.AddEdge(left, merge); MachineFunction.AddEdge(right, merge);
            var function = new MachineFunction { Entry = 0, Range = new(0, 80, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [start, left, right, merge] };
            if (following)
            {
                var exit = new Block(80) { End = 96, Statements = [new Return(84) { Value = new Use(vector, 32) }] };
                merge.Statements[^1] = new Jump(60, exit.Start);
                MachineFunction.AddEdge(merge, exit);
                function.Blocks.Add(exit);
            }
            a.True(Cpp2CS.Machine.Ssa.TailDuplication.Run(function, b => b == merge, keepResults: following), "帧地址选择的终结尾部展开");
            a.True(following ? merge.Statements.First() is Phi { Target: var returned, Sources.Length: 2 } && returned == vector
                && new[] { left, right }.All(b => b.Successors.SequenceEqual([merge]))
                : new[] { left, right }.All(b => b.Successors.Count == 0 && b.Statements[^1] is Return), "独立返回或在原块汇合后续使用的结果");
            a.True(new[] { left, right }.All(b => b.Statements.OfType<Define>().Last().Target.Width == 128), "复制保持向量寄存器宽度");
            a.True(left.Statements.OfType<Define>().Last().Target != right.Statements.OfType<Define>().Last().Target, "副本定义互不覆盖");
            if (following) a.True(!Cpp2CS.Machine.Ssa.TailDuplication.Run(function, b => b == merge), "只剩结果合流时不重复展开");
        }
        return a.Finish("interface-tails");
    }
}
