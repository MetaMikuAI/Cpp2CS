using Cpp2CS.Native;
using System.Text.Json;

public static class NativeChecks
{
    public static void ExceptionBoundaries(Action<bool, string> check, string config)
    {
        using var session = new RecoverySession(JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(config))!);
        var result = session.Recover(0x570e728);
        var boundary = UnwindBoundary.Read(session.Image, result.Method.Address);
        check(boundary.End == 0x570e970 && result.Instructions[^1].Address == 0x570e96c, "真实 FDE 边界不扩展进下一个方法");
        check(result.Graph.Problems.Length == 0 && result.Graph.TopologicalOrder() is not null && result.Blocks.Count > 0, "真实异常出口不会伪造越界或循环");
        var flow = result.Ssa!.Program.Flow;
        check(flow.Problems.Length == 0 && flow.Cycles.Length == 0, "SSA 控制流与基本块图均无越界和循环");
        foreach (var pc in new ulong[] { 0x570e95c, 0x570e960, 0x570e96c })
            check(flow.Nodes.Single(n => n.Instruction.Address == pc).Edges is [{ Kind: "exception-unwind", Target: null }], $"0x{pc:x} 只保留异常出口");
        foreach (var pc in new ulong[] { 0x570e928, 0x570e93c, 0x570e964 })
            check(flow.Nodes.Single(n => n.Instruction.Address == pc).Edges.Any(e => e.Kind == "normal-return" && e.Target == pc + 4), $"0x{pc:x} 普通调用或异常工厂正常返回");
        var statements = result.Blocks.Values.SelectMany(b => b.Statements).ToArray();
        check(statements.OfType<ThrowStatement>().Any(s => s.Type == "System.IndexOutOfRangeException"), "数组越界恢复为抛异常语义");
        check(statements.OfType<CallStatement>().Any(s => s.Name == "Runtime.RaiseException" && s.NoReturn && s.Arguments.Length == 1), "通用抛异常入口保留异常对象且不返回");
    }
    public static void Constructors(Action<bool, string> check, string config)
    {
        using var session = new RecoverySession(JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(config))!);
        foreach (var address in new ulong[] { 0x52061c0, 0x52067e8, 0x5206a44 })
        {
            var result = session.Recover(address);
            check(result.Problems.Count == 0, $"0x{address:x}: 构造函数无未解析语义");
            if (address != 0x52067e8) continue;
            var statements = result.Blocks.Values.SelectMany(b => b.Statements).ToArray();
            var stores = statements.OfType<StoreStatement>().Where(s => s.Target is MemberExpression).ToArray();
            foreach (var (offset, name) in new[] { (0x48, "userId"), (0x50, "mysekaiOwnerUserId"), (0x58, "userMysekaiRoomRequest") })
                check(stores.Any(s => s.Target is MemberExpression { Receiver: NameExpression { Name: "this" } } field && field.Field.Offset == offset &&
                    field.DisplayName == name && s.Value is NameExpression parameter && parameter.Name == name), $"写回寻址保留 {name} 的原对象、偏移和参数");
            check(statements.OfType<CallStatement>().Any(c => c.Name == "Runtime.InitializeClass"), "类初始化行为显式保留");
            check(statements.OfType<CallStatement>().Any(c => c.Address == 0x5206880 && c.Name == "Runtime.GCWriteBarrier"), "运行时尾调用保留写屏障行为");
            check(result.Graph.Blocks.Values.Single(b => b.Instructions[^1].Address == 0x5206880).Successors.Length == 0, "helper 尾调用没有函数内后继");
        }
    }
    public static void Run(Action<bool, string> check)
    {
        Instruction I(ulong address, string mnemonic, params Operand[] operands) => new(address, mnemonic, "", operands, false, false, "");
        Operand Target(long address) => new(2, null, address, null, null, 0, 0, 0, 0);
        Operand Register(string name) => new(1, name, 0, null, null, 0, 0, 0, 0);
        NativeGraph Graph(params Instruction[] instructions) => new(instructions, _ => false);
        var callGraph = Graph(I(0x100, "bl", Target(0x200)), I(0x104, "ret"));
        check(UnusedReceiver.Prove(callGraph, "x1", _ => ["x0"]), "已知 helper 仅读 X0，调用破坏可证明入口 X1 未使用");
        check(!UnusedReceiver.Prove(callGraph, "x1", _ => ["x0", "x1"]), "ABI 参数读取发生在调用破坏之前");
        check(!UnusedReceiver.Prove(callGraph, "x1"), "未知调用不能证明入口参数未读");
        check(UnusedReceiver.Prove(Graph(I(0x100, "mov", Register("w1"), Register("w2")), I(0x104, "ret")), "x1"), "W 覆盖使用统一机器效果清除入口 X 参数");
        check(!UnusedReceiver.Prove(Graph(I(0x100, "mov", Register("w2"), Register("w1")), I(0x104, "mov", Register("w1"), Register("w0")), I(0x108, "ret")), "x1"), "子寄存器读取不能被后续覆盖隐藏");
        check(!UnusedReceiver.Prove(Graph(I(0x100, "cbz", Register("w2"), Target(0x10c)), I(0x104, "mov", Register("w1"), Register("w0")),
            I(0x108, "ret"), I(0x10c, "mov", Register("w0"), Register("w1")), I(0x110, "ret")), "x1"), "只有一条分支覆盖参数时不能证明未读");
        check(!UnusedReceiver.Prove(Graph(I(0x100, "unsupported"), I(0x104, "mov", Register("w1"), Register("w0")), I(0x108, "ret")), "x1"), "未知机器效果阻止未读参数证明");
        var loop = new NativeGraph([I(0x100, "b", Target(0x100))], _ => false);
        check(loop.TopologicalOrder() is null, "含回边的图不生成无环排序");
        check(new NaturalLoops(loop).Loops is [{ Header: 0x100 }] && new NaturalLoops(loop).Reducible, "自回边识别为自然循环");
        var irreducible = new NaturalLoops(1, new() { [1] = [2, 3], [2] = [3], [3] = [2, 4], [4] = [] });
        check(!irreducible.Reducible, "多入口强连通区域不视为自然循环");
        var outside = new NativeGraph([I(0x100, "b", Target(0x200))], _ => false);
        check(outside.Problems.Length == 1, "候选函数范围不是无条件可信边界");
        check(outside.Problems[0].Contains("0x100: 分支") && outside.Problems[0].Contains("[0x100, 0x104)"), "范围错误报告来源指令、边类型和函数范围");
        var unknownCall = new NativeGraph([I(0x100, "bl", Target(0x200))], _ => false);
        check(unknownCall.Problems is [var callProblem] && callProblem.Contains("调用返回") && callProblem.Contains("被调函数 0x200"), "未知末尾调用提示核对不返回属性，不伪造终止");
        var throwingCall = new NativeGraph([I(0x100, "bl", Target(0x200))], pc => pc == 0x200);
        check(throwingCall.Problems.Length == 0 && throwingCall.Blocks[0x100].Successors.Length == 0, "不返回调用不产生越界返回边");
        var ordinaryCall = new NativeGraph([I(0x100, "bl", Target(0x200)), I(0x104, "ret")], _ => false);
        check(ordinaryCall.Problems.Length == 0 && ordinaryCall.Blocks[0x100].Instructions.Length == 2, "普通外部调用仍保留调用后的返回指令");
        var tail = new NativeGraph([I(0x100, "b", Target(0x200))], _ => false, pc => pc == 0x200);
        check(tail.Problems.Length == 0 && tail.Blocks[0x100].Successors.Length == 0, "已知外部跳转作为尾调用终止，不作为函数内分支");
        check(ManagedNames.SplitGeneric("Example.<Wait>d__1").Name == "Example.<Wait>d__1", "状态机名称中的尖括号不是泛型参数");
        check(ManagedNames.SplitGeneric("Example.<>c__DisplayClass0_0").Arguments.Length == 0, "闭包类型名称不会被拆成泛型");
        check(ManagedNames.SplitGeneric("Example.List<System.Int32>").Arguments.Single() == "System.Int32", "泛型实参保持类型身份");
        var graph = new NativeGraph([I(0x100, "ret")], _ => false);
        var field = new HeaderField("field", "int32_t", 16, 4, "Example_Fields");
        var receiver = new NameExpression("arg");
        var read = new AssignStatement(0x108, "value", new MemberExpression(receiver, field, "Field", "System.Int32"), "int32_t");
        var blocks = new Dictionary<ulong, LiftedBlock>
        {
            [0x100] = new(0x100, [], new BinaryExpression("is", receiver, new NameExpression("null")), [0x104, 0x108]),
            [0x104] = new(0x104, [new ThrowStatement(0x104, "System.NullReferenceException")], null, []),
            [0x108] = new(0x108, [read, new ReturnStatement(0x10c, new CapturedExpression("value", read.Value))], null, [])
        };
        var method = new NativeMethod(0x100, "Example$$Read", "int32_t", [], "");
        var result = new LiftResult(method, [], blocks, [], [], graph);
        var normalized = ViewNormalizer.Normalize(result);
        check(normalized.Proofs.Any(p => p.Rule == "ViewImplicitNullCheck"), "紧邻解引用可承接显式空引用检查");
        check(result.Blocks.Count == 3 && result.Blocks[0x108].Statements.Count == 2, "视图简化不修改原始 IR");
        blocks[0x108] = blocks[0x108] with { Statements = [new CallStatement(0x108, "Effect", [], null, "void", false, null), read, new ReturnStatement(0x110, null)] };
        check(!ViewNormalizer.Normalize(result).Proofs.Any(p => p.Rule == "ViewImplicitNullCheck"), "有调用副作用隔开的空检查不能删除");
        var unknown = new CapturedExpression("saved", new UnknownExpression("missing"));
        var invalid = result with { Blocks = new() { [0x100] = new(0x100,
            [new CallStatement(0x104, "Use", [], null, "void", true, unknown), new ReturnStatement(0x108, unknown)],
            new BinaryExpression("==", unknown, new ConstantExpression(0)), []) }, Problems = [] };
        SemanticValidation.Check(invalid);
        check(invalid.Problems.Count == 3, "未知值流入分支、调用接收者和返回值均报告未决");
        var phi = new PhiExpression("joined", "int32_t", [new(0x104, new ConstantExpression(1)), new(0x108, new ConstantExpression(2))]);
        var merge = result with { Blocks = new()
        {
            [0x100] = new(0x100, [], new BinaryExpression("==", receiver, new ConstantExpression(0)), [0x104, 0x108]),
            [0x104] = new(0x104, [], null, [0x10c]),
            [0x108] = new(0x108, [], null, [0x10c]),
            [0x10c] = new(0x10c, [new ReturnStatement(0x10c, phi)], null, [])
        }, Problems = [], Proofs = [] };
        PhiLowering.Apply(merge);
        check(merge.Blocks[0x104].Statements is [SetLocalStatement { Value: ConstantExpression { Value: 1 } }] &&
            merge.Blocks[0x108].Statements is [SetLocalStatement { Value: ConstantExpression { Value: 2 } }], "Phi 赋值保持前驱与取值的对应关系");
        check(merge.Blocks[0x100].Statements is [DeclareStatement] && merge.Blocks[0x10c].Statements is [ReturnStatement { Value: NameExpression { Name: "joined" } }], "Phi 声明与合流使用分离，不生成默认值");
    }
}
