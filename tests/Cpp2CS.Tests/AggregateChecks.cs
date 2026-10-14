using System.Text.Json;
using Cpp2CS.Native;

public static class AggregateChecks
{
    public static void Native(Action<bool, string> check, string config)
    {
        var inputs = JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(config))!;
        using var managed = new ManagedNames(inputs.ManagedAssembly);
        check(managed.ReturnOf("Method$ImprovedLinq.FirstOrDefault<MasterMysekaiStamina>()") == "MasterMysekaiStamina", "占位程序集缺失的依赖引用与泛型共同返回类型恢复");
        using var session = new RecoverySession(inputs);
        var result = session.Recover(0x570e970);
        session.Save(result, "artifacts/recovered");
        check(result.Problems.Count == 0, "真实元组方法无未恢复语义");
        var text = new SemanticWriter(session.Symbols).Structured(session.View(result));
        check(!text.Contains("UNKNOWN") && !text.Contains("Runtime.Bits"), "元组、字段和布尔条件无未解析位片段");
        check(result.Proofs.Count(p => p.Rule == "ValueConstructor") == 2, "两个栈构造调用均更新结构体存储");
        check(result.Proofs.Any(p => p.Rule == "UnusedReceiver"), "真实被调函数证明不读取入口接收者");
        var calls = result.Blocks.Values.SelectMany(b => b.Statements).OfType<CallStatement>().ToArray();
        var rates = calls.Where(c => c.Name == "UpdateStaminaGageRate").ToArray();
        string Shape(Expression expression) => JsonSerializer.Serialize(SemanticData.Expression(expression));
        check(rates.Length == 2 && Shape(rates[0].Arguments[2]) == Shape(rates[1].Arguments[2]), "两次进度条调用共享原始增强体力比例");
        check(Shape(rates[1].Arguments[1]) != Shape(rates[0].Arguments[1]) && Shape(rates[1].Arguments[3]) != Shape(rates[0].Arguments[3]), "转换后的普通和 boost 比例保持独立来源");
        bool LeBit(Expression value) => value switch
        {
            CapturedExpression captured => LeBit(captured.Value),
            OperationExpression { Operation: ValueOperation.IntegerCast, Arguments: [var inner], Type: var type } when IntegerProjection.Width(type) > 0 => LeBit(inner),
            OperationExpression { Operation: ValueOperation.Select, Arguments: [BinaryExpression { Operator: "<=" }, ConstantExpression { Value: 1 }, ConstantExpression { Value: 0 }] } => true,
            _ => false
        };
        var active = calls.Single(c => c.Name == "SetActive").Arguments[0];
        check(active is BinaryExpression { Operator: "<=" } || active is BinaryExpression { Operator: "!=", Right: ConstantExpression { Value: 0 } } converted && LeBit(converted.Left),
            "CSET 有符号 LE 的 0/1 值经整数转换后仍作为同一布尔参数");
        check(text.Contains("masterMysekaiStamina.maxStamina") && text.Contains("this.ConvertLiveBonusToBoostStamina"), "泛型字段布局与省略接收者恢复");
        Operand R(string name) => new(1, name, 0, null, null, 0, 0, 0, 0);
        Instruction I(ulong address, string mnemonic, params Operand[] operands) => new(address, mnemonic, "", operands, false, false, "");
        NativeGraph Graph(params Instruction[] instructions) => new(instructions, _ => false);
        check(UnusedReceiver.Prove(Graph(I(0x100, "mov", R("w0"), R("w2")), I(0x104, "ret"))), "先覆盖 W0 证明入口 X0 未使用");
        check(!UnusedReceiver.Prove(Graph(I(0x100, "mov", R("x1"), R("x0")), I(0x104, "ret"))), "读取入口接收者禁止替代");
        check(!UnusedReceiver.Prove(Graph(I(0x100, "bl", new Operand(2, null, 0x200, null, null, 0, 0, 0, 0)), I(0x104, "ret"))), "未知调用不能当作接收者覆盖证明");
    }
}
