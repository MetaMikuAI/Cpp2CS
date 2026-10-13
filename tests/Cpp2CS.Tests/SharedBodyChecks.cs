using System.Text.Json;
using Cpp2CS.Native;

public static class SharedBodyChecks
{
    public static void Run(Action<bool, string> check)
    {
        Instruction[] code = [new(0x100, "ret", "", [], false, false, "")];
        var method = new NativeMethod(0x100, "Example$$Run", "void", [], "");
        EvaluateStatement Call(ulong pc, string name) => new(pc, new InvocationExpression(name, null, [], false));
        var diamond = new LiftResult(method, code, new()
        {
            [0x100] = new(0x100, [], new NameExpression("condition"), [0x104, 0x108]),
            [0x104] = new(0x104, [Call(0x104, "First")], null, [0x10c]),
            [0x108] = new(0x108, [Call(0x108, "Second")], null, [0x10c]),
            [0x10c] = new(0x10c, [Call(0x10c, "Joined"), new ReturnStatement(0x110, null)], null, [])
        }, [], [], new NativeGraph(code, _ => false));
        var writer = new SemanticWriter(null!);
        var normal = writer.Structured(diamond, true);
        var awaited = SourceTree.Map(diamond, value => value is InvocationExpression c ? new AwaitExpression(c) : value);
        var async = writer.Structured(awaited, true);
        check(normal.Split("Joined()").Length == 2 && async.Split("Joined()").Length == 2,
            "普通与 await 分支共用结构化输出，合流业务只输出一次");
        check(normal == async.Replace("await ", ""), "await 包装不改变业务分支结构");

        var read = new AssignStatement(0x100, "snapshot", new SourceMemberExpression(new NameExpression("this"), "Field", "int"), "int");
        var sequence = diamond with { Blocks = new()
        {
            [0x100] = new(0x100, [read, Call(0x104, "Mutate"),
                new EvaluateStatement(0x108, new AwaitExpression(new InvocationExpression("Use", null, [new NameExpression("snapshot")], false))),
                new ReturnStatement(0x10c, null)], null, [])
        }};
        var normalized = ViewNormalizer.Normalize(sequence);
        var text = writer.Structured(normalized, true);
        check(normalized.Blocks[0x100].Statements[0] == read && text.IndexOf("this.Field", StringComparison.Ordinal) < text.IndexOf("Mutate()", StringComparison.Ordinal) &&
            text.Contains("await Use(snapshot);"), "字段快照不越过有副作用调用移入 await 参数");
        var renamed = SourceTree.Map(sequence, value => value is NameExpression { Name: "snapshot" } ? new NameExpression("captured") : value);
        check(JsonSerializer.Serialize(SemanticData.Function(renamed)).Contains("captured"), "await 子树参与语义遍历及序列化");
        var unknown = SourceTree.Map(sequence, value => value is NameExpression { Name: "snapshot" } ? new UnknownExpression("unbound") : value);
        SemanticValidation.Check(unknown);
        check(unknown.Problems.Any(p => p.Contains("unbound")), "await 包装不能掩盖未知输入");
    }
}
