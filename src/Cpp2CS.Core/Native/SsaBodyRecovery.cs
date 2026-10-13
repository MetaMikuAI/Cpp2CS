namespace Cpp2CS.Native;

public sealed record SsaBodyResult(LiftResult? Body, string[] Problems);

// 普通业务体的投影。未覆盖的效果保留诊断，由调用方选择已有恢复路径。
public static class SsaBodyRecovery
{
    public static SsaBodyResult Recover(MethodAnalysis analysis, ManagedNames managed, HeaderLayout layouts, Symbols symbols)
    {
        var problems = analysis.Ssa.Problems.Concat(analysis.Flow.Problems).ToList();
        if (analysis.Machine.Boundary.Unsupported is { } unsupported) problems.Add(unsupported);
        if (analysis.Machine.Boundary.Lsda is not null) problems.Add("普通 SSA 业务体尚未投影局部异常区域");
        if (analysis.Flow.Cycles.Length != 0) problems.Add("普通 SSA 业务体尚未结构化循环");
        if (problems.Count != 0) return new(null, problems.ToArray());
        var semantics = analysis.Semantics;
        var proofs = new List<string>();
        var expressions = new ManagedExpressionBuilder(semantics, managed, layouts, symbols, problems.Add, proofs.Add, analysis.Method);
        expressions.CaptureFieldReads(_ => true);
        foreach (var load in analysis.Ssa.Values.Where(v => v.Operation == "load"))
            if (SsaSemantics.AddressParts(semantics.Resolve(load.Inputs[1])).Root.Kind != "stack" &&
                semantics.Resolve(load.Id).Kind is not ("field" or "constant" or "metadata" or "metadata-slot"))
                problems.Add($"0x{load.Address:x}: 内存读取效果尚未投影");
        var calls = semantics.Calls().ToDictionary(c => c.Address);
        var stores = semantics.Stores().GroupBy(s => s.Address).ToDictionary(g => g.Key, g => g.ToArray());
        var instructions = analysis.Ssa.Instructions.ToDictionary(i => i.Address);
        var blocks = new Dictionary<ulong, LiftedBlock>();
        foreach (var call in calls.Values.Where(c => c.Kind is "managed" or "virtual"))
        {
            expressions.Results[call.Value] = "call_" + call.Address.ToString("x");
            if (call.ReturnType == "bool") expressions.BooleanResults.Add(expressions.Results[call.Value]);
        }
        foreach (var node in analysis.Flow.Nodes.Where(n => n.Reachable))
        {
            var pc = node.Instruction.Address;
            var source = instructions[pc];
            var statements = expressions.ReadStatements(pc);
            if (calls.TryGetValue(pc, out var call))
            {
                if (call.Kind is "managed" or "virtual")
                {
                    if (call.Arguments.Any(a => SsaSemantics.Contains(a, "stack"))) problems.Add($"0x{pc:x}: 普通 SSA 调用的局部存储效果尚未投影");
                    var expression = expressions.Call(call, statements);
                    statements.Add(call.ReturnType == "void" ? new EvaluateStatement(pc, expression) :
                        new AssignStatement(pc, expressions.Results[call.Value], expression, call.ReturnType!));
                }
                else if (call is { Kind: "runtime", Name: "ThrowNullReference" }) statements.Add(new ThrowStatement(pc, "System.NullReferenceException"));
                else if (call is { Kind: "runtime", Name: "WriteBarrier", Arguments: [var slot] })
                {
                    if (Field(slot, 8) is { } field)
                        statements.Add(new CallStatement(pc, "Runtime.GCWriteBarrier", [new AddressOfExpression(field)], null, null, false, null));
                }
                else problems.Add($"0x{pc:x}: 调用效果尚未投影：{call.Name}");
            }
            foreach (var store in stores.GetValueOrDefault(pc, []))
            {
                if (SsaSemantics.AddressParts(store.AddressValue).Root.Kind == "stack") continue;
                if (Field(store.AddressValue, store.Value.Width / 8) is { } field)
                    statements.Add(new StoreStatement(pc, field, expressions.TypedValue(store.Value, field.Type)));
            }
            foreach (var effect in source.Effects.Select(semantics.Raw).Where(v => v.Operation == "return"))
            {
                Expression? value = null;
                if (analysis.Method.ReturnType != "void")
                {
                    var shape = layouts.Shape(analysis.Method.ReturnType);
                    if (shape.Kind != Cpp2CS.Abi.ShapeKind.Integer || shape.Size > 8 || effect.Inputs.Length == 0)
                        problems.Add($"0x{pc:x}: 普通 SSA 返回布局尚未投影");
                    else value = expressions.TypedValue(SsaSemantics.Slice(semantics.Resolve(effect.Inputs[0]), 0, shape.Size * 8), analysis.Method.ReturnType);
                }
                statements.Add(new ReturnStatement(pc, value));
            }
            var successors = node.Edges.Where(e => e.Kind is "next" or "branch" or "normal-return" or "taken" or "not-taken")
                .Select(e => e.Target!.Value).ToArray();
            if (node.Edges.Any(e => e.Kind is "tail-call" or "indirect-transfer")) problems.Add($"0x{pc:x}: 普通 SSA 尾调用尚未投影");
            blocks.Add(pc, new(pc, statements, source.Condition is { } condition ? expressions.Value(semantics.Resolve(condition)) : null, successors));
        }
        var body = new LiftResult(analysis.Method, analysis.Machine.Instructions, blocks, problems,
            proofs.Select(p => new Proof(analysis.Method.Address, "SsaBody", p)).ToList(), new NativeGraph(analysis.Machine.Instructions, _ => false))
        { RecoveryPath = "ssa" };
        SemanticValidation.Check(body);
        return new(problems.Count == 0 ? body : null, problems.Distinct().ToArray());

        SourceMemberExpression? Field(SemanticTerm address, int bytes)
        {
            var (root, offset) = SsaSemantics.AddressParts(address);
            var native = root.Type;
            var field = native is null ? null : layouts.ContainingField(native, checked((int)offset), bytes);
            if (field is null || field.Offset != offset || field.Size != bytes || field.Path.Where(p => p != "fields").Count() != 1 ||
                managed.SourceMember(symbols.Display(native!), field.Name) is null)
            { problems.Add("SSA 存储字段未绑定：" + address.Name); return null; }
            // 存储和写屏障指向实际字段；属性不能作为 ref 写屏障的目标。
            return new(expressions.Value(root), field.Name, field.Type);
        }
    }
}
