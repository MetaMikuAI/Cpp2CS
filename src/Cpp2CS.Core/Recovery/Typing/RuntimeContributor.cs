using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Typing;

/// <summary>MarkRuntime 的布尔域与闭包忠实迁移；细类只记录在证据中，不凭旧规则无法区分的 φ 创造细类冲突。</summary>
internal sealed class RuntimeContributor(TypingInputs input) : ITypeContributor
{
    internal static readonly RuntimeKind Legacy = new("legacy-reference");
    public string Name => "运行时";
    public void Contribute(TypingContext context, TypeConstraints constraints)
    {
        var definitions = context.Statements.OfType<Define>().ToArray();
        var values = definitions.ToDictionary(d => d.Target, d => d.Value);
        var phis = context.Statements.OfType<Phi>().ToArray();
        var results = context.Statements.OfType<Call>().SelectMany(c => c.Defines.OfType<Variable>().Select(v => (v, c))).ToDictionary(x => x.v, x => x.c);
        var marked = new HashSet<Variable>();
        var evidence = new Dictionary<Variable, TypeEvidence>();
        void Mark(Variable v, ulong address, string detail) { marked.Add(v); evidence.TryAdd(v, new(Name, address, detail)); }
        foreach (var define in definitions)
            if (define.Value is Symbol { Kind: not SymbolKind.String } or FrameAddress)
                Mark(define.Target, define.Address, define.Value.ToString()!);
        foreach (var (variable, call) in results)
            if (call.Op?.Kind is OpKind.InitClass or OpKind.InitMethodRgctx or OpKind.InterfaceInvokeData or OpKind.ResolveGenericVirtual)
                Mark(variable, call.Address, call.Op.Kind.ToString());
        // 只读其他规则的上一轮结果作种子；本贡献者的闭包不能因中间解为 Conflict 而丢失已证明的运行时来源。
        foreach (var variable in values.Keys.Concat(phis.Select(p => p.Target)).Concat(results.Keys).Where(context.IsRuntime)) marked.Add(variable);
        foreach (var variable in input.Wrappers.Keys) marked.Add(variable);
        foreach (var define in definitions)
            if (input.HasExceptions && define.Value is Intrinsic { Name: "eh_exception" or "eh_selector" }) marked.Add(define.Target);
        foreach (var (_, klass) in input.Expressions(context).TypeChecks()) marked.Add(klass.Variable);
        Expr Expand(Expr expression) => expression is Use u && marked.Contains(u.Variable) && values.TryGetValue(u.Variable, out var value) ? Expand(value) : expression;
        for (var changed = true; changed;)
        {
            var before = marked.Count;
            foreach (var define in definitions)
            {
                if (define.Value is Use copied && marked.Contains(copied.Variable)) Mark(define.Target, define.Address, $"复制 {copied.Variable}");
                if (define.Value is not Load { Width: 64 } load) continue;
                var address = Expand(load.Address);
                if (address is Binary { Op: BinOp.Add, Right: Const { Value: 0 or 8 } } add) address = Expand(add.Left);
                if (address is Use use && results.TryGetValue(use.Variable, out var call) && call.Op?.Kind == OpKind.InterfaceInvokeData)
                    Mark(define.Target, define.Address, $"InterfaceInvokeData +0/+8 {use.Variable}");
            }
            foreach (var phi in phis)
                foreach (var source in phi.Sources.Where(marked.Contains)) Mark(phi.Target, phi.Address, $"φ 含运行时来源 {source}");
            changed = marked.Count != before;
        }
        // 其他贡献者的种子仍由其自身写出证据；这里只写本规则及沿复制/φ 传播得到的事实。
        foreach (var (variable, source) in evidence) constraints.IsRuntime(variable, Legacy, source);
    }
}
