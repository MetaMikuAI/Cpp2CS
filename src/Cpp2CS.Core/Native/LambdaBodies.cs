namespace Cpp2CS.Native;

public sealed record LambdaBlockExpression(LiftResult Body) : Expression;

// 先证明单表达式方法体，再生成不捕获外层变量的 lambda；复杂控制流保持原样。
public static class LambdaBodies
{
    public static LambdaExpression? Expression(LiftResult source, string[]? captures = null)
    {
        if (source.Problems.Count != 0 || source.Blocks.Count == 0) return null;
        var parameters = source.Method.Parameters.Where(p => p.Name != "__this" && !(p.Name == "method" && p.Type.Contains("MethodInfo")))
            .Select(p => p.Name).ToArray();
        var bound = parameters.Concat(captures ?? []).ToHashSet();
        var body = source with { Blocks = source.Blocks.ToDictionary(p => p.Key, p => p.Value with
            { Statements = p.Value.Statements.Where(s => s is not EnsureMetadataStatement).ToList() }), Proofs = [.. source.Proofs] };
        foreach (var block in body.Blocks.Values.ToArray())
        {
            if (block.Condition is not BinaryExpression { Operator: "is", Left: var receiver, Right: NameExpression { Name: "null" } } ||
                !(receiver is NameExpression n && bound.Contains(n.Name) || receiver is CapturedExpression) || block.Successors.Length != 2 ||
                body.Blocks[block.Successors[0]].Statements is not [ThrowStatement { Type: "System.NullReferenceException" }] ||
                body.Blocks[block.Successors[0]].Successors.Length != 0 ||
                body.Blocks[block.Successors[1]].Statements.FirstOrDefault() is not CallStatement { IsInstance: true } call || call.Receiver != receiver ||
                !call.Arguments.All(a => a is ConstantExpression || a is NameExpression n && bound.Contains(n.Name))) continue;
            // 参数取值无副作用，紧邻实例调用在同一时点执行空引用检查。
            body.Blocks[block.Address] = block with { Condition = null, Successors = [block.Successors[1]] };
        }
        body = ViewNormalizer.Normalize(body);
        if (body.Blocks.Count != 1) return BooleanBody(body) is { } boolean && Bound(boolean) ? new(parameters, boolean, source.Method.Address) : Block();
        if (body.Blocks.Values.Single() is not { Condition: null, Successors.Length: 0 } single) return null;
        Native.Expression? expression = single.Statements switch
        {
            [CallStatement { Result: { } result } call, ReturnStatement { Value: NameExpression value }] when result == value.Name => Invoke(call),
            [CallStatement { Result: null } call, ReturnStatement { Value: null }] => Invoke(call),
            [ReturnStatement { Value: { } value }] => value,
            _ => null
        };
        return expression is not null && Bound(expression) ? new(parameters, expression, source.Method.Address) : Block();
        LambdaExpression? Block()
        {
            if (captures is null) return null;
            var all = body.Blocks.Values.SelectMany(b => b.Statements).ToArray();
            bound.UnionWith(all.OfType<AssignStatement>().Select(a => a.Name));
            bound.UnionWith(all.OfType<CallStatement>().Select(c => c.Result).OfType<string>());
            if (all.Any(s => s is not (AssignStatement or CallStatement or ReturnStatement or ThrowStatement or StoreStatement or SetLocalStatement) ||
                s is CallStatement c && (c.Name.StartsWith("Runtime.") || c.Name == ".ctor")) ||
                all.SelectMany(ViewNormalizer.Expressions).Any(e => !Bound(e)) || body.Blocks.Values.Any(b => b.Condition is { } c && !Bound(c))) return null;
            return new(parameters, new LambdaBlockExpression(body), source.Method.Address);
        }
        Native.Expression? Invoke(CallStatement call) => call.NoReturn || call.Name.StartsWith("Runtime.") || call.Name == ".ctor" ? null :
            new InvocationExpression(call.Name, call.IsInstance ? call.Receiver : null, call.Arguments, call.IsProperty);
        bool Bound(Native.Expression e) => e switch
        {
            NameExpression n => bound.Contains(n.Name) || n.Name is "null" or "true" or "false",
            ConstantExpression => true,
            CapturedExpression c => bound.Contains(c.Name),
            OperationExpression o => o.Arguments.All(Bound),
            MemberExpression m => Bound(m.Receiver),
            BinaryExpression b => Bound(b.Left) && Bound(b.Right),
            InvocationExpression c => (c.Receiver is null || Bound(c.Receiver)) && c.Arguments.All(Bound),
            _ => false
        };
    }
    // 每个调用结果仅在本块使用一次；分支归约为短路表达式，不提前计算右侧。
    private static Native.Expression? BooleanBody(LiftResult source)
    {
        Native.Expression? Reduce(ulong pc, HashSet<ulong> path)
        {
            if (!path.Add(pc)) return null;
            var block = source.Blocks[pc];
            var statements = block.Statements.ToArray();
            CallStatement? call = statements.FirstOrDefault() as CallStatement;
            if (call is not null && (call.NoReturn || call.Result is null || call.ReturnType is not ("bool" or "System.Boolean") || call.Name.StartsWith("Runtime."))) return null;
            Native.Expression Rewrite(Native.Expression e)
            {
                if (call is not null && e is NameExpression n && n.Name == call.Result) return new InvocationExpression(call.Name, call.Receiver, call.Arguments, call.IsProperty);
                if (e is BinaryExpression { Operator: "!=", Left: ConstantExpression { Value: 1 }, Right: ConstantExpression { Value: 0 } }) return new NameExpression("true");
                if (e is BinaryExpression { Operator: "==" or "!=", Left: BinaryExpression { Operator: "&", Left: SliceExpression { BitOffset: 0, BitWidth: 32, Value: InvocationExpression value }, Right: ConstantExpression { Value: 1 } }, Right: ConstantExpression { Value: 0 } } b)
                    return b.Operator == "!=" ? value : new BinaryExpression("==", value, new NameExpression("false"));
                return e;
            }
            var rest = call is null ? statements : statements[1..];
            if (call is not null && block.Statements.Sum(s => ViewNormalizer.Expressions(s).Sum(e => ViewNormalizer.Count(e, call.Result!))) +
                (block.Condition is null ? 0 : ViewNormalizer.Count(block.Condition, call.Result!)) != 1) return null;
            if (rest is [ReturnStatement { Value: { } returned }] && block.Successors.Length == 0) return SourceTree.Map(returned, Rewrite);
            if (rest.Length != 0 || block.Condition is null || block.Successors.Length != 2) return null;
            var condition = SourceTree.Map(block.Condition, Rewrite);
            var yes = Reduce(block.Successors[0], new(path)); var no = Reduce(block.Successors[1], new(path));
            if (yes is null || no is null) return null;
            if (condition is BinaryExpression { Operator: "==", Right: NameExpression { Name: "false" } } negated)
            { condition = negated.Left; (yes, no) = (no, yes); }
            return yes is NameExpression { Name: "true" } ? new BinaryExpression("||", condition, no) :
                no is NameExpression { Name: "false" } ? new BinaryExpression("&&", condition, yes) : null;
        }
        return Reduce(source.Method.Address, []);
    }
}

public sealed record LambdaSite(DelegateCacheStatement Cache, LambdaExpression Lambda, LiftResult Body);
public sealed record LambdaProjection(LiftResult View, LambdaSite[] Sites, string[] Diagnostics)
{
    public ClosureSite[] Closures { get; init; } = [];
}

public static class LambdaProjectionBuilder
{
    public static LambdaProjection Build(LiftResult source, Func<DelegateCacheStatement, LambdaSite?> resolve)
    {
        var view = source with { Blocks = source.Blocks.ToDictionary(p => p.Key, p => p.Value with { Statements = [.. p.Value.Statements] }), Proofs = [.. source.Proofs] };
        var sites = new List<LambdaSite>(); var diagnostics = new List<string>();
        if (source.Problems.Count != 0) return new(view, [], []);
        var caches = source.Blocks.Values.SelectMany(b => b.Statements).OfType<DelegateCacheStatement>().ToArray();
        foreach (var block in view.Blocks.Values)
        {
            for (var i = 0; i + 1 < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not DelegateCacheStatement cache) continue;
                var uses = view.Blocks.Values.Sum(b => b.Statements.Sum(s => ViewNormalizer.Expressions(s).Sum(e => ViewNormalizer.Count(e, cache.Name))) +
                    (b.Condition is null ? 0 : ViewNormalizer.Count(b.Condition, cache.Name)));
                if (uses != 1 || block.Statements[i + 1] is not CallStatement call ||
                    !call.Arguments.Any(a => a is NameExpression n && n.Name == cache.Name)) continue;
                if (view.Blocks.Values.Any(b => b.Statements.Where(s => s != cache).SelectMany(ViewNormalizer.Expressions).Any(e => References(e, cache.Cache.Field)) ||
                    b.Condition is { } condition && References(condition, cache.Cache.Field))) continue;
                var site = resolve(cache);
                if (site is null) { diagnostics.Add($"0x{cache.Address:x}: lambda 身份、签名或单表达式方法体未确认，保留缓存"); continue; }
                site = site with { Lambda = AvoidParameterShadowing(site.Lambda, source.Method.Parameters.Select(p => p.Name)) };
                block.Statements[i + 1] = call with { Arguments = call.Arguments.Select(a => a is NameExpression n && n.Name == cache.Name ? site.Lambda : a).ToArray() };
                block.Statements.RemoveAt(i--);
                sites.Add(site);
                view.Proofs.Add(new(cache.Address, "SourceLambdaProjection", $"generated delegate cache -> lambda body 0x{site.Lambda.MethodAddress:x}; one adjacent argument use; lowering retained separately, not a runtime-equivalence rewrite"));
            }
        }
        if (sites.Count > 0)
        {
            view = view with { IsSourceProjection = true };
            if (sites.Count == caches.Length)
            {
                var owners = caches.Select(c => ((MemberExpression)c.Cache.Receiver).Receiver).ToHashSet();
                foreach (var block in view.Blocks.Values)
                    block.Statements.RemoveAll(s => s is EnsureMetadataStatement || s is CallStatement
                        { Name: "Runtime.EnsureClassInitialized", Arguments: [var type] } && owners.Contains(type));
            }
        }
        return new(view, sites.ToArray(), diagnostics.ToArray());
    }
    private static LambdaExpression AvoidParameterShadowing(LambdaExpression lambda, IEnumerable<string> outerParameters)
    {
        var used = outerParameters.ToHashSet(); var names = new Dictionary<string, string>();
        foreach (var parameter in lambda.Parameters)
        {
            var name = parameter; var suffix = 2;
            while (!used.Add(name)) name = parameter + suffix++;
            names.Add(parameter, name);
        }
        Expression Rename(Expression e) => e switch
        {
            NameExpression n when names.TryGetValue(n.Name, out var name) => n with { Name = name },
            MemberExpression m => m with { Receiver = Rename(m.Receiver) },
            BinaryExpression b => b with { Left = Rename(b.Left), Right = Rename(b.Right) },
            InvocationExpression c => c with { Receiver = c.Receiver is null ? null : Rename(c.Receiver), Arguments = c.Arguments.Select(Rename).ToArray() },
            _ => e
        };
        return lambda with { Parameters = lambda.Parameters.Select(p => names[p]).ToArray(), Body = Rename(lambda.Body) };
    }
    private static bool References(Expression e, HeaderField field) => e switch
    {
        OperationExpression o => o.Arguments.Any(a => References(a, field)),
        MemberExpression m => m.Field == field || References(m.Receiver, field),
        CapturedExpression c => References(c.Value, field),
        BinaryExpression b => References(b.Left, field) || References(b.Right, field),
        AddressOfExpression a => References(a.Target, field),
        SliceExpression s => References(s.Value, field),
        ComposeExpression c => c.Parts.Any(p => References(p, field)),
        AggregateExpression a => References(a.Bits, field),
        _ => false
    };
}
