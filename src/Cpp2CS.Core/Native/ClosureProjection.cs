namespace Cpp2CS.Native;

public sealed record ClosureBinding(HeaderField Field, string Name, string Type);
public sealed record ClosureLambda(ulong Construction, string DelegateType, LambdaExpression Lambda, LiftResult Body);
public sealed record ClosureSite(ulong Allocation, string EnvironmentType, ClosureBinding[] Bindings, ClosureLambda[] Lambdas);

// 环境身份由分配点决定；父环境链接保持共享，捕获变量在原分配位置声明。
public static class ClosureProjection
{
    private sealed record Environment(CallStatement Allocation, CallStatement Constructor, string Type, NameExpression Root);
    public static LambdaProjection Build(LambdaProjection source, ManagedNames managed,
        Func<MetadataExpression, NativeMethod?> target, Func<ulong, LiftResult> lift)
    {
        var view = SourceTree.Map(source.View, e => e);
        if (view.Problems.Count != 0 || view.Blocks.Count == 0) return source;
        var diagnostics = source.Diagnostics.ToList();
        var statements = view.Blocks.Values.SelectMany(b => b.Statements).ToArray();
        var environments = new List<Environment>();
        foreach (var block in view.Blocks.Values)
            for (var i = 0; i + 1 < block.Statements.Count; i++)
                if (block.Statements[i] is CallStatement { Result: { } name, Arguments.Length: 0 } allocation &&
                    allocation.Name.StartsWith("Runtime.Allocate<") && allocation.Name.EndsWith('>') &&
                    managed.IsClosureType(allocation.Name[17..^1], view.Method) &&
                    block.Statements[i + 1] is CallStatement { Name: ".ctor", DeclaringType: "System.Object", Arguments.Length: 0 } ctor && ctor.Receiver == new NameExpression(name))
                    environments.Add(new(allocation, ctor, allocation.Name[17..^1], new(name)));
        if (environments.Count == 0) return source;
        var roots = environments.Select(e => e.Root).ToHashSet();
        var links = new Dictionary<MemberExpression, NameExpression>();
        var removed = environments.SelectMany(e => new Statement[] { e.Allocation, e.Constructor }).ToHashSet();
        foreach (var store in statements.OfType<StoreStatement>())
        {
            if (store.Target is not MemberExpression { Receiver: NameExpression child } member || !roots.Contains(child) || store.Value is not NameExpression parent || !roots.Contains(parent)) continue;
            var owner = environments.Single(e => e.Root == child); var parentEnvironment = environments.Single(e => e.Root == parent);
            if (managed.SourceMember(owner.Type, member.Field.Name)?.Type != parentEnvironment.Type || child == parent ||
                statements.OfType<StoreStatement>().Count(s => s.Target == store.Target) != 1) return Reject("父环境链接存在重赋值或类型不匹配");
            if (!DominatesUses(view, store, member)) return Reject("父环境链接初始化未支配所有读取");
            links.Add(member, parent); removed.Add(store);
        }
        var aliases = new Dictionary<string, NameExpression>();
        Expression Link(Expression e)
        {
            if (e is NameExpression n && aliases.TryGetValue(n.Name, out var alias)) return alias;
            if (e is CapturedExpression { Value: NameExpression v } && roots.Contains(v)) return v;
            if (e is MemberExpression m && links.SingleOrDefault(p => p.Key.Receiver == m.Receiver && p.Key.Field == m.Field).Value is { } parent) return parent;
            return e;
        }
        // 别名只能来自已证明不变的父链接，普通捕获读取仍保留取值时点。
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var a in statements.OfType<AssignStatement>())
                if (!aliases.ContainsKey(a.Name) && SourceTree.Map(a.Value, Link) is NameExpression n && roots.Contains(n))
                { aliases.Add(a.Name, n); removed.Add(a); changed = true; }
        }
        foreach (var barrier in statements.OfType<CallStatement>())
            if (barrier is { Name: "Runtime.GCWriteBarrier", Arguments: [AddressOfExpression { Target: MemberExpression m }] } &&
                SourceTree.Map(m.Receiver, Link) is NameExpression n && roots.Contains(n)) removed.Add(barrier);
        var used = view.Method.Parameters.Select(p => p.Name).Concat(statements.OfType<AssignStatement>().Select(a => a.Name)).ToHashSet();
        var bindings = new Dictionary<NameExpression, List<ClosureBinding>>();
        foreach (var environment in environments)
        {
            var fields = statements.OfType<StoreStatement>().Where(s => !removed.Contains(s)).Select(s => SourceTree.Map(s.Target, Link)).OfType<MemberExpression>()
                .Where(m => m.Receiver == environment.Root).Select(m => m.Field).Distinct().ToArray();
            var list = new List<ClosureBinding>(); bindings.Add(environment.Root, list);
            foreach (var field in fields)
            {
                var member = managed.SourceMember(environment.Type, field.Name);
                if (member is null) return Reject("捕获字段缺少托管元数据");
                var name = member.Value.Name == "<>4__this" ? "capturedThis" : "captured" + char.ToUpperInvariant(member.Value.Name[0]) + member.Value.Name[1..];
                if (!System.Text.RegularExpressions.Regex.IsMatch(name, @"^[A-Za-z_]\w*$")) return Reject("捕获字段名称尚未恢复");
                var unique = name; var suffix = 2; while (!used.Add(unique)) unique = name + suffix++;
                list.Add(new(field, unique, member.Value.Type));
            }
        }
        Expression Bind(Expression e)
        {
            e = Link(e);
            return e is MemberExpression { Receiver: NameExpression n } m && bindings.TryGetValue(n, out var fields) && fields.SingleOrDefault(b => b.Field == m.Field) is { } field ? new NameExpression(field.Name) : e;
        }
        var lambdas = new Dictionary<CallStatement, ClosureLambda>();
        var sites = new List<ClosureSite>();
        foreach (var environment in environments)
        {
            var delegates = statements.OfType<CallStatement>().Where(c => c is { Name: ".ctor", Arguments: [var receiver, MetadataExpression] } && SourceTree.Map(receiver, Link) == environment.Root).ToArray();
            var recovered = new List<ClosureLambda>();
            foreach (var ctor in delegates)
            {
                if (ctor.Receiver is not NameExpression delegateName || ctor.Arguments[1] is not MetadataExpression method || target(method) is not { } native) return Reject("闭包委托入口未确定");
                var allocations = statements.OfType<CallStatement>().Where(c => c.Result == delegateName.Name && c.Name.StartsWith("Runtime.Allocate<") && c.Arguments.Length == 0).ToArray();
                if (allocations.Length != 1) return Reject("委托分配身份不唯一");
                var creation = view.Blocks.Values.Single(b => b.Statements.Contains(allocations[0]));
                if (creation.Statements.IndexOf(ctor) != creation.Statements.IndexOf(allocations[0]) + 1) return Reject("委托构造与分配未相邻");
                var delegateType = allocations[0].Name[17..^1];
                if (!managed.IsCapturingLambda(view.Method, native, environment.Type, delegateType) || ManagedNames.SplitGeneric(ctor.DeclaringType ?? "").Name != ManagedNames.SplitGeneric(delegateType).Name)
                    return Reject("闭包方法的元数据身份或签名不匹配");
                var original = lift(native.Address);
                var boundBody = SourceTree.Map(original, e => Bind(e is NameExpression { Name: "this" } ? environment.Root : e));
                foreach (var b in boundBody.Blocks.Values.ToArray())
                {
                    b.Statements.RemoveAll(s => s is AssignStatement { Value: NameExpression n } && roots.Contains(n));
                    if (b.Condition is BinaryExpression { Operator: "is", Left: NameExpression n, Right: NameExpression { Name: "null" } } && roots.Contains(n) &&
                        b.Successors.Length == 2 && boundBody.Blocks[b.Successors[0]].Statements is [ThrowStatement { Type: "System.NullReferenceException" }])
                        boundBody.Blocks[b.Address] = b with { Condition = null, Successors = [b.Successors[1]] };
                }
                var lambda = LambdaBodies.Expression(boundBody, bindings.Values.SelectMany(b => b).Select(b => b.Name).ToArray());
                if (lambda is null || lambda.Parameters.Any(used.Contains)) return Reject($"0x{native.Address:x}: 捕获绑定后的方法体未归约或参数名称冲突");
                var site = new ClosureLambda(ctor.Address, delegateType, lambda, original);
                lambdas.Add(ctor, site); recovered.Add(site); removed.Add(allocations[0]); removed.Add(ctor);
            }
            sites.Add(new(environment.Allocation.Address, environment.Type, bindings[environment.Root].ToArray(), recovered.ToArray()));
        }
        if (lambdas.Count == 0) return source;
        foreach (var block in view.Blocks.Values.ToArray())
        {
            var updated = new List<Statement>();
            foreach (var statement in block.Statements)
            {
                if (environments.SingleOrDefault(e => e.Allocation == statement) is { } environment)
                    updated.AddRange(bindings[environment.Root].Select(b => new AssignStatement(statement.Address, b.Name, new NameExpression("default(" + b.Type + ")"), b.Type)));
                else if (statement is CallStatement ctor && lambdas.TryGetValue(ctor, out var lambda))
                    updated.Add(new AssignStatement(ctor.Address, ((NameExpression)ctor.Receiver!).Name, lambda.Lambda, lambda.DelegateType));
                else if (!removed.Contains(statement))
                {
                    var mapped = SourceTree.Map(statement, Bind);
                    updated.Add(mapped is StoreStatement { Target: NameExpression n } store ? new SetLocalStatement(store.Address, n.Name, store.Value) : mapped);
                }
            }
            var guard = block.Condition is BinaryExpression { Operator: "is", Left: var left, Right: NameExpression { Name: "null" } } &&
                SourceTree.Map(left, Link) is NameExpression root && roots.Contains(root) && block.Successors.Length == 2 &&
                view.Blocks[block.Successors[0]].Statements is [ThrowStatement { Type: "System.NullReferenceException" }];
            view.Blocks[block.Address] = block with { Statements = updated, Condition = guard ? null : block.Condition is { } c ? SourceTree.Map(c, Bind) : null,
                Successors = guard ? [block.Successors[1]] : block.Successors };
        }
        bool Escapes(Expression e)
        { var bad = false; SourceTree.Map(e, n => { if (n is NameExpression name && roots.Contains(name)) bad = true; return n; }); return bad; }
        if (view.Blocks.Values.Any(b => b.Statements.SelectMany(ViewNormalizer.Expressions).Any(Escapes) || b.Condition is { } c && Escapes(c))) return Reject("环境对象身份逃逸，保留原始环境");
        view = ViewNormalizer.Normalize(view with { IsSourceProjection = true });
        foreach (var site in sites) view.Proofs.Add(new(site.Allocation, "SourceClosureEnvironment", "allocation-scoped locals; immutable parent links share identity; capture reads and writes retain CFG positions; environment escape rejected"));
        return source with { View = view, Closures = sites.ToArray(), Diagnostics = diagnostics.ToArray() };
        LambdaProjection Reject(string reason) => source with { Diagnostics = [.. diagnostics, reason] };
    }
    private static bool DominatesUses(LiftResult view, StoreStatement store, MemberExpression member)
    {
        var owner = view.Blocks.Values.Single(b => b.Statements.Contains(store));
        var without = new HashSet<ulong>(); var pending = new Stack<ulong>(); pending.Push(view.Method.Address);
        while (pending.TryPop(out var pc)) if (pc != owner.Address && without.Add(pc)) foreach (var next in view.Blocks[pc].Successors) pending.Push(next);
        bool Uses(Expression e) { var found = false; SourceTree.Map(e, n => { if (n == member) found = true; return n; }); return found; }
        return !view.Blocks.Values.Any(b => (without.Contains(b.Address) ? b.Statements : b.Address == owner.Address ? b.Statements.Take(b.Statements.IndexOf(store)) : [])
            .Any(s => ViewNormalizer.Expressions(s).Any(Uses) || s is CallStatement { Name: ".ctor", Arguments: [var receiver, MetadataExpression] } && receiver == member.Receiver) ||
            without.Contains(b.Address) && b.Condition is { } c && Uses(c));
    }
}
