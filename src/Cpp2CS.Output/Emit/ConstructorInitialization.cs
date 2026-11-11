namespace Cpp2CS.Output;

/// <summary>验证各可达路径上的 this 初始化与初始化前使用，不限制 C# 表达形式。</summary>
internal static class ConstructorInitialization
{
    public sealed record Analysis(ConstructorValues Values, IReadOnlySet<MethodRef> Targets,
        IReadOnlyList<ManagedStatement> BeforeBase, bool InitializerStores);

    public static string? Check(ManagedBody body, out Analysis? analysis)
    {
        analysis = null;
        var owner = body.Method.Method.Owner;
        var values = new ConstructorValues(body);
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var queue = new Queue<(ulong Address, bool Initialized)>();
        queue.Enqueue((body.Blocks[0].Address, false));
        var visited = new HashSet<(ulong, bool)>();
        var targets = new HashSet<MethodRef>();
        var initializerStores = false;
        var beforeBase = new List<ManagedStatement>();
        while (queue.TryDequeue(out var state))
        {
            if (!visited.Add(state)) continue;
            var initialized = state.Initialized;
            foreach (var statement in blocks[state.Address].Statements)
            {
                if (statement is ManagedCall call && values.IsInitialization(call))
                {
                    var target = call.Invocation.Method;
                    if (initialized) return "构造函数路径重复初始化 this";
                    if (target.Method.IsStatic || target.Method.Owner != owner && target.DeclaringType != owner.BaseType)
                        return "构造函数没有调用本类或直接基类构造函数";
                    if (call.Invocation.Arguments.Any(values.UsesThis)) return "基类构造参数使用了未初始化的 this";
                    targets.Add(target);
                    initialized = true;
                }
                else if (!initialized)
                {
                    beforeBase.Add(statement);
                    initializerStores |= values.IsOwnFieldStore(statement);
                    var permitted = statement switch
                    {
                        ManagedAssignment a => values.IsThis(a.Value) || !values.UsesThis(a.Value),
                        ManagedStore s when values.IsOwnFieldStore(s) => !values.UsesThis(s.Value),
                        ManagedStore s => !values.UsesThis(s.Target) && !values.UsesThis(s.Value),
                        ManagedCall c => (c.Invocation.Receiver is null || !values.UsesThis(c.Invocation.Receiver)) && !c.Invocation.Arguments.Any(values.UsesThis),
                        ManagedJump => true,
                        ManagedBranch b => !values.UsesThis(b.Condition),
                        ManagedSwitch w => !values.UsesThis(w.Index),
                        ManagedCheck k => !values.UsesThis(k.Condition),
                        ManagedThrow t => !values.UsesThis(t.Exception),
                        ManagedReturn => false,
                        _ => false,
                    };
                    if (!permitted) return "构造函数在基类初始化前读取或泄漏 this，或直接返回";
                }
                foreach (var edge in ManagedValues.Edges(statement))
                {
                    if (!initialized && edge.Copies.Any(c => !values.IsThis(c.Value) && values.UsesThis(c.Value))) return "构造函数的边赋值使用了未初始化的 this";
                    queue.Enqueue((edge.Target, initialized));
                }
                if (statement is ManagedReturn)
                    if (!initialized) return "构造函数的返回路径没有初始化 this";
            }
        }
        analysis = new(values, targets, beforeBase, initializerStores);
        return null;
    }
}
