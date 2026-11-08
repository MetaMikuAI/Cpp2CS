using Cpp2CS.Ir;
using Cpp2CS.Managed;

namespace Cpp2CS.Recovery.Effects;

/// <summary>
/// 托管调用对堆的摘要：返回路径上可能写的实例字段（按实参代入后的声明类型），
/// 以及每条返回路径上都写入同一常量的字段。摘要之外的堆位置，调用前后内容不变。
/// </summary>
internal sealed record CallSummary(IReadOnlyList<FieldRef> Writes, IReadOnlyList<(FieldValue Location, ConstantValue Value)> Stores);

/// <summary>
/// 由方法体计算调用摘要。方法体只经过有界的方法时才有摘要：路径上只有对字段、数组元素和静态字段的写入，
/// 对非重写方法（同样有界）和只写数组元素的库方法的调用；抛出的路径不返回，不计。
/// 出现环、可重写方法或没有方法体的调用时没有摘要，调用方按全部堆位置可能被改写处理。
/// </summary>
internal sealed class CallSummaries(Func<MethodRef, ManagedBody?> bodies)
{
    private readonly Dictionary<MethodRef, IReadOnlyList<FieldRef>?> writeSets = [];

    /// <summary>调用的摘要；未知时为 null。</summary>
    public CallSummary? Of(ManagedInvocation invocation)
    {
        if (invocation.Method.Method.IsOverridable || invocation.Receiver is null || Writes(invocation.Method, []) is not { } writes) return null;
        var stores = bodies(invocation.Method) is { } body ? Constants(body, invocation) : [];
        return new(writes, stores);
    }

    private IReadOnlyList<FieldRef>? Writes(MethodRef method, HashSet<MethodRef> active)
    {
        if (writeSets.TryGetValue(method, out var known)) return known;
        if (!active.Add(method) || active.Count > 8 || bodies(method) is not { } body) return null;
        var result = Bounded(method, body, active);
        active.Remove(method);
        return writeSets[method] = result;
    }

    private IReadOnlyList<FieldRef>? Bounded(MethodRef method, ManagedBody body, HashSet<MethodRef> active)
    {
        var returning = body.Blocks.Where(b => b.Statements.Any(st => st is ManagedReturn)).Select(b => b.Address).ToHashSet();
        for (var grew = true; grew;)
        {
            grew = false;
            foreach (var block in body.Blocks)
                if (!returning.Contains(block.Address) && block.Statements.SelectMany(ManagedValues.Edges).Any(e => returning.Contains(e.Target)))
                    grew = returning.Add(block.Address);
        }
        var writes = new List<FieldRef>();
        foreach (var block in body.Blocks.Where(b => returning.Contains(b.Address)))
            foreach (var statement in block.Statements)
            {
                if (ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).Any(v => ManagedEffects.Value(v).InvalidatesMemory)) return null;
                switch (statement)
                {
                    case ManagedStore { Target: FieldValue written }:
                        writes.Add(written.Field with { DeclaringType = written.Field.DeclaringType.Substitute(method.TypeArguments, method.MethodArguments) });
                        break;
                    case ManagedStore { Target: ArrayElementValue or StaticFieldValue }:
                    case ManagedAssignment or ManagedCheck or ManagedBranch or ManagedJump or ManagedSwitch or ManagedReturn or ManagedThrow:
                        break;
                    case ManagedCall { Invocation: var inner }:
                        if (inner.Method.Method.IsOverridable) return null;
                        if (ArrayOnly(inner.Method.Method)) break;
                        var callee = inner.Method with
                        {
                            TypeArguments = inner.Method.TypeArguments.Select(t => t.Substitute(method.TypeArguments, method.MethodArguments)).ToArray(),
                            MethodArguments = inner.Method.MethodArguments.Select(t => t.Substitute(method.TypeArguments, method.MethodArguments)).ToArray(),
                        };
                        if (Writes(callee, active) is not { } nested) return null;
                        writes.AddRange(nested);
                        break;
                    default:
                        return null;
                }
            }
        return writes;
    }

    /// <summary>System.Array 的复制与清除只写数组元素，不写任何对象字段。</summary>
    private static bool ArrayOnly(MethodDef method) => method.Owner.FullName == "System.Array" && method.Name is "Copy" or "Clear";

    /// <summary>
    /// 方法体在每条返回路径上都对 this 的同一字段写入同一常量时，调用返回后该字段就是这个常量。
    /// 路径上的调用、对同一字段定义的其他写入和未知语句使之失效。
    /// </summary>
    private static IReadOnlyList<(FieldValue Location, ConstantValue Value)> Constants(ManagedBody template, ManagedInvocation invocation)
    {
        if (invocation.Receiver is null || template.Blocks.Count == 0) return [];
        var byAddress = template.Blocks.ToDictionary(b => b.Address);
        var entries = new Dictionary<ulong, Dictionary<FieldDef, ConstantValue>> { [template.Blocks[0].Address] = [] };
        var pending = new Queue<ulong>([template.Blocks[0].Address]);
        Dictionary<FieldDef, ConstantValue>? result = null;
        while (pending.TryDequeue(out var address))
        {
            var facts = new Dictionary<FieldDef, ConstantValue>(entries[address]);
            foreach (var statement in byAddress[address].Statements)
            {
                if (ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).Any(v => ManagedEffects.Value(v).InvalidatesMemory)) facts.Clear();
                switch (statement)
                {
                    case ManagedStore { Target: FieldValue written } store:
                        facts.Remove(written.Field.Field);
                        if (written.Receiver is ArgumentValue { Index: -1 } && store.Value is ConstantValue constant) facts[written.Field.Field] = constant;
                        break;
                    case ManagedStore { Target: ArrayElementValue or StaticFieldValue }:
                    case ManagedAssignment or ManagedCheck or ManagedBranch or ManagedJump or ManagedSwitch or ManagedThrow:
                        break;
                    case ManagedReturn:
                        result = result is null ? new(facts) : result.Where(r => facts.TryGetValue(r.Key, out var other) && other.Equals(r.Value)).ToDictionary();
                        break;
                    default:
                        facts.Clear();
                        break;
                }
                foreach (var edge in ManagedValues.Edges(statement))
                {
                    if (!byAddress.ContainsKey(edge.Target)) continue;
                    if (!entries.TryGetValue(edge.Target, out var known))
                    {
                        entries[edge.Target] = new(facts);
                        pending.Enqueue(edge.Target);
                    }
                    else
                    {
                        var before = known.Count;
                        foreach (var key in known.Keys.ToArray())
                            if (!facts.TryGetValue(key, out var other) || !other.Equals(known[key])) known.Remove(key);
                        if (known.Count != before) pending.Enqueue(edge.Target);
                    }
                }
            }
        }
        var owner = invocation.Method.Method.Owner;
        return (result ?? []).Where(r => ReferenceEquals(r.Key.Owner, owner))
            .Select(r => (new FieldValue(invocation.Receiver, new FieldRef(r.Key, invocation.Method.DeclaringType), invocation.Method.Concrete(r.Key.Type), r.Value.Width), r.Value)).ToArray();
    }
}
