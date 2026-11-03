using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Inlining;

internal sealed partial class TemplateRecovery
{
    /// <summary>
    /// 连续写入 this 的不同字段、写入值为参数或常量且两两不别名（<see cref="MayAlias"/>）时可交换。按优先字段、再按布局偏移
    /// 排出一种规范次序，使基类构造模板所需的写入与本类写入分开。值限于参数与常量：局部或表达式在模板与调用方中的表示
    /// 可能不同（一侧是局部，另一侧是内联的表达式），规范次序须对两侧一致。
    /// </summary>
    private ManagedBody CommuteIndependentStores(ManagedBody body, IReadOnlySet<FieldDef> preferred)
    {
        static bool Plain(ManagedValue value) => value is ArgumentValue or ConstantValue;
        int Offset(FieldRef field) => field.DeclaringType is DefinitionRef owner
            && types.Layouts.Of(owner)?.Fields.FirstOrDefault(f => f.Field == field.Field) is { } slot ? slot.Offset : int.MaxValue;
        return body with { Blocks = body.Blocks.Select(block =>
        {
            var statements = block.Statements.ToArray();
            for (var first = 0; first < statements.Length; first++)
            {
                if (statements[first] is not ManagedStore { Target: FieldValue { Receiver: ArgumentValue { Index: -1 } receiver } head, Value: var value } || !Plain(value)) continue;
                var run = new List<FieldValue> { head };
                var end = first + 1;
                while (end < statements.Length && statements[end] is ManagedStore { Target: FieldValue next, Value: var stored }
                    && next.Receiver.Equals(receiver) && Plain(stored) && run.All(r => !MayAlias(r, next)))
                { run.Add(next); end++; }
                if (run.Count < 2) continue;
                var ordered = statements[first..end].Zip(run)
                    .OrderByDescending(p => preferred.Contains(p.Second.Field.Field)).ThenBy(p => Offset(p.Second.Field)).Select(p => p.First).ToArray();
                Array.Copy(ordered, 0, statements, first, ordered.Length);
                first = end - 1;
            }
            return block with { Statements = statements };
        }).ToArray() };
    }

    /// <summary>仅转发给另一构造函数的完整方法体，可按形参代入继续比较原生内联后的调用。</summary>
    private ManagedInvocation ConstructorOrigin(ManagedInvocation invocation)
    {
        var seen = new HashSet<MethodRef>();
        while (invocation is { Virtual: false, Method.Method.Name: ".ctor" } && seen.Add(invocation.Method)
            && summaries(invocation.Method) is { Body: { Regions.Count: 0, Blocks: [var block] } })
        {
            var forward = block.Statements switch
            {
                [ManagedCall { Tail: true } call] => call,
                [ManagedCall { Tail: false } call, ManagedReturn { Value: null }] => call,
                _ => null,
            };
            if (forward?.Invocation is not { Virtual: false, Method.Method.Name: ".ctor", Receiver: ArgumentValue { Index: -1 } } next
                || next.Arguments.Any(a => a is not (ArgumentValue { Index: >= 0 } or ConstantValue)
                    || a is ArgumentValue argument && argument.Index >= invocation.Arguments.Count)) break;
            invocation = next with
            {
                Method = Instantiated(next.Method, invocation.Method.TypeArguments),
                Receiver = invocation.Receiver,
                Arguments = next.Arguments.Select(a => a is ArgumentValue argument ? invocation.Arguments[argument.Index] : a).ToArray(),
            };
        }
        return invocation;
    }

    private List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>? ConstructorWrites(MethodRef method) =>
        summaries(method) is { Body: { Regions.Count: 0 } template } && method.DeclaringType is DefinitionRef structure
            ? ConstructorWrites(template, structure) : null;

    /// <summary>
    /// 值类型构造函数沿唯一路径对 this 的写入：字段链与写入的值（模板的项）。整体写入的组合值按叶子展开，缺省叶子为零；
    /// 同一字段的后一次写入代替前一次，写入已整体写过的字段的内部不成立。不能求值时为 null。
    /// </summary>
    private List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>? ConstructorWrites(ManagedBody template, DefinitionRef structure)
    {
        var walker = new Walker { Blocks = template.Blocks.ToDictionary(b => b.Address), Caller = false, Block = template.Blocks[0].Address, Index = 0 };
        walker.Visited.Add(walker.Block);
        var writes = new List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>();
        bool Write(IReadOnlyList<FieldRef> path, ManagedValue value)
        {
            if (writes.Any(w => w.Path.Count < path.Count && path.Take(w.Path.Count).SequenceEqual(w.Path))) return false;
            writes.RemoveAll(w => w.Path.Count >= path.Count && w.Path.Take(path.Count).SequenceEqual(path));
            writes.Add((path, value));
            return true;
        }
        for (var steps = 0; steps < 256; steps++)
        {
            if (!Advance(walker, null)) return null;
            switch (walker.Current)
            {
                case ManagedReturn { Value: null }:
                    return writes;
                case ManagedStore store:
                    {
                        if (Term(walker, store.Value) is not { } value || !Plain(value)) return null;
                        if (store.Target is IndirectValue { Address: ArgumentValue { Index: -1 } } && value is ComposedValue composed)
                        {
                            foreach (var (path, type, _) in types.Leaves(structure))
                                if (!Write(path, composed.Leaves.FirstOrDefault(l => l.Path.SequenceEqual(path)).Value ?? new ConstantValue(0, type, Width(type)))) return null;
                        }
                        else if (ThisPath(walker, store.Target) is not { Count: > 0 } path || !Write(path, value)) return null;
                        walker.Index++;
                        break;
                    }
                default:
                    return null;
            }
        }
        return null;
    }

    /// <summary>项中没有路径上的读取或调用结果。</summary>
    private static bool Plain(ManagedValue value) => value is not (Observed or Returned) && ManagedValues.Children(value).All(Plain);

    /// <summary>写入目标相对 this 的字段链：字段、取地址、读取与模板局部按其项展开；根须为 this。</summary>
    private static IReadOnlyList<FieldRef>? ThisPath(Walker walker, ManagedValue target)
    {
        var path = new List<FieldRef>();
        for (var steps = 0; steps < 32; steps++)
            switch (target)
            {
                case FieldValue field: path.Insert(0, field.Field); target = field.Receiver; break;
                case AddressValue address: target = address.Target; break;
                case Observed observed: target = observed.Read; break;
                case LocalValue local when walker.Env.TryGetValue(local.Variable, out var bound): target = bound; break;
                case ArgumentValue { Index: -1 }: return path;
                default: return null;
            }
        return null;
    }
}
