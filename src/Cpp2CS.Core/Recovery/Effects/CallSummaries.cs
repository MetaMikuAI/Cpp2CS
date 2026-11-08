using Cpp2CS.Ir;
using Cpp2CS.Managed;

namespace Cpp2CS.Recovery.Effects;

/// <summary>
/// 托管调用对堆的摘要：返回路径上可能写的实例字段（按实参代入后的声明类型），
/// 每条返回路径上都写入同一常量的字段，以及每条返回路径上都等于调用前内容加同一常量的字段（如 _version++）。
/// 摘要之外的堆位置，调用前后内容不变。
/// </summary>
internal sealed record CallSummary(IReadOnlyList<FieldRef> Writes, IReadOnlyList<(FieldValue Location, ConstantValue Value)> Stores,
    IReadOnlyList<(FieldValue Location, ConstantValue Step)> Increments);

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
        if (bodies(invocation.Method) is not { } body) return new(writes, [], []);
        var (stores, increments) = Contents(body, invocation);
        return new(writes, stores, increments);
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

    /// <summary>this 的字段在返回时的内容：常量，或调用前的内容加常量（Relative）。调用前的内容本身记为相对 0，不带宽度。</summary>
    private readonly record struct Content(bool Relative, ulong Bits, int Width)
    {
        public static readonly Content Unchanged = new(true, 0, 0);

        public Content Add(ulong step, int width)
        {
            var bits = (Bits + step) & Expr.Mask(width);
            return Relative && bits == 0 ? Unchanged : new(Relative, bits, width);
        }
    }

    /// <summary>
    /// 路径上 this 各字段的内容与读入局部的字段内容。没有记录的字段：失效（Havoc）之前未被写过，即调用前的内容；失效之后未知。
    /// 值为 null 的字段内容未知。
    /// </summary>
    private sealed class PathContents
    {
        public Dictionary<FieldDef, Content?> Fields { get; init; } = [];
        public Dictionary<Variable, (FieldDef Field, Content Value)> Locals { get; init; } = [];
        public bool Havoc { get; private set; }
        public PathContents Copy() => new() { Fields = new(Fields), Locals = new(Locals), Havoc = Havoc };

        public Content? Current(FieldDef field) => Fields.TryGetValue(field, out var known) ? known : Havoc ? null : Content.Unchanged;

        public void Invalidate()
        {
            Fields.Clear();
            Havoc = true;
        }

        /// <summary>并入另一条路径的内容，两边不同的成为未知；返回是否有变化。</summary>
        public bool Merge(PathContents other)
        {
            var changed = false;
            foreach (var field in Fields.Keys.Union(other.Fields.Keys).ToArray())
            {
                var mine = Current(field);
                var merged = mine == other.Current(field) ? mine : null;
                if (!Fields.TryGetValue(field, out var before) || before != merged) changed = true;
                Fields[field] = merged;
            }
            // 两边都没有记录的字段在另一条路径上未知。
            if (other.Havoc && !Havoc) Havoc = changed = true;
            foreach (var (variable, value) in Locals.ToArray())
                if (!other.Locals.TryGetValue(variable, out var theirs) || theirs != value) { Locals.Remove(variable); changed = true; }
            return changed;
        }
    }

    /// <summary>
    /// 方法体在每条返回路径上对 this 的字段留下的内容：同一常量，或调用前的内容加同一常量（读取 this.f，加常量后写回 this.f）。
    /// 对其他接收者的同一字段的写入使内容未知；路径上的调用（只写数组元素的库方法除外）和未知语句使全部内容未知。
    /// </summary>
    private static (IReadOnlyList<(FieldValue Location, ConstantValue Value)> Stores, IReadOnlyList<(FieldValue Location, ConstantValue Step)> Increments)
        Contents(ManagedBody template, ManagedInvocation invocation)
    {
        if (invocation.Receiver is null || template.Blocks.Count == 0) return ([], []);
        var byAddress = template.Blocks.ToDictionary(b => b.Address);
        var entries = new Dictionary<ulong, PathContents> { [template.Blocks[0].Address] = new() };
        var pending = new Queue<ulong>([template.Blocks[0].Address]);
        PathContents? result = null;
        static bool Self(ManagedValue receiver) => receiver is ArgumentValue { Index: -1 };
        // 值相对 this.f 的内容：常量、this.f 的读取、持有它的局部，或后三者加常量。
        static Content? Of(ManagedValue value, FieldValue target, PathContents facts) => value switch
        {
            ConstantValue constant when constant.Width == target.Width => new Content(false, constant.Bits & Expr.Mask(target.Width), target.Width),
            FieldValue { Receiver: var receiver } read when Self(receiver) && ReferenceEquals(read.Field.Field, target.Field.Field) && read.Width == target.Width
                => facts.Current(target.Field.Field),
            LocalValue local when local.Width == target.Width && facts.Locals.TryGetValue(local.Variable, out var held) && ReferenceEquals(held.Field, target.Field.Field)
                => held.Value,
            BinaryValue { Op: BinOp.Add, Right: ConstantValue step } add when add.Width == target.Width && target.Width is 8 or 16 or 32 or 64
                => Of(add.Left, target, facts)?.Add(step.Bits, target.Width),
            _ => null,
        };
        while (pending.TryDequeue(out var address))
        {
            var facts = entries[address].Copy();
            foreach (var statement in byAddress[address].Statements)
            {
                if (ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).Any(v => ManagedEffects.Value(v).InvalidatesMemory)) facts.Invalidate();
                switch (statement)
                {
                    case ManagedStore { Target: FieldValue written } store:
                        var content = Self(written.Receiver) ? Of(store.Value, written, facts) : null;
                        // 写入值类型字段的成员也改变了外层字段。
                        for (var outer = written.Receiver; outer is FieldValue or AddressValue;)
                        {
                            if (outer is AddressValue { Target: var inner }) { outer = inner; continue; }
                            var field = (FieldValue)outer;
                            facts.Fields[field.Field.Field] = null;
                            outer = field.Receiver;
                        }
                        facts.Fields[written.Field.Field] = content;
                        break;
                    case ManagedAssignment assignment:
                        facts.Locals.Remove(assignment.Target.Variable);
                        if (assignment.Value is FieldValue read && Self(read.Receiver) && read.Width == assignment.Target.Width && facts.Current(read.Field.Field) is { } held)
                            facts.Locals[assignment.Target.Variable] = (read.Field.Field, held);
                        break;
                    case ManagedCall { Invocation.Method.Method: var called } call when ArrayOnly(called):
                        if (call.Result is { } returned) facts.Locals.Remove(returned.Variable);
                        break;
                    case ManagedStore { Target: ArrayElementValue or StaticFieldValue }:
                    case ManagedCheck or ManagedBranch or ManagedJump or ManagedSwitch or ManagedThrow:
                        break;
                    case ManagedReturn:
                        if (result is null) result = facts.Copy();
                        else result.Merge(facts);
                        break;
                    default:
                        facts.Invalidate();
                        facts.Locals.Clear();
                        break;
                }
                foreach (var edge in ManagedValues.Edges(statement))
                {
                    if (!byAddress.ContainsKey(edge.Target)) continue;
                    var arriving = facts.Copy();
                    foreach (var copy in edge.Copies) arriving.Locals.Remove(copy.Target.Variable);
                    if (!entries.TryGetValue(edge.Target, out var known))
                    {
                        entries[edge.Target] = arriving;
                        pending.Enqueue(edge.Target);
                    }
                    else if (known.Merge(arriving)) pending.Enqueue(edge.Target);
                }
            }
        }
        if (result is null) return ([], []);
        var owner = invocation.Method.Method.Owner;
        var stores = new List<(FieldValue, ConstantValue)>();
        var increments = new List<(FieldValue, ConstantValue)>();
        foreach (var (field, content) in result.Fields)
        {
            if (content is not { Width: > 0 } known || !ReferenceEquals(field.Owner, owner)) continue;
            var type = invocation.Method.Concrete(field.Type);
            var location = new FieldValue(invocation.Receiver, new FieldRef(field, invocation.Method.DeclaringType), type, known.Width);
            var value = new ConstantValue(known.Bits, type, known.Width);
            if (known.Relative) increments.Add((location, value));
            else stores.Add((location, value));
        }
        return (stores, increments);
    }
}
