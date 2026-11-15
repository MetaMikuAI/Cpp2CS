using System.Collections.Immutable;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Inlining;

public abstract record AccessorEvent;
public sealed record AccessorFieldWrite(FieldRef Field, Term Receiver, Term Value) : AccessorEvent;
public sealed record AccessorInvocation(MethodRef Method, bool Virtual, Term? Receiver, IReadOnlyList<Term> Arguments) : AccessorEvent;
public sealed record AccessorEventPath(IReadOnlyList<AccessorCondition> Conditions, IReadOnlyList<AccessorEvent> Events, Term? Result);
public sealed record AccessorEventTemplate(IReadOnlyList<AccessorEventPath> Paths, IReadOnlyList<ManagedValue> Anchors);

/// <summary>带事件的托管体投影到公共快照；路径由内核区域查询展开。</summary>
internal static class AccessorEventTemplates
{
    public static AccessorTemplateResult Read(ManagedBody body)
    {
        AccessorTemplateResult No(string text) => new(AccessorTemplateStatus.NotTemplate,
            Failure: new("inline.Accessor.None", "候选的方法体不是模板：Conditional；" + text));
        if (body.Regions.Count != 0 || body.Blocks.Count == 0) return No("含异常区域或没有入口");
        var all = body.Blocks.SelectMany(b => b.Statements).ToArray();
        if (all.Any(s => s is not (ManagedAssignment or ManagedStore or ManagedCall or ManagedBranch or ManagedJump or ManagedReturn)))
            return No("含显式抛出路径或未支持的事件");
        if (all.SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk).Any(v => v is ArrayElementValue or ArrayLengthValue))
            return No("数组访问的隐含检查缺少模板来源凭据");
        var assignments = all.OfType<ManagedAssignment>().ToArray();
        if (assignments.Any(a => a.ExceptionArrival) || assignments.GroupBy(a => a.Target.Id).Any(g => g.Count() != 1))
            return No("局部不是单定义");
        var definitions = assignments.ToDictionary(a => a.Target.Id, a => a.Value);
        var edges = all.OfType<ManagedJump>().Select(j => j.Edge).Concat(all.OfType<ManagedBranch>().SelectMany(b => new[] { b.Taken, b.Fallthrough })).ToArray();
        if (edges.Any(e => e.Copies.Count != 0)) return No("事件模板的局部含合流");
        var active = new HashSet<LocalId>(); bool invalid = false;
        ManagedValue Normalize(ManagedValue value)
        {
            if (value is LocalValue local)
            {
                if (!definitions.TryGetValue(local.Id, out var source) || !active.Add(local.Id)) { invalid = true; return value; }
                var result = Normalize(source); active.Remove(local.Id); return result;
            }
            return ManagedValues.Map(value, Normalize);
        }
        bool Pure(ManagedValue value) => AccessorTemplates.IsPure(body.Method, value)
            && ManagedValues.Walk(value).All(v => v is not StaticFieldValue && (v is not FieldValue field || field.Receiver is ArgumentValue { Index: -1 }));
        var terms = new TermTable(); var entry = new BlockIdentity(); var exit = new BlockIdentity();
        var builder = new FunctionBuilder(terms, entry, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
        var blocks = body.Blocks.ToDictionary(b => b.Address, _ => new BlockIdentity());
        if (edges.Any(e => !blocks.ContainsKey(e.Target))) return No("出边不属于模板");
        var fields = new Dictionary<FieldRef, ManagedValue>();
        var widths = all.SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk).OfType<ArgumentValue>()
            .GroupBy(a => a.Index).ToDictionary(g => g.Key, g => g.Max(a => a.Width));
        var interpreter = new AccessorTerms(terms, i => widths.TryGetValue(i, out int width) ? terms.Atom(new AccessorParameter(i), width) : null,
            (field, receiver) => terms.Atom(new AccessorField(field, receiver), all.SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk)
                .Where(v => FieldAccessor.FieldOf(v)?.Equals(field) == true).Max(v => v.Width)));
        Term? Read(ManagedValue value)
        {
            value = Normalize(value);
            foreach (var field in ManagedValues.Walk(value).OfType<FieldValue>())
                if (field.Receiver is ArgumentValue { Index: -1 }) fields.TryAdd(field.Field, field);
            if (!Pure(value)) return null;
            return interpreter.Read(value);
        }
        var events = new Dictionary<Point, AccessorEvent>();
        var returned = new Dictionary<BlockIdentity, Term?>();
        builder.Blocks.Add(new(entry, [], [], new Jump(blocks[body.Blocks[0].Address])));
        foreach (var block in body.Blocks)
        {
            var statements = new List<Statement>();
            foreach (var statement in block.Statements.SkipLast(1))
            {
                var point = new Point(blocks[block.Address], statements.Count);
                AccessorEvent? effect = null;
                switch (statement)
                {
                    case ManagedAssignment a when Read(a.Value) is not null: break;
                    case ManagedStore store:
                        var target = Normalize(store.Target); var value = Read(store.Value);
                        if (target is FieldValue { Receiver: ArgumentValue { Index: -1 } } field && Read(field.Receiver) is { } self && value is not null)
                        {
                            fields.TryAdd(field.Field, field); effect = new AccessorFieldWrite(field.Field, self, value);
                        }
                        else return No("写入不是 this 字段");
                        break;
                    case ManagedCall { Result: null, Invocation.Constraint: null } call:
                        var args = call.Invocation.Arguments.Select(Read).ToArray();
                        var receiver = call.Invocation.Receiver is { } r ? Read(r) : null;
                        if (args.Any(a => a is null) || call.Invocation.Receiver is not null && receiver is null) return No("调用实参不是纯项");
                        effect = new AccessorInvocation(call.Invocation.Method, call.Invocation.Virtual, receiver, args.OfType<Term>().ToArray()); break;
                    default: return No("含未支持的局部、调用结果或事件");
                }
                statements.Add(new MemoryWrite(new(), terms.Constant(0, 64), 1, terms.Constant(0, 1)));
                if (effect is not null) events.Add(point, effect);
            }
            Terminator end;
            switch (block.Statements.LastOrDefault())
            {
                case ManagedJump jump: end = new Jump(blocks[jump.Edge.Target]); break;
                case ManagedBranch branch when Read(branch.Condition) is { } condition:
                    end = new Branch(interpreter.Truth(condition), blocks[branch.Taken.Target], blocks[branch.Fallthrough.Target]); break;
                case ManagedReturn result:
                    var value = result.Value is null ? null : Read(result.Value);
                    if (result.Value is not null && value is null) return No("返回值不是纯项");
                    returned.Add(blocks[block.Address], value); end = new Jump(exit); break;
                default: return No("控制转移不在块末尾");
            }
            builder.Blocks.Add(new(blocks[block.Address], [], statements.ToImmutableArray(), end));
        }
        if (invalid || fields.Count == 0) return No("局部依赖不完整或没有 this 字段锚点");
        builder.Blocks.Add(new(exit, [], [], new Return([])));
        var snapshot = builder.Freeze(); var context = new QueryContext(snapshot);
        var paths = context.Get(new SnapshotPathsQuery(new FlowQueries(false)), new(new(entry, 0), exit));
        if (!paths.IsSuccess) return No("不是单入口无环返回区域：" + paths.Why!.Message);
        var byId = snapshot.Blocks.ToDictionary(b => b.Identity); var resultPaths = new List<AccessorEventPath>();
        foreach (var path in paths.Value)
        {
            var effects = path.Points.Where(events.ContainsKey).Select(p => events[p]).ToArray();
            if (effects.OfType<AccessorInvocation>().Count() > 1) return No("路径上的调用多于一次");
            var written = new HashSet<FieldRef>(); bool called = false;
            foreach (var edge in path.Edges.Where(e => e.Source != entry))
            {
                var original = body.Blocks.Single(b => blocks[b.Address] == edge.Source);
                foreach (var statement in original.Statements)
                {
                    var inputs = statement is ManagedStore store ? new[] { store.Value }.Concat(store.Target is ArrayElementValue a ? new[] { a.Array, a.Index } : [])
                        : ManagedValues.Of(statement);
                    if (inputs.SelectMany(ManagedValues.Walk).OfType<FieldValue>().Any(f => called || written.Contains(f.Field)))
                        return No("写入或调用之后直接重读字段，缺少模板内存版本");
                    if (statement is ManagedStore { Target: FieldValue write }) written.Add(write.Field);
                    called |= statement is ManagedCall;
                }
            }
            var guards = path.Edges.Where(e => byId[e.Source].End is Branch).Select(e =>
            {
                var branch = (Branch)byId[e.Source].End; return new AccessorCondition(branch.Condition, branch.True == e.Target);
            }).ToArray();
            resultPaths.Add(new(guards, effects, returned[path.Edges[^1].Source]));
        }
        return new(AccessorTemplateStatus.Complete, new(ManagedTypes.IsVoid(body.Method.Method.ReturnType) ? AccessorKind.Setter : AccessorKind.Getter, fields.Keys.First())
        { Fields = fields.Keys.ToArray(), Events = new(resultPaths, fields.Values.ToArray()) });
    }
}
