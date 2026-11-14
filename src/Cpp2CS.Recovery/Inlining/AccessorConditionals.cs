using System.Collections.Immutable;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Inlining;

internal sealed record AccessorParameter(int Index) : AtomIdentity
{ public override string StableText => "inline.parameter"; }
internal sealed record AccessorField(FieldRef Field, Term? Receiver) : AtomIdentity
{ public override string StableText => "inline.field"; }
public sealed record AccessorCondition(Term Value, bool Positive);
public sealed record AccessorPath(IReadOnlyList<AccessorCondition> Conditions, Term Value);
public sealed record AccessorConditional(IReadOnlyList<AccessorPath> Paths, IReadOnlyList<ManagedValue> Anchors);

/// <summary>纯模板投影到内核快照；区域、返回边与路径条件均由公共查询给出。</summary>
internal static class AccessorConditionals
{
    public static AccessorTemplateResult Read(ManagedBody body)
    {
        AccessorTemplateResult No(string text) => new(AccessorTemplateStatus.NotTemplate,
            Failure: new("inline.Accessor.None", "候选的方法体不是模板：Conditional；" + text));
        if (body.Regions.Count != 0 || body.Blocks.Count == 0) return No("含异常区域或没有入口");
        var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
        if (statements.Any(s => s is not (ManagedAssignment or ManagedJump or ManagedBranch or ManagedReturn)))
            return No("含调用、写入或其他事件");
        if (statements.SelectMany(ManagedValues.Of).Any(v => !AccessorTemplates.IsPure(body.Method, v, true)))
            return No("含未支持的条件或结果表达式");
        var assigned = statements.OfType<ManagedAssignment>().GroupBy(a => a.Target.Id).ToArray();
        if (assigned.Any(g => g.Count() != 1 || g.First().ExceptionArrival)) return No("局部不是单定义");
        var definitions = assigned.ToDictionary(g => g.Key, g => g.First().Value);
        var blocks = body.Blocks.ToDictionary(b => b.Address, _ => new BlockIdentity());
        var edges = body.Blocks.SelectMany(b => b.Statements.OfType<ManagedJump>().Select(j => (Source: b.Address, Edge: j.Edge))
            .Concat(b.Statements.OfType<ManagedBranch>().SelectMany(br => new[] { (Source: b.Address, Edge: br.Taken), (Source: b.Address, Edge: br.Fallthrough) }))).ToArray();
        if (edges.Any(e => !blocks.ContainsKey(e.Edge.Target))) return No("出边不属于模板");
        var terms = new TermTable(); var entry = new BlockIdentity(); var exit = new BlockIdentity();
        var builder = new FunctionBuilder(terms, entry, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
        var copies = edges.SelectMany(e => e.Edge.Copies.Select(copy => (e.Source, e.Edge.Target, Copy: copy))).ToArray();
        var merged = copies.GroupBy(c => (c.Target, c.Copy.Target.Id)).ToDictionary(g => g.Key,
            g => (Identity: new MergeIdentity(), Width: g.First().Copy.Target.Width));
        if (merged.Keys.Any(k => definitions.ContainsKey(k.Id)) || merged.Values.Any(v => v.Width is <= 0 or > 64)) return No("合流局部重复定义或不是标量");
        var localMerges = merged.GroupBy(p => p.Key.Id).ToArray();
        if (localMerges.Any(g => g.Count() != 1)) return No("合流局部有多个定义点");
        var mergeValues = localMerges.ToDictionary(g => g.Key, g => terms.Atom(new ResultAtom(g.First().Value.Identity), g.First().Value.Width));
        var values = statements.SelectMany(ManagedValues.Of).Concat(copies.Select(c => c.Copy.Value)).SelectMany(ManagedValues.Walk).ToArray();
        var widths = values.OfType<ArgumentValue>().GroupBy(a => a.Index).ToDictionary(g => g.Key, g => g.Max(a => a.Width));
        var fields = values.OfType<FieldValue>().Select(f => (f.Field, f.Width)).Concat(values.OfType<StaticFieldValue>().Select(f => (f.Field, f.Width)))
            .GroupBy(f => f.Field).ToDictionary(g => g.Key, g => g.Max(f => f.Width));
        if (fields.Count == 0) return No("没有字段锚点");
        var active = new HashSet<LocalId>(); var cached = new Dictionary<LocalId, Term>();
        AccessorTerms? interpreter = null;
        Term? Local(LocalValue local)
        {
            if (mergeValues.TryGetValue(local.Id, out var merge)) return merge;
            if (cached.TryGetValue(local.Id, out var known)) return known;
            if (!definitions.TryGetValue(local.Id, out var definition) || !active.Add(local.Id)) return null;
            var value = interpreter!.Read(definition); active.Remove(local.Id);
            if (value is not null) cached.Add(local.Id, value);
            return value;
        }
        var fieldSymbols = new List<AccessorField>();
        Term? Field(FieldRef field, Term? receiver)
        {
            if (fields.GetValueOrDefault(field) is not (> 0 and <= 64)) return null;
            var symbol = new AccessorField(field, receiver); fieldSymbols.Add(symbol);
            return terms.Atom(symbol, fields[field]);
        }
        interpreter = new(terms, i => widths.TryGetValue(i, out var width) ? terms.Atom(new AccessorParameter(i), width) : null,
            Field, Local);
        Term? Condition(ManagedValue value) => interpreter.Read(value) is { } term
            ? term.Width == 1 ? term : terms.Apply(new CoreOperator(CoreOperation.NotEqual), 1, term, terms.Constant(0, term.Width)) : null;
        var conditions = new List<Term>(); var returned = new List<(BlockIdentity Block, Term Value)>();
        builder.Blocks.Add(new(entry, [], [], new Jump(blocks[body.Blocks[0].Address])));
        foreach (var block in body.Blocks)
        {
            if (block.Statements.SkipLast(1).Any(s => s is not ManagedAssignment)) return No("控制转移不在块末尾");
            var merges = new List<Merge>();
            foreach (var pair in merged.Where(p => p.Key.Target == block.Address))
            {
                var inputs = copies.Where(c => c.Target == pair.Key.Target && c.Copy.Target.Id == pair.Key.Id).ToArray();
                if (inputs.GroupBy(i => i.Source).Any(g => g.Count() != 1)) return No("同一边对合流有多次赋值");
                var incoming = inputs.Select(i => (Block: blocks[i.Source], Value: interpreter.Read(i.Copy.Value))).ToArray();
                if (incoming.Any(i => i.Value is null)) return No("合流来源不是纯项");
                merges.Add(new(pair.Value.Identity, mergeValues[pair.Key.Id], incoming.Select(i => new Incoming(i.Block, i.Value!)).ToImmutableArray()));
            }
            Terminator end;
            switch (block.Statements.LastOrDefault())
            {
                case ManagedJump jump: end = new Jump(blocks[jump.Edge.Target]); break;
                case ManagedBranch branch when Condition(branch.Condition) is { } condition:
                    conditions.Add(condition); end = new Branch(condition, blocks[branch.Taken.Target], blocks[branch.Fallthrough.Target]); break;
                case ManagedReturn { Value: { } result } when interpreter.Read(result) is { } value:
                    returned.Add((blocks[block.Address], value)); end = new Jump(exit); break;
                default: return No("缺少纯分支、跳转或有值返回");
            }
            builder.Blocks.Add(new(blocks[block.Address], merges.ToImmutableArray(), [], end));
        }
        builder.Blocks.Add(new(exit, [], [], new Return([])));
        var snapshot = builder.Freeze(); var state = new StateQueries(); var context = state.CreateContext(snapshot); var flow = new FlowQueries();
        var region = context.Get(new SnapshotRegionQuery(flow), new(entry, exit));
        if (!region.IsSuccess) return No("区域不是单入口无环完整返回区域：" + region.Why!.Message);
        var facts = new PathFactQuery(state); var incomingValues = new IncomingValuesQuery(state); var paths = new List<AccessorPath>();
        void Expand(Term value, List<AccessorCondition> guards)
        {
            if (value.Operator is CoreOperator { Operation: CoreOperation.Select })
            {
                conditions.Add(value.Operands[0]);
                Expand(value.Operands[1], [.. guards, new(value.Operands[0], true)]);
                Expand(value.Operands[2], [.. guards, new(value.Operands[0], false)]);
            }
            else paths.Add(new(guards, value));
        }
        foreach (var result in returned)
        {
            var inputs = context.Get(incomingValues, new(result.Value, result.Block));
            if (!inputs.IsSuccess) return No("返回值的入边投影失败");
            var points = inputs.Value.IsEmpty ? new[] { (Block: result.Block, Value: result.Value, Edge: (FlowEdge?)null) }
                : inputs.Value.Select(i => (Block: i.Predecessor, i.Value, Edge: (FlowEdge?)new FlowEdge(i.Predecessor, result.Block))).ToArray();
            foreach (var point in points)
            {
                if (SnapshotRewrite.Dependencies([point.Value]).Any(t => t.Identity is ResultAtom)) return No("返回项仍含未投影的合流");
                var guards = new List<AccessorCondition>();
                foreach (var condition in conditions.Distinct().ToArray())
                {
                    var truth = context.Get(facts, new(new Point(point.Block, 0), condition, point.Edge));
                    if (!truth.IsSuccess) return No("返回路径事实查询失败");
                    if (truth.Value != PathTruth.Unknown) guards.Add(new(condition, truth.Value == PathTruth.True));
                }
                Expand(point.Value, guards);
            }
        }
        if (paths.Count is < 2 or > 3) return No("返回路径数不在二至三条内");
        var predicates = paths.SelectMany(p => p.Conditions).Select(g => g.Value).Distinct().ToArray();
        if (predicates.Length > 2) return No("条件组合超过三条返回路径的证明范围");
        for (int bits = 0; bits < 1 << predicates.Length; bits++)
            if (paths.Count(p => p.Conditions.All(g => (((bits >> Array.IndexOf(predicates, g.Value)) & 1) != 0) == g.Positive)) != 1)
                return No("路径条件没有形成互斥且完整的划分");
        var anchors = fieldSymbols.Distinct().Where(f => f.Receiver?.Identity is AccessorParameter).Select(f => (ManagedValue)new FieldValue(
                new ArgumentValue(((AccessorParameter)f.Receiver!.Identity!).Index, f.Field.DeclaringType, f.Receiver!.Width), f.Field, f.Field.Field.Type, fields[f.Field])).ToArray();
        return new(AccessorTemplateStatus.Complete, new(AccessorKind.Getter, fields.Keys.First())
        { Fields = fields.Keys.ToArray(), Conditional = new(paths, anchors) });
    }
}
