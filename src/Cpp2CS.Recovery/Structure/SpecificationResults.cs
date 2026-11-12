using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Structure;

public sealed partial class UnobservableEffects
{
    private NativeFunction ReplaceSpecificationResults(NativeFunction input, List<StructureRecord> records, out QueryContext context)
    {
        var c = names.CreateContext(input); context = c;
        HashSet<Term>? uses = null;
        var edit = new SnapshotRewrite(input);
        foreach (var block in input.Blocks)
        {
            var statements = ImmutableArray.CreateBuilder<Statement>();
            foreach (var statement in block.Statements)
            {
                statements.Add(statement);
                if (statement is not Call call || call.DoesNotReturn) continue;
                var classified = c.Get(calls, call.Identity);
                if (!classified.IsSuccess || classified.Value.Operation is not { DoesNotReturn: false } operation) continue;
                // 只在有效开放上下文中应用元数据初始化的恒等结果；不改变其他入口的恢复结果。
                if (names.DefinitionMethod is not null && operation.MetadataInitialization is { } metadata
                    && operation.Result.ReturnInput is { } sameInput
                    && classified.Value.Inputs?.GetValueOrDefault(sameInput)?.Source is TermSource identity
                    && classified.Value.Result?.Source is TermSource output
                    && output.Term.Width == identity.Term.Width && c.Get(names, identity.Term) is { IsSuccess: true } identityName
                    && names.ContextEntity(identityName.Value.Name))
                {
                    edit.Replacements[output.Term] = identity.Term;
                    records.Add(new("specification-result", call.Trace?.NativeAddress, metadata.Evidence, true));
                    continue;
                }
                if (operation.Result.Relation is not { Kind: RuntimeResultRelationKind.ResolvedPointee, Input: { } inputName }
                    || classified.Value.Inputs?.GetValueOrDefault(inputName)?.Source is not TermSource address
                    || classified.Value.Result?.Source is not TermSource result
                    || result.Term.Width != input.AddressWidth
                    || !call.Results.Any(r => r.Value == result.Term)) continue;
                uses ??= SnapshotRewrite.Dependencies(input.Blocks.SelectMany(b => b.Statements.SelectMany(SnapshotRewrite.Uses)
                    .Concat(EndUses(b.End)).Concat(b.Merges.SelectMany(m => m.Inputs.Select(i => i.Value)))));
                if (!uses.Contains(result.Term)) continue;
                var resolved = c.Get(state.Resolve, address.Term);
                if (!resolved.IsSuccess) continue;
                var location = c.Get(state.Locations, new(resolved.Value, result.Term.Width));
                if (!location.IsSuccess) continue;
                var named = c.Get(names, input.Terms.Atom(new MemoryAtom(location.Value, null), result.Term.Width));
                // 解析失败可以返回空而不发布槽；只有能解码的有效实体才满足此等式。
                if (!named.IsSuccess || named.Value.Name is not EntityName) continue;
                var id = new ReadIdentity(); var value = input.Terms.Atom(new ResultAtom(id), result.Term.Width);
                statements.Add(new MemoryRead(id, address.Term, value.Width, value) { Trace = call.Trace });
                edit.Replacements[result.Term] = value;
                records.Add(new("specification-result", call.Trace?.NativeAddress, operation.Result.Relation.Evidence!, true));
            }
            if (statements.Count != block.Statements.Length)
                edit.Blocks[block.Identity] = block with { Statements = statements.ToImmutable() };
        }
        return edit.Replacements.Count == 0 ? input : edit.Apply();
    }

    private sealed record GuardedEvent(Block Join, ImmutableArray<BlockIdentity> Inside, Call Event, string Evidence);

    private GuardedEvent? Guarded(QueryContext c, Block head, IReadOnlyDictionary<BlockIdentity, Block> blocks,
        IReadOnlyDictionary<BlockIdentity, HashSet<BlockIdentity>> predecessors, out string? failure)
    {
        failure = null;
        var branch = (Branch)head.End;
        foreach (var (eventId, skipId, whenTrue) in new[] { (branch.True, branch.False, true), (branch.False, branch.True, false) })
        {
            var arm = blocks[eventId];
            if (arm.End is not Jump jump || jump.Target == head.Identity || jump.Target == eventId || arm.Handler is not null || arm.Merges.Length != 0
                || arm.Statements.OfType<Call>().ToArray() is not [var call]
                || call.DoesNotReturn || call.Unwind is not null
                || arm.Statements.Any(s => s is not MemoryRead && s != call)) continue;
            var inside = ImmutableArray.CreateBuilder<BlockIdentity>(); inside.Add(eventId);
            if (jump.Target != skipId)
            {
                var skip = blocks[skipId];
                if (skip.End is not Jump next || next.Target != jump.Target || !skip.Statements.IsEmpty
                    || !skip.Merges.IsEmpty || skip.Handler is not null) continue;
                inside.Add(skipId);
            }
            if (inside.Any(id => !predecessors[id].SetEquals([head.Identity]))) continue;
            var classified = c.Get(calls, call.Identity);
            if (!classified.IsSuccess || classified.Value.Operation is not
                { Observation: RuntimeObservation.IdempotentEvent, DoesNotReturn: false, Result.Kind: RuntimeValueKind.Void,
                    Idempotence: { } post } operation
                || classified.Value.Function?.Signature?.ReturnType.Size != 0) continue;
            failure = "守卫未证明是该幂等事件的状态测试";
            // 移动调用不移动实参的定义，也不把其余调用或内存效果越过守卫。
            var definitions = arm.Statements.OfType<MemoryRead>().Select(r => r.Result).ToHashSet();
            if (SnapshotRewrite.Dependencies(SnapshotRewrite.Uses(call)).Overlaps(definitions))
            { failure = "事件实参定义在守卫内部"; continue; }
            var resolved = c.Get(state.Resolve, branch.Condition);
            if (!resolved.IsSuccess) continue;
            foreach (var representation in post.Representations)
            {
                if (representation.Record is null || representation.Field is null
                    || representation.Test is not (RuntimeStateTest.Nonzero or RuntimeStateTest.Zero)
                    || classified.Value.Inputs?.GetValueOrDefault(representation.Input)?.Source is not TermSource owner) continue;
                var ownerName = c.Get(names, owner.Term);
                if (!ownerName.IsSuccess || ownerName.Value.Name is null) continue;
                foreach (var term in SnapshotRewrite.Dependencies([resolved.Value]))
                {
                    var named = c.Get(names, term);
                    if (!named.IsSuccess || named.Value.Name is not FieldName field
                        || field.Record != representation.Record || field.Field != representation.Record + "." + representation.Field
                        || field.Index is not null) continue;
                    if (field.Owner != ownerName.Value.Name)
                    { failure = "守卫状态与幂等事件的对象不同"; continue; }
                    var table = c.Snapshot.Terms;
                    var established = table.Apply(new CoreOperator(representation.Test == RuntimeStateTest.Nonzero
                        ? CoreOperation.NotEqual : CoreOperation.Equal), 1, term, table.Constant(0, term.Width));
                    var notEstablished = table.Apply(new CoreOperator(CoreOperation.Equal), 1, established, table.Constant(0, 1));
                    if (resolved.Value != (whenTrue ? notEstablished : established)) continue;
                    return new(blocks[jump.Target], inside.ToImmutable(), call, representation.Evidence + "；" + operation.Evidence);
                }
            }
        }
        return null;
    }
    private void ForwardFixedReads(NativeFunction function, List<StructureRecord> records, QueryContext c, SnapshotRewrite edit)
    {
        var reads = new Dictionary<ValueName, List<(MemoryRead Read, Point Point)>>();
        foreach (var block in function.Blocks)
        for (int i = 0; i < block.Statements.Length; i++)
        {
            if (block.Statements[i] is not MemoryRead read) continue;
            var named = names.FixedValue(c, read.Result);
            if (!named.IsSuccess || named.Value is not { } fixedValue) continue;
            if (!reads.TryGetValue(fixedValue, out var group)) reads[fixedValue] = group = [];
            group.Add((read, new(block.Identity, i)));
        }
        foreach (var group in reads.Values)
        foreach (var (read, point) in group)
        {
            if (edit.RemovedStatements.Contains(read)) continue;
            var previous = group.FirstOrDefault(other => c.Get(flow.PointDominates, new(other.Point, point)) is { IsSuccess: true, Value: true });
            if (previous.Read is null) continue;
            edit.RemovedStatements.Add(read); edit.Replacements[read.Result] = previous.Read.Result;
            records.Add(new("forwarded-read", read.Trace?.NativeAddress, "同一定值的规格读取由支配位置的读取提供", true));
        }
    }
}
