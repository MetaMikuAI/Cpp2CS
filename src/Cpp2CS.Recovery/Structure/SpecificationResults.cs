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
        SlotContentsRewrite? mergedSlots = null;
        SemanticUses? slotUses = null;
        bool MergedAddress(Term address, out Term resolved)
        {
            resolved = address;
            if (address.Identity is not ResultAtom && address.Operator is not CoreOperator { Operation: CoreOperation.Select }) return false;
            var value = c.Get(state.Resolve, address); resolved = value.IsSuccess ? value.Value : address;
            return value.IsSuccess && (resolved.Identity is ResultAtom { Definition: MergeIdentity }
                || resolved.Operator is CoreOperator { Operation: CoreOperation.Select });
        }
        void Project(Term address, Term result, Statement statement)
        {
            mergedSlots ??= new(c, new(state, names, input.Blocks.SelectMany(b => b.Merges.Select(m => (b.Identity, Merge: m)))
                .ToDictionary(p => p.Merge.Result, p => (p.Identity, p.Merge))));
            var proof = mergedSlots.Prove(address);
            if (!proof.IsSuccess)
            {
                records.Add(new("merged-slot", statement.Trace?.NativeAddress, proof.Why!.Message, false) { Reason = proof.Why });
                return;
            }
            edit.Replacements[result] = mergedSlots.Materialize(proof.Value);
            if (statement is MemoryRead) edit.RemovedStatements.Add(statement);
            records.Add(new("merged-slot", statement.Trace?.NativeAddress, "已解码槽的稳定内容按地址合流的同一入边或原选择条件分配", true));
        }
        foreach (var block in input.Blocks)
        {
            var statements = ImmutableArray.CreateBuilder<Statement>();
            foreach (var statement in block.Statements)
            {
                statements.Add(statement);
                if (statement is MemoryRead { Acquire: false } read && read.Width == input.AddressWidth && names.Slots.Count != 0
                    && MergedAddress(read.Address, out var readAddress)
                    && (slotUses ??= new(c, calls, state, names.Binder, names.Entry)).ImageAddresses(readAddress, c, state).Any(names.Slots.ContainsKey))
                    Project(read.Address, read.Result, read);
                if (statement is not Call call || call.DoesNotReturn) continue;
                var classified = c.Get(calls, call.Identity);
                if (!classified.IsSuccess || classified.Value.Operation is not { DoesNotReturn: false } operation) continue;
                // 已知实体的元数据初始化返回同一实体。
                if (operation.MetadataInitialization is { } metadata
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
                if (MergedAddress(resolved.Value, out var mergedAddress))
                {
                    Project(address.Term, result.Term, call);
                    continue;
                }
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
        if (edit.Replacements.Count == 0) return input;
        mergedSlots?.Publish(edit);
        var rewritten = edit.Apply();
        if (mergedSlots is { PathEntities.Count: > 0 })
        {
            var mapped = new Dictionary<Term, Term>();
            Term Map(Term term)
            {
                if (mapped.TryGetValue(term, out var value)) return value;
                return mapped[term] = edit.Replacements.TryGetValue(term, out var replacement) && replacement != term
                    ? Map(replacement) : SnapshotRewrite.Rebuild(term, Map);
            }
            RecordPathEntities(rewritten, mergedSlots.PathEntities.Select(Map).ToHashSet(), records);
        }
        return rewritten;
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
