using System.Collections.Immutable;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Structure;

internal sealed record StackProtectionProof(BlockIdentity Pass, Location Source, Location Copy, MemoryWrite Save);

/// <summary>只认帧副本与同一线程或全局保护源的完整比较；失败前沿只能是不返回的栈保护失败。</summary>
internal sealed class StackProtectionQuery(StateQueries state, CallNamingQuery calls) : Query<BlockIdentity, StackProtectionProof?>
{
    private readonly ReadLocationQuery reads = new(state);
    private readonly FlowQueries flow = new();
    public override Outcome<StackProtectionProof?> Compute(QueryContext c, BlockIdentity key)
    {
        Outcome<StackProtectionProof?> None() => Outcome<StackProtectionProof?>.Success(null);
        var block = c.Snapshot.Blocks.Single(b => b.Identity == key);
        if (block.End is not Branch branch) return None();
        var literal = branch.Condition; bool equalWhenTrue = true;
        while (literal.Operator is CoreOperator { Operation: CoreOperation.Not })
        { equalWhenTrue = !equalWhenTrue; literal = literal.Operands[0]; }
        if (literal.Operator is not CoreOperator { Operation: CoreOperation.Equal or CoreOperation.NotEqual } comparison) return None();
        equalWhenTrue ^= comparison.Operation == CoreOperation.NotEqual;
        var left = c.Get(state.Resolve, literal.Operands[0]); var right = c.Get(state.Resolve, literal.Operands[1]);
        if (!left.IsSuccess || !right.IsSuccess || left.Value.Width != c.Snapshot.AddressWidth || left.Value.ContainsUndefined || right.Value.ContainsUndefined) return None();
        var a = c.Get(reads, left.Value); var b = c.Get(reads, right.Value);
        if (!a.IsSuccess || !b.IsSuccess || a.Value != b.Value || a.Value.Region is not (Region.Thread or Region.Image) || a.Value.Offset is null) return None();
        var point = new Point(key, block.Statements.Length);
        MemoryWrite? save = null; Location? storage = null;
        foreach (var owner in c.Snapshot.Blocks)
        for (int i = 0; i < owner.Statements.Length; i++)
        {
            if (owner.Statements[i] is not MemoryWrite write || write.Width != c.Snapshot.AddressWidth) continue;
            var value = c.Get(state.Resolve, write.Value);
            if (!value.IsSuccess || value.Value != left.Value && value.Value != right.Value) continue;
            var address = c.Get(state.Resolve, write.Address);
            var location = address.IsSuccess ? c.Get(state.Locations, new(address.Value, write.Width)) : default;
            if (!location.IsSuccess || location.Value.Region != Region.Frame || location.Value.Offset is null) continue;
            if (c.Get(flow.PointDominates, new(new(owner.Identity, i + 1), point)) is not { IsSuccess: true, Value: true }) continue;
            var contents = c.Get(state.ValueAt, new(point, location.Value));
            if (!contents.IsSuccess || contents.Value != value.Value) continue;
            save = write; storage = location.Value; break;
        }
        if (save is null || storage is null) return None();
        var failed = equalWhenTrue ? branch.False : branch.True;
        var frontier = new EventFrontierQuery((context, position) =>
        {
            var owner = context.Snapshot.Blocks.Single(b => b.Identity == position.Block);
            if (position.Before == owner.Statements.Length) return Outcome<bool>.Success(false);
            var statement = owner.Statements[position.Before];
            if (statement is Call call)
            {
                var named = context.Get(calls, call.Identity);
                return named.IsSuccess ? Outcome<bool>.Success(call.DoesNotReturn || named.Value.Operation is not { Observation: RuntimeObservation.Unobservable })
                    : named.Propagate<bool>();
            }
            if (statement is MemoryRead read)
            {
                var address = context.Get(state.Resolve, read.Address);
                var location = address.IsSuccess ? context.Get(state.Locations, new(address.Value, read.Width)) : default;
                return Outcome<bool>.Success(!location.IsSuccess || location.Value.Region != Region.Frame && location.Value != a.Value);
            }
            return Outcome<bool>.Success(true);
        });
        var result = c.Get(frontier, new(new(failed, 0)));
        if (!result.IsSuccess) return result.Propagate<StackProtectionProof?>();
        if (result.Value.HasCycle || result.Value.ReachesExit || result.Value.Stops.Count == 0)
            return Outcome<StackProtectionProof?>.Failure(new("structure.stack-protection.exit", "保护失败臂有循环或非失败结局。"));
        foreach (var stop in result.Value.Stops)
        {
            var owner = c.Snapshot.Blocks.Single(b => b.Identity == stop.Block);
            if (owner.Statements[stop.Before] is not Call { DoesNotReturn: true, Unwind: null } call
                || c.Get(calls, call.Identity) is not { IsSuccess: true, Value.Operation: { Name: "StackProtectionFailure", DoesNotReturn: true } })
                return Outcome<StackProtectionProof?>.Failure(new("structure.stack-protection.effect", "保护失败前先遇到其他事件或写入。"));
        }
        return Outcome<StackProtectionProof?>.Success(new(equalWhenTrue ? branch.True : branch.False, a.Value, storage, save));
    }
}

public sealed partial class UnobservableEffects
{
    public const string StackProtectionAssumption = "栈保护检查在托管语义下恒成立；托管操作不能破坏自己帧上的保护副本。";
    private readonly StackProtectionQuery protection = new(state, calls);

    private bool FoldStackProtection(QueryContext c, SnapshotRewrite edit, Block block, List<StructureRecord> records)
    {
        var result = c.Get(protection, block.Identity);
        if (!result.IsSuccess)
        {
            foreach (var call in c.Snapshot.Blocks.SelectMany(b => b.Statements).OfType<Call>()
                .Where(call => c.Get(calls, call.Identity) is { IsSuccess: true, Value.Operation.Name: "StackProtectionFailure" }))
                records.Add(new("stack-protection-retained", call.Trace?.NativeAddress, result.Why!.Message, false) { Reason = result.Why });
            return false;
        }
        if (result.Value is not { } proof) return false;
        edit.Blocks[block.Identity] = block with { End = new Jump(proof.Pass) };
        var used = SnapshotRewrite.Dependencies([((Branch)block.End).Condition, proof.Save.Value]);
        var candidates = new HashSet<MemoryRead>();
        foreach (var read in c.Snapshot.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>())
        {
            var resolved = c.Get(state.Resolve, read.Address);
            var location = resolved.IsSuccess ? c.Get(state.Locations, new(resolved.Value, read.Width)) : default;
            if (used.Contains(read.Result) && location.IsSuccess && (location.Value == proof.Source || location.Value == proof.Copy)) candidates.Add(read);
        }
        var escaped = c.Get(state.Escapes, 0);
        bool privateCopy = escaped.IsSuccess && !escaped.Value.MayReach(proof.Copy);
        foreach (var read in c.Snapshot.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>().Except(candidates)
            .Where(read => !edit.RemovedStatements.Contains(read)))
        {
            var address = c.Get(state.Resolve, read.Address);
            var location = address.IsSuccess ? c.Get(state.Locations, new(address.Value, read.Width)) : default;
            if (!location.IsSuccess || c.Get(state.Alias, new(proof.Copy, location.Value)) is not { IsSuccess: true, Value.Kind: AliasKind.Disjoint }) privateCopy = false;
        }
        if (privateCopy) edit.RemovedStatements.Add(proof.Save);
        bool changed;
        do
        {
            changed = false;
            var live = SnapshotRewrite.Dependencies(edit.Blocks.Values.SelectMany(b => b.Statements.Where(s => !edit.RemovedStatements.Contains(s))
                .SelectMany(SnapshotRewrite.Uses).Concat(EndUses(b.End)).Concat(b.Merges.SelectMany(m => m.Inputs.Select(i => i.Value)))));
            foreach (var read in candidates.Where(r => !edit.RemovedStatements.Contains(r) && !live.Contains(r.Result)))
            { edit.RemovedStatements.Add(read); changed = true; }
        } while (changed);
        records.Add(new("stack-protection", block.Trace?.NativeAddress, "帧保护副本与同一保护源比较，失败前沿只有不返回的保护失败", true));
        return true;
    }
}
