using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.RuntimeFunctions;

namespace Cpp2CS.Recovery.Structure;

public sealed partial class UnobservableEffects
{
    private Reason? FoldInternalCallCache(QueryContext original, SnapshotRewrite edit, MemoryRead guard, Location cache,
        InitializationGroup group, InternalCallForwarder? known, MethodRef method)
    {
        Reason No(string code, string message, Reason? cause = null) => new("structure.init-guard.icall-" + code, message, cause);
        var writes = group.Statements.OfType<MemoryWrite>().ToArray();
        if (writes.Length != 1 || group.WrittenResult is not { } initialized) return No("write", "缓存没有唯一的解析结果写回。");
        var uses = new SemanticUses(original, calls, state, names.Binder, names.Entry);
        foreach (var write in original.Snapshot.Blocks.SelectMany(b => b.Statements).OfType<MemoryWrite>().Where(w => w.Identity != writes[0].Identity))
        {
            var address = original.Get(state.Resolve, write.Address);
            var location = address.IsSuccess ? original.Get(state.Locations, new(address.Value, write.Width)) : default;
            if (!location.IsSuccess || original.Get(state.Alias, new(cache, location.Value)) is not { IsSuccess: true, Value.Kind: AliasKind.Disjoint })
                return No("other-write", "本函数的其他写入没有与缓存不相交的凭据。", location.Why);
        }
        if (uses.Roots.Where(u => !u.Address).Any(u => uses.ImageAddresses(u.Value, original, state).Contains((ulong)cache.Offset!.Value)))
            return No("escape", "缓存地址另有非内存用途。");
        var kept = edit.Apply(); var c = names.CreateContext(kept);
        var targets = kept.Blocks.SelectMany(b => b.Statements).OfType<Call>().Where(call => call.Target is ComputedTarget target
            && c.Get(state.Resolve, target.Value) is { IsSuccess: true } value && value.Value == initialized).ToArray();
        if (targets.Length == 0) return No("target", "没有使用初始化后缓存内容的间接调用。");
        var cacheReads = kept.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>().Where(read =>
        {
            var address = c.Get(state.Resolve, read.Address);
            return address.IsSuccess && c.Get(state.Locations, new(address.Value, read.Width)) is { IsSuccess: true } location && location.Value == cache;
        }).ToArray();
        if (known is null)
        {
            if (targets.Length != 1) return No("wrapper", "包装不是一次缓存调用。");
            var privateStatements = kept.Blocks.SelectMany(b => b.Statements).Where(s => group.Statements.Any(g =>
                g is Call a && s is Call b && a.Identity == b.Identity || g is MemoryWrite w && s is MemoryWrite v && w.Identity == v.Identity)
                || cacheReads.Contains(s)).ToHashSet();
            var proof = InternalCallWrappers.Forwarder(method, kept, names.Binder, state, targets[0], privateStatements);
            if (!proof.IsSuccess) return No("wrapper", "缓存包装的纯转发凭据不足。", proof.Why);
            DiscoveredCaches.Add(((ulong)cache.Offset!.Value, proof.Value with { WrapperEntry = wrapperEntry }));
            return null;
        }
        var replacement = new SnapshotRewrite(kept);
        foreach (var block in kept.Blocks)
        {
            var statements = block.Statements.ToBuilder();
            for (int i = 0; i < statements.Count; i++)
                if (statements[i] is Call call && targets.Any(t => t.Identity == call.Identity))
                {
                    var rewritten = known.Rewrite(names.Binder, call, kept.Terms);
                    if (rewritten is null) return No("binding", "缓存调用的实参与包装入口不能完整重绑定。");
                    statements[i] = rewritten;
                }
            replacement.Blocks[block.Identity] = block with { Statements = statements.ToImmutable() };
        }
        foreach (var statement in group.Statements)
        foreach (var current in kept.Blocks.SelectMany(b => b.Statements).Where(s =>
            statement is Call a && s is Call b && a.Identity == b.Identity || statement is MemoryWrite w && s is MemoryWrite v && w.Identity == v.Identity))
            replacement.RemovedStatements.Add(current);
        var live = SnapshotRewrite.Dependencies(replacement.Blocks.Values.SelectMany(b => b.Statements.Where(s => !replacement.RemovedStatements.Contains(s))
            .SelectMany(SnapshotRewrite.Uses).Concat(EndUses(b.End)).Concat(b.Merges.SelectMany(m => m.Inputs.Select(i => i.Value)))));
        // 目标已改成托管调用，解析结果不得另有可观察用途。
        if (live.Contains(initialized)) return No("result-used", "解析结果除缓存和已命名的调用目标外仍有使用。");
        foreach (var read in cacheReads)
            if (!live.Contains(read.Result)) replacement.RemovedStatements.Add(read);
        var rewrittenFunction = replacement.Apply();
        foreach (var block in rewrittenFunction.Blocks) edit.Blocks[block.Identity] = block;
        foreach (var block in kept.Blocks.Where(b => rewrittenFunction.Blocks.All(x => x.Identity != b.Identity))) edit.RemovedBlocks.Add(block.Identity);
        VerifiedInternalCallCaches.Add(((ulong)cache.Offset!.Value, guard.Identity, writes[0].Identity));
        foldedInternalCall = true;
        return null;
    }
}
