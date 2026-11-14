using System.Collections.Immutable;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Structure;

public sealed partial class UnobservableEffects
{
    private NativeFunction FoldInitializationGuards(NativeFunction input, List<StructureRecord> records, QueryContext context, out HashSet<BlockIdentity> retainedGuards, out QueryContext finalContext, ref bool assumed)
    {
        var rejected = new Dictionary<ReadIdentity, StructureRecord>();
        var rejectedHeads = new Dictionary<ReadIdentity, BlockIdentity>();
        while (true)
        {
            var tests = input.Blocks.Where(b => b.End is Branch).Select(b => (Head: b, Test: InitializationTest.Of(((Branch)b.End).Condition)))
                .Where(x => x.Test is not null).ToArray();
            if (tests.Length == 0) break;
            var c = context = ReferenceEquals(context.Snapshot, input) ? context : names.CreateContext(input);
            var reads = input.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>().ToDictionary(r => r.Identity);
            SemanticUses? uses = null;
            var prefix = new InitializationPrefixQuery(state, calls, names, image);
            bool changed = false;
            var batch = new SnapshotRewrite(input);
            var occupied = new HashSet<BlockIdentity>();
            var owners = input.Blocks.SelectMany(b => b.Statements.Select(statement => (statement, b.Identity))).ToDictionary(x => x.statement, x => x.Identity);
            var originalBlocks = input.Blocks.ToDictionary(b => b.Identity);
            foreach (var (head, test) in tests)
            {
                if (occupied.Contains(head.Identity)) continue;
                var branch = (Branch)head.End;
                if (test is null || !reads.TryGetValue(test.Read, out var read)) continue;
                var address = c.Get(state.Resolve, read.Address);
                var location = address.IsSuccess ? c.Get(state.Locations, new(address.Value, read.Width)) : default;
                if (!location.IsSuccess) continue;
                bool methodFlag = read.Width == 8 && location.Value is { Region: Region.Image, Offset: { } offset } && offset >= 0 && offset <= ulong.MaxValue && names.Flags.ContainsKey((ulong)offset);
                if (!methodFlag && (location.Value.Region != Region.Other || !InitializationStateWidths.Contains(read.Width))) continue;
                FieldName? field = null;
                if (!methodFlag)
                {
                    var storage = input.Terms.Atom(new MemoryAtom(location.Value, null), read.Width);
                    var named = c.Get(names, input.Terms.Slice(storage, test.Low, test.Width));
                    field = named.IsSuccess && named.Value.Name is FieldName value ? value : null;
                    if (field is null && read.Width == input.AddressWidth && (test.Low != 0 || test.Width != read.Width)
                        && c.Get(names, storage) is { IsSuccess: true, Value.Name: FieldName { Record: "MethodInfo" } whole }) field = whole;
                }
                bool stateField = field is not null && InitializationStateFields.Contains(field.Field);
                bool classFlag = stateField && field!.Record == "Il2CppClass";
                bool methodContext = stateField && field!.Record == "MethodInfo";
                if (!stateField && !methodFlag) continue;
                void Reject(Reason why)
                {
                    rejected[read.Identity] = new("init-guard", read.Trace?.NativeAddress, why.Message, false) { Reason = why };
                    rejectedHeads[read.Identity] = head.Identity;
                }
                // 类型含本定义的类型参数时，类来自泛型上下文；封闭的类实体照常改写。
                if (classFlag && field!.Owner is EntityName { Entity: ClassEntity { Type: var guarded } } && guarded.ContainsGenericParameter()
                    || classFlag && field!.Owner is ParameterName { MethodInformation: true })
                { Reject(new("structure.init-guard.generic-context", "类来自当前泛型上下文，本变换不处理该来源。")); continue; }
                if (classFlag && field!.Owner is not EntityName { Entity: ClassEntity })
                { Reject(new("structure.init-guard.class-unnamed", "初始化状态的类没有实体凭据或来自泛型上下文。")); continue; }
                if (methodContext && (field!.Owner is not (EntityName { Entity: MethodEntity } or ParameterName { MethodInformation: true })
                    || !names.ContextEntity(field.Owner)))
                { Reject(new("structure.init-guard.method-unnamed", "初始化状态的方法没有已命名的实体或当前定义的泛型上下文凭据。")); continue; }
                if (methodContext && (test.Low != 0 || test.Width != read.Width))
                { Reject(new("structure.init-guard.test-width", "泛型上下文指针没有按完整宽度测试零或非零。")); continue; }
                var flag = methodFlag ? names.Flags.GetValueOrDefault((ulong)location.Value.Offset!.Value) : null;
                Reason? flagFailure = methodFlag && flag?.IsFlag != true ? new("structure.init-guard.flag-evidence", "本函数未证明该字节是方法元数据初始化标志。",
                    Chain(flag?.Reasons ?? [new("naming.no-access-evidence", "本函数没有该字节的访问凭据。")])) : null;
                uses ??= new(c, calls, state, names.Binder, names.Entry);
                if (uses.Of(read.Identity).Any(use => !use.Condition || use.Point != new Point(head.Identity, head.Statements.Length)))
                { Reject(new("structure.init-guard.read-used", "标志读取除本次分支测试外还有真实使用。", flagFailure)); continue; }
                var eventId = test.ZeroWhenTrue ? branch.True : branch.False;
                var group = c.Get(prefix, new(new(head.Identity, eventId), stateField ? field : null,
                    methodFlag ? location.Value : null, test.Low, test.Width));
                if (!group.IsSuccess) { Reject(Append(group.Why!, flagFailure)); continue; }
                if (flagFailure is not null) { Reject(flagFailure); continue; }
                var moved = group.Value.Statements;
                var region = moved.Select(statement => owners[statement]).Append(head.Identity).Append(group.Value.After.Block)
                    .Concat(moved.OfType<Call>().Where(call => call.Unwind is not null).Select(call => call.Unwind!)).ToHashSet();
                if (region.Overlaps(occupied)) continue;
                var edit = new SnapshotRewrite(input);
                var tail = edit.Blocks[group.Value.After.Block];
                bool unwindValid = true;
                foreach (var call in moved.OfType<Call>().Where(call => call.Unwind is not null))
                {
                    var source = input.Blocks.Single(b => b.Statements.OfType<Call>().Any(x => x.Identity == call.Identity));
                    var handler = edit.Blocks[call.Unwind!];
                    var merges = ImmutableArray.CreateBuilder<Merge>();
                    foreach (var merge in handler.Merges)
                    {
                        var incoming = merge.Inputs.Single(i => i.Predecessor == source.Identity);
                        var existing = merge.Inputs.FirstOrDefault(i => i.Predecessor == head.Identity);
                        if (existing is not null && existing.Value != incoming.Value) { unwindValid = false; break; }
                        merges.Add(existing is null ? merge with { Inputs = merge.Inputs.Add(new(head.Identity, incoming.Value)) } : merge);
                    }
                    if (!unwindValid) break;
                    edit.Blocks[handler.Identity] = handler with { Merges = merges.ToImmutable() };
                }
                if (!unwindValid)
                { Reject(new("structure.init-guard.unwind-merge", "移动调用的展开边与入口处已有的异常合流值不一致。")); continue; }
                RefineGuardResults(c, edit, moved.OfType<Call>(), ref assumed);
                edit.Blocks[tail.Identity] = tail with { Statements = tail.Statements.Skip(group.Value.After.Before).ToImmutableArray() };
                edit.Blocks[head.Identity] = head with { Statements = head.Statements.AddRange(moved), End = new Jump(tail.Identity) };
                // 单入口前缀的中间块失去入口，由共同图改写删除；续点保留原来的定义与入边身份。
                if (edit.Replacements.Any(p => batch.Replacements.TryGetValue(p.Key, out var previous) && previous != p.Value)) continue;
                foreach (var (id, block) in edit.Blocks)
                    if (!ReferenceEquals(block, originalBlocks[id])) batch.Blocks[id] = block;
                foreach (var (from, to) in edit.Replacements) batch.Replacements[from] = to;
                occupied.UnionWith(region);
                rejected.Remove(read.Identity);
                records.Add(new("init-guard", read.Trace?.NativeAddress, (classFlag ? "类初始化" : methodContext ? "方法泛型上下文初始化" : "方法元数据初始化") + "模板守卫归位；" + group.Value.Evidence, true));
                changed = true;
            }
            if (!changed) break;
            input = batch.Apply();
        }
        var remaining = input.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>().Select(r => r.Identity).ToHashSet();
        records.AddRange(rejected.Where(p => remaining.Contains(p.Key)).Select(p => p.Value));
        retainedGuards = rejected.Where(p => remaining.Contains(p.Key) && p.Value.Reason?.Code != "structure.init-guard.generic-context")
            .Select(p => rejectedHeads[p.Key]).ToHashSet();
        finalContext = ReferenceEquals(context.Snapshot, input) ? context : names.CreateContext(input);
        return input;
    }

    private static readonly HashSet<string> InitializationStateFields = Cpp2CS.Runtime.RuntimeOperations.All.Values
        .SelectMany(InitializationPrefixQuery.Representations)
        .Select(r => r.Record + "." + r.Field).ToHashSet();

    private HashSet<int> InitializationStateWidths { get; } = InitializationStateFields.Select(path => path.Split('.'))
        .Select(path => checked((int)names.Spec.Layout.Field(path[0], path[1]).Size * 8)).ToHashSet();

    private static Reason? Chain(IEnumerable<Reason> reasons)
    {
        Reason? result = null;
        foreach (var reason in reasons.Reverse()) result = Append(reason, result);
        return result;
    }
    private static Reason Append(Reason reason, Reason? tail) => reason with { Cause = reason.Cause is null ? tail : Append(reason.Cause, tail) };
}
