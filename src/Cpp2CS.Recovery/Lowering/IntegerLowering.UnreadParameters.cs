using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Checks;
using Cpp2CS.Recovery.Dispatch;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    private UnreadReceiverQuery? unreadReceivers;
    private readonly Dictionary<BlockIdentity, BlockIdentity> unreadNullBranches = [];
    private readonly HashSet<CallIdentity> unreadNullCalls = [];
    private readonly Dictionary<ManagedStatement, CallIdentity> explicitNullStatements = new(ReferenceEqualityComparer.Instance);
    private readonly HashSet<CallIdentity> unreadCheckedCalls = [];

    private static bool UnreadArgumentFailure(Reason reason) =>
        reason.Code == "lowering.Binding" && reason.Message.StartsWith("使用了调用结果绑定之外的位", StringComparison.Ordinal)
        || reason.Code == "lowering.UnsupportedType" && (reason.Message is
            "值的托管类型与使用位置不兼容：Reference → Reference，LocalValue" or
            "值的托管类型与使用位置不兼容：Reference → Reference，ArgumentValue" or
            "值的托管类型与使用位置不兼容：Int → Reference，LocalValue")
        || reason.Cause is { } cause && UnreadArgumentFailure(cause);
    private static Reason UnreadCause(Reason original, Reason cause) => original with
        { Cause = original.Cause is null ? cause : UnreadCause(original.Cause, cause) };

    /// <summary>只有原槽下降失败才消费事实；失败保留原洞，并追加被调方的使用或证明原因。</summary>
    private ManagedValue? UnreadCallArgument(Call call, CallDefinition definition, int index, TypeRef type, Point point, int pendingStart)
    {
        var original = failure;
        if (original is null || !UnreadArgumentFailure(original.Reason) || parameterReads is null || calls is null
            || call.Target is not ImageFunction entry || definition.Virtual || definition.Method.Method.Owner.IsInterface || definition.Registration is not null
            || DispatchQuery.IsDelegateType(definition.Method.DeclaringType)) return null;
        var named = context.Get(calls, call.Identity);
        if (!named.IsSuccess || named.Value.Kind != CallKind.Managed || named.Value.Candidates?.Candidates is not [{ Entry.Method: { } target }]
            || target.Method != definition.Method.Method) return null;
        ManagedValue? No(Reason why)
        { failure = original with { Reason = UnreadCause(original.Reason, why) }; return null; }
        var summary = parameterReads.Get(entry.EntryOffset, definition.Method);
        if (!summary.IsSuccess) return No(summary.Why!);
        var usage = index == -1 ? summary.Value.This : summary.Value.Parameters.ElementAtOrDefault(index);
        if (usage is null) return No(new("binding.parameter-reads.binding", "摘要没有这个形参的入口绑定。"));
        if (usage.IsRead) return No(usage.Reason ?? new("binding.parameter-reads.read", "形参被读。"));
        if (type is ByRefRef) return No(new("lowering.UnreadArgument.ByRef", "按引用形参或值类型接收者没有默认写法。"));
        if (!DiscardUnreadArgumentMerges(pendingStart))
            return No(new("lowering.UnreadArgument.Temporaries", "失败的实参下降已把临时合流用于读取物化，不能只丢弃该实参。"));
        if (index != -1)
        {
            failure = null;
            return types.Kind(type) == TypeKind.Struct || Opaque(type) ? new ComposedValue(type, [])
                : new ConstantValue(0, type, types.ValueWidth(type));
        }
        if (definition.Method.Method is { IsOverridable: true } or { Name: ".ctor" })
            return No(new("lowering.UnreadReceiver.Target", "该实例目标不能用同目标的 callvirt 吸收判空。"));
        if (locations is not null)
        {
            runtimeChecks ??= new(state, calls, locations, dispatch is null ? null : new CheckedDispatchReceiver(dispatch));
            var replacement = context.Get(unreadReceivers ??= new(runtimeChecks, types), call.Identity);
            if (!replacement.IsSuccess) return No(replacement.Why!);
            if (replacement.Value is { } checkedReceiver)
            {
                failure = null;
                var receiver = ReferenceAt(checkedReceiver.Value, type, point);
                if (receiver is null || failure is not null)
                    return No(new("lowering.UnreadReceiver.Value", "判空对象没有可下降的托管写法。", failure?.Reason));
                if (checkedReceiver.Branch is { } branch) unreadNullBranches[branch.Source] = branch.Target;
                if (checkedReceiver.Check is { } check) unreadNullCalls.Add(check);
                unreadCheckedCalls.Add(call.Identity);
                return receiver;
            }
        }
        if (!method.Method.IsStatic && !method.Method.Owner.IsValueType && types.IsAssignable(method.DeclaringType, type))
        {
            failure = null;
            return new ArgumentValue(-1, method.DeclaringType, types.PointerSize * 8);
        }
        return No(new("lowering.UnreadReceiver.Source", "未读接收者没有无间隔事件的显式判空对象，也没有可赋值的调用方 this。"));
    }

    /// <summary>失败尝试建立的纯合流不属于替代后的实参；读取物化仍引用它们时保留原洞。</summary>
    private bool DiscardUnreadArgumentMerges(int start)
    {
        if (pending.Count == start) return true;
        var locals = pending.Skip(start).Select(merge => merge.Local.Id).ToHashSet();
        bool Uses(ManagedValue? value) => value is not null && ManagedValues.Walk(value)
            .Any(value => value is LocalValue local && locals.Contains(local.Id));
        if (readDefinitions.Values.Concat(structReads.Values.SelectMany(reads => reads)).Any(read => Uses(read.Value))) return false;
        foreach (var key in values.Where(pair => Uses(pair.Value)).Select(pair => pair.Key).ToArray()) values.Remove(key);
        foreach (var key in merges.Where(pair => locals.Contains(pair.Value.Id)).Select(pair => pair.Key).ToArray()) merges.Remove(key);
        pending.RemoveRange(start, pending.Count - start);
        return true;
    }

    private ManagedBody AbsorbUnreadNullChecks(ManagedBody body) => body with
    {
        Blocks = body.Blocks.Select(block => block with
        {
            Statements = block.Statements.Where(statement => !explicitNullStatements.TryGetValue(statement, out var check)
                || !unreadNullCalls.Contains(check)).Select(statement =>
            {
                if (statement is not ManagedBranch branch) return statement;
                var source = labels.FirstOrDefault(pair => pair.Value == block.Address).Key;
                if (source is null || !unreadNullBranches.TryGetValue(source, out var target)) return statement;
                var edge = branch.Taken.Target == labels[target] ? branch.Taken : branch.Fallthrough;
                return (ManagedStatement)new ManagedJump(branch.Address, edge);
            }).ToArray(),
        }).ToArray(),
    };
}
