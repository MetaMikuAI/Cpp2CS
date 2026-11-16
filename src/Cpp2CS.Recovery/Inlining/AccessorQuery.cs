using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Inlining;

public enum AccessorNoneReason { NoCandidates, Incomplete, NotTemplate, GenericMethod, FieldInstance }
public sealed record AccessorAccess(MethodRef Caller, ulong Position, FieldRef Field, TypeRef? Receiver,
    AccessorKind Kind, bool HasPlacement, Reason? PlacementFailure = null)
{
    /// <summary>结构体值上的单字段纯读取；声明类型实例由接收者给出。</summary>
    public bool ValueRead { get; init; }
}
public sealed record AccessorCandidateFailure(MethodDef Method, Reason? Failure);
public sealed record AccessorAnswer(MethodRef? Method, Reason? Failure, AccessorNoneReason? NoneReason = null, int Matches = 0)
{
    public IReadOnlyList<AccessorCandidateFailure> IncompleteCandidates { get; init; } = [];
    public Reason? Witness { get; init; }
}
public sealed record AccessorAttempt(AccessorAccess Access, AccessorAnswer Answer);

/// <summary>元数据筛候选，候选自己的恢复体证明模板；泛型值类型保留封闭见证，不依赖名称或枚举次序。</summary>
public sealed partial class AccessorQuery(ManagedTypes types, IAccessorTemplateSource templates, Action<AccessorAttempt>? observe = null)
{
    public AccessorReadPlacementQuery ReadPlacement { get; } = new();
    public AccessorAnswer Resolve(AccessorAccess access)
    {
        var answer = Find(access);
        if (answer.Failure is { } failure) answer = answer with { Failure = WithAnchor(failure, access) };
        observe?.Invoke(new(access, answer));
        return answer;
    }

    public AccessorAnswer Reject(AccessorAccess access, Reason failure)
    {
        failure = WithAnchor(failure, access);
        var answer = new AccessorAnswer(null, failure, failure.Code == "inline.Accessor.None"
            ? failure.Message == "没有候选" ? AccessorNoneReason.NoCandidates
                : failure.Message == "候选未能完整恢复" ? AccessorNoneReason.Incomplete : AccessorNoneReason.NotTemplate : null);
        observe?.Invoke(new(access, answer));
        return answer;
    }

    private AccessorAnswer Find(AccessorAccess access)
    {
        var incomplete = new List<AccessorCandidateFailure>();
        Reason? inference = null;
        var witnesses = new Dictionary<MethodRef, Reason>();
        // 方法体里读写了这个字段、却不是单字段模板的第一个候选；只用于诊断。
        Reason? rejected = null;
        AccessorAnswer None(AccessorNoneReason reason) => new(null, new("inline.Accessor.None", reason switch
        {
            AccessorNoneReason.NoCandidates => "没有候选",
            AccessorNoneReason.Incomplete => "候选未能完整恢复",
            AccessorNoneReason.NotTemplate => "候选的方法体不是模板",
            AccessorNoneReason.GenericMethod => inference is null ? "签名候选只有泛型方法，尚不支持" : "字段所属类型未能唯一确定泛型实参",
            _ => "字段没有完整的声明类型实例",
        }, inference ?? (reason == AccessorNoneReason.Incomplete ? Anchor(access.Kind == AccessorKind.Setter, access.Field, CandidateCause(incomplete))
            : reason == AccessorNoneReason.NotTemplate && rejected is not null ? Anchor(access.Kind == AccessorKind.Setter, access.Field, rejected) : null)),
            reason) { IncompleteCandidates = incomplete };
        var field = access.Field.Field;
        if (access.Field.DeclaringType is not DefinitionRef instance || instance.Definition != field.Owner
            || instance.Arguments.Count != field.Owner.GenericParameters.Count) return None(AccessorNoneReason.FieldInstance);
        var receiver = access.Receiver is ByRefRef address ? address.Element : access.Receiver;
        bool valueRead = access.ValueRead && access.Kind == AccessorKind.Getter && !field.IsStatic
            && field.Owner.IsValueType && instance.Equals(receiver);
        if (access.ValueRead && !valueRead) return None(AccessorNoneReason.FieldInstance);
        MethodRef OnInstance(MethodDef method) => new(method, instance.Arguments, []);
        // 不可重写的虚方法（值类型或密封类上的接口实现）目标唯一，与非虚方法一样能被内联，也一样能写回成调用。
        var candidates = field.Owner.Methods.Where(m => !m.IsOverridable && m.IsStatic == field.IsStatic
            && (access.Kind == AccessorKind.Getter
                ? m.Parameters.Count == 0 && m.ReturnType.Equals(field.Type)
                : m.Parameters is [var p] && p.Type.Equals(field.Type) && ManagedTypes.IsVoid(m.ReturnType)))
            .Where(m => ManagedAccess.Method(types, access.Caller.Method.Owner, OnInstance(m), access.Receiver)).ToArray();
        var reason = candidates.Any(m => m.GenericParameters.Count != 0) ? AccessorNoneReason.GenericMethod : AccessorNoneReason.NoCandidates;
        var matches = access.Kind == AccessorKind.Getter && field.IsStatic
            ? StaticCandidates(access.Field, out inference).Where(m => ManagedAccess.Method(types, access.Caller.Method.Owner, m, null)).ToList()
            : new List<MethodRef>();
        foreach (var candidate in candidates.Where(m => m.GenericParameters.Count == 0))
        {
            bool closed = AccessorTemplates.UsesClosedWitness(candidate);
            var result = closed ? templates.Get(OnInstance(candidate)) : templates.Get(candidate);
            // 封闭见证只核对字段定义；现场的声明类型实例仍由定位给出。
            var openField = new FieldRef(field, MethodRef.Open(candidate).DeclaringType);
            if (result.Template is { } template && result.Status == AccessorTemplateStatus.Complete
                && template.SingleField && template.Kind == access.Kind && (closed ? template.Field.Field == field : template.Field.Equals(openField)))
            {
                var selected = OnInstance(candidate);
                if (!matches.Contains(selected)) matches.Add(selected);
                if (result.Witness is { } witness) witnesses[selected] = witness;
            }
            else if (result.Status == AccessorTemplateStatus.Incomplete)
            {
                incomplete.Add(new(candidate, result.Failure));
                if (reason != AccessorNoneReason.NotTemplate) reason = AccessorNoneReason.Incomplete;
            }
            else
            {
                reason = AccessorNoneReason.NotTemplate;
                if (rejected is null && (closed || result.Evidence?.Fields.Contains(field) == true))
                    rejected = new("inline.candidate", "候选 " + candidate.Owner.FullName + "." + candidate.Name,
                        result.Failure ?? new("inline.Accessor.None", "候选的模板不是这个字段的单字段读写", result.Witness));
            }
        }
        if (matches.Count == 0) return None(reason);
        if (matches.Count > 1) return new(null, new("inline.Accessor.Ambiguous", $"有 {matches.Count} 个访问器模板相同，无法区分原调用", witnesses.Values.FirstOrDefault()), Matches: matches.Count)
            { IncompleteCandidates = incomplete };
        if (!access.HasPlacement && !valueRead) return new(null, new("inline.Accessor.Placement", "调用无法放在这次完整字段访问的原位置",
                witnesses.GetValueOrDefault(matches[0]) is { } evidence ? evidence with { Cause = access.PlacementFailure } : access.PlacementFailure), Matches: 1)
            { IncompleteCandidates = incomplete };
        return new(matches[0], null, Matches: 1) { IncompleteCandidates = incomplete, Witness = witnesses.GetValueOrDefault(matches[0]) };
    }
}
