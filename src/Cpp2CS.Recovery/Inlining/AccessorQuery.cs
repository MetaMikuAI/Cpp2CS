using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Inlining;

public enum AccessorNoneReason { NoCandidates, Incomplete, NotTemplate, GenericMethod, FieldInstance }
public sealed record AccessorAccess(MethodRef Caller, ulong Position, FieldRef Field, TypeRef? Receiver,
    AccessorKind Kind, bool HasPlacement, Reason? PlacementFailure = null);
public sealed record AccessorCandidateFailure(MethodDef Method, Reason? Failure);
public sealed record AccessorAnswer(MethodRef? Method, Reason? Failure, AccessorNoneReason? NoneReason = null, int Matches = 0)
{
    public IReadOnlyList<AccessorCandidateFailure> IncompleteCandidates { get; init; } = [];
}
public sealed record AccessorAttempt(AccessorAccess Access, AccessorAnswer Answer);

/// <summary>元数据筛候选，候选自己的开放恢复体证明模板；不依赖名称、属性登记或枚举次序。</summary>
public sealed partial class AccessorQuery(ManagedTypes types, IAccessorTemplateSource templates, Action<AccessorAttempt>? observe = null)
{
    public AccessorReadPlacementQuery ReadPlacement { get; } = new();
    public AccessorAnswer Resolve(AccessorAccess access)
    {
        var answer = Find(access);
        observe?.Invoke(new(access, answer));
        return answer;
    }

    public AccessorAnswer Reject(AccessorAccess access, Reason failure)
    {
        var answer = new AccessorAnswer(null, failure, failure.Code == "inline.Accessor.None"
            ? failure.Message == "没有候选" ? AccessorNoneReason.NoCandidates
                : failure.Message == "候选未能完整恢复" ? AccessorNoneReason.Incomplete : AccessorNoneReason.NotTemplate : null);
        observe?.Invoke(new(access, answer));
        return answer;
    }

    private AccessorAnswer Find(AccessorAccess access)
    {
        var incomplete = new List<AccessorCandidateFailure>();
        AccessorAnswer None(AccessorNoneReason reason) => new(null, new("inline.Accessor.None", reason switch
        {
            AccessorNoneReason.NoCandidates => "没有候选",
            AccessorNoneReason.Incomplete => "候选未能完整恢复",
            AccessorNoneReason.NotTemplate => "候选的方法体不是模板",
            AccessorNoneReason.GenericMethod => "签名候选只有泛型方法，尚不支持",
            _ => "字段没有完整的声明类型实例",
        }), reason) { IncompleteCandidates = incomplete };
        var field = access.Field.Field;
        if (access.Field.DeclaringType is not DefinitionRef instance || instance.Definition != field.Owner
            || instance.Arguments.Count != field.Owner.GenericParameters.Count) return None(AccessorNoneReason.FieldInstance);
        MethodRef OnInstance(MethodDef method) => new(method, instance.Arguments, []);
        var candidates = field.Owner.Methods.Where(m => !m.IsVirtual && m.IsStatic == field.IsStatic
            && (access.Kind == AccessorKind.Getter
                ? m.Parameters.Count == 0 && m.ReturnType.Equals(field.Type)
                : m.Parameters is [var p] && p.Type.Equals(field.Type) && ManagedTypes.IsVoid(m.ReturnType)))
            .Where(m => ManagedAccess.Method(types, access.Caller.Method.Owner, OnInstance(m), access.Receiver)).ToArray();
        var reason = candidates.Any(m => m.GenericParameters.Count != 0) ? AccessorNoneReason.GenericMethod : AccessorNoneReason.NoCandidates;
        var matches = new List<MethodDef>();
        foreach (var candidate in candidates.Where(m => m.GenericParameters.Count == 0))
        {
            var result = templates.Get(candidate);
            // 定位已给出字段所属实例；模板核对开放字段身份，不比较实例间的布局偏移。
            var openField = new FieldRef(field, MethodRef.Open(candidate).DeclaringType);
            if (result.Template is { } template && result.Status == AccessorTemplateStatus.Complete
                && template.SingleField && template.Kind == access.Kind && template.Field.Equals(openField)) matches.Add(candidate);
            else if (result.Status == AccessorTemplateStatus.Incomplete)
            {
                incomplete.Add(new(candidate, result.Failure));
                if (reason != AccessorNoneReason.NotTemplate) reason = AccessorNoneReason.Incomplete;
            }
            else reason = AccessorNoneReason.NotTemplate;
        }
        if (matches.Count == 0) return None(reason);
        if (matches.Count > 1) return new(null, new("inline.Accessor.Ambiguous", $"有 {matches.Count} 个访问器模板相同，无法区分原调用"), Matches: matches.Count)
            { IncompleteCandidates = incomplete };
        if (!access.HasPlacement) return new(null, new("inline.Accessor.Placement", "调用无法放在这次完整字段访问的原位置", access.PlacementFailure), Matches: 1)
            { IncompleteCandidates = incomplete };
        return new(OnInstance(matches[0]), null, Matches: 1) { IncompleteCandidates = incomplete };
    }
}
