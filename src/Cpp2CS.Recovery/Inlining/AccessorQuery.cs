using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Inlining;

public enum AccessorNoneReason { NoCandidates, Incomplete, NotTemplate, Generic }
public sealed record AccessorAccess(MethodRef Caller, ulong Position, FieldRef Field, TypeRef? Receiver,
    AccessorKind Kind, bool HasPlacement);
public sealed record AccessorAnswer(MethodRef? Method, Reason? Failure, AccessorNoneReason? NoneReason = null, int Matches = 0);
public sealed record AccessorAttempt(AccessorAccess Access, AccessorAnswer Answer);

/// <summary>元数据筛候选，候选自己的恢复体证明模板；不依赖名称、属性登记或枚举次序。</summary>
public sealed class AccessorQuery(ManagedTypes types, IAccessorTemplateSource templates, Action<AccessorAttempt>? observe = null)
{
    public AccessorReadPlacementQuery ReadPlacement { get; } = new();
    public AccessorAnswer Resolve(AccessorAccess access)
    {
        var answer = Find(access);
        observe?.Invoke(new(access, answer));
        return answer;
    }

    private AccessorAnswer Find(AccessorAccess access)
    {
        AccessorAnswer None(AccessorNoneReason reason) => new(null, new("inline.Accessor.None", reason switch
        {
            AccessorNoneReason.NoCandidates => "没有候选",
            AccessorNoneReason.Incomplete => "候选未能完整恢复",
            AccessorNoneReason.NotTemplate => "候选的方法体不是模板",
            _ => "声明类型或方法是泛型",
        }), reason);
        var field = access.Field.Field;
        if (field.Owner.GenericParameters.Count != 0) return None(AccessorNoneReason.Generic);
        var candidates = field.Owner.Methods.Where(m => !m.IsVirtual && m.IsStatic == field.IsStatic
            && (access.Kind == AccessorKind.Getter
                ? m.Parameters.Count == 0 && m.ReturnType.Equals(field.Type)
                : m.Parameters is [var p] && p.Type.Equals(field.Type) && ManagedTypes.IsVoid(m.ReturnType)))
            .Where(m => ManagedAccess.Method(types, access.Caller.Method.Owner, MethodRef.Open(m), access.Receiver)).ToArray();
        var reason = candidates.Any(m => m.GenericParameters.Count != 0) ? AccessorNoneReason.Generic : AccessorNoneReason.NoCandidates;
        var matches = new List<MethodDef>();
        foreach (var candidate in candidates.Where(m => m.GenericParameters.Count == 0))
        {
            var result = templates.Get(candidate);
            if (result.Template is { } template && result.Status == AccessorTemplateStatus.Complete
                && template.Kind == access.Kind && template.Field.Equals(access.Field)) matches.Add(candidate);
            else if (result.Status == AccessorTemplateStatus.Incomplete)
            {
                if (reason != AccessorNoneReason.NotTemplate) reason = AccessorNoneReason.Incomplete;
            }
            else reason = AccessorNoneReason.NotTemplate;
        }
        if (matches.Count == 0) return None(reason);
        if (matches.Count > 1) return new(null, new("inline.Accessor.Ambiguous", $"有 {matches.Count} 个访问器模板相同，无法区分原调用"), Matches: matches.Count);
        if (!access.HasPlacement) return new(null, new("inline.Accessor.Placement", "调用无法放在这次完整字段访问的原位置"), Matches: 1);
        return new(MethodRef.Open(matches[0]), null, Matches: 1);
    }
}
