using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Binding;

/// <summary>直接调用的多身份候选按已有静态引用类型筛选；没有类型凭据的候选仍然保留。</summary>
public sealed class DirectCallQuery(CallNamingQuery calls, ValueNamingQuery? names, BoundSourceQuery sources, ManagedTypes types)
    : Query<CallIdentity, CandidateBinding>
{
    public override Outcome<CandidateBinding> Compute(QueryContext context, CallIdentity key)
    {
        var classified = context.Get(calls, key);
        if (!classified.IsSuccess) return classified.Propagate<CandidateBinding>();
        var candidates = classified.Value.Candidates?.Candidates ?? [];
        var site = context.Snapshot.Blocks.SelectMany(b => b.Statements.Select((s, i) => (Statement: s, Point: new Point(b.Identity, i))))
            .Single(x => x.Statement is Call call && call.Identity == key);
        bool Compatible(BoundValue value, TypeRef expected, bool receiver)
        {
            if (names is null) return true;
            var source = context.Get(sources, new(value.Source, site.Point));
            if (!source.IsSuccess) return true;
            var name = context.Get(names, source.Value);
            if (!name.IsSuccess || name.Value == NameLattice.Pending || name.Value.StaticType is not { } actual) return true;
            if (receiver && actual is ByRefRef byref) actual = byref.Element;
            // 原生整数不携带托管的符号与枚举身份；只用名义接收者或引用类型排除候选。
            if (!receiver && (!ManagedTypes.IsReferenceType(actual) || !ManagedTypes.IsReferenceType(expected))) return true;
            return types.IsAssignable(actual, expected);
        }
        var remaining = candidates.Where(candidate =>
        {
            if (candidate.Entry.Method is not { } method || candidate.Binding.Value is not { } binding) return true;
            if (binding.This is { } receiver && !Compatible(receiver, method.DeclaringType, true)) return false;
            return binding.Parameters.Select((value, i) => Compatible(value, method.Concrete(method.Method.Parameters[i].Type), false)).All(x => x);
        }).ToArray();
        return remaining.Length == 1 ? Outcome<CandidateBinding>.Success(remaining[0])
            : Outcome<CandidateBinding>.Failure(new("binding.direct-call.ambiguous",
                $"直接调用的身份不唯一：{candidates.Length} 个候选，静态类型筛选后 {remaining.Length} 个。"));
    }
}
