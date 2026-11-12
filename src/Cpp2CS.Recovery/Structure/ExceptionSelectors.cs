using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Structure;

public sealed record ExceptionSelectorFolding(NativeFunction Function, ImmutableHashSet<BlockIdentity> Folded,
    ImmutableDictionary<BlockIdentity, Reason> Failures, int OtherTypes);

/// <summary>在托管异常包装假设下折叠唯一包装子句的相等测试；不赋予选择值其他托管含义。</summary>
public static class ExceptionSelectors
{
    public static ExceptionSelectorFolding Run(NativeFunction function, RuntimeSpec spec)
    {
        var handlers = function.Blocks.Where(b => b.Handler is not null).ToArray();
        if (handlers.Length == 0) return new(function, [], ImmutableDictionary<BlockIdentity, Reason>.Empty, 0);
        var failures = ImmutableDictionary.CreateBuilder<BlockIdentity, Reason>();
        var selectors = new Dictionary<Term, (BlockIdentity Handler, long Value)>();
        int other = 0;
        foreach (var h in handlers)
        {
            var catches = h.Handler!.Clauses.Where(c => c.Kind != ClauseKind.Cleanup).ToArray();
            if (catches.Any(c => c.Kind == ClauseKind.Catch && (spec.ManagedExceptionWrapperTypeName is null || c.TypeName != spec.ManagedExceptionWrapperTypeName)))
            { other++; failures[h.Identity] = new("lowering.Exception.Selector", "子句表含其他 C++ 类型或未识别的类型身份"); continue; }
            if (catches.Length == 1 && catches[0].Kind == ClauseKind.Catch && catches[0].Selector > 0)
                selectors.Add(h.Handler.Selector, (h.Identity, catches[0].Selector));
        }
        var folded = ImmutableHashSet.CreateBuilder<BlockIdentity>();
        var rewrite = new SnapshotRewrite(function); bool changed = false;
        var mapped = new Dictionary<Term, Term>();
        Term Map(Term t)
        {
            if (mapped.TryGetValue(t, out var known)) return known;
            if (t.Operator is CoreOperator { Operation: CoreOperation.Equal or CoreOperation.NotEqual } op)
            {
                for (int i = 0; i < 2; i++)
                {
                    var value = t.Operands[i]; var constant = t.Operands[1 - i].ConstantValue;
                    if (value.Kind == TermKind.Slice && value.SliceLow == 0) value = value.Operands[0];
                    if (constant is { } n && selectors.TryGetValue(value, out var entry) && n == entry.Value)
                    {
                        folded.Add(entry.Handler); changed = true;
                        var foldedValue = function.Terms.Constant(op.Operation == CoreOperation.Equal ? 1 : 0, 1);
                        mapped.Add(t, foldedValue); return foldedValue;
                    }
                }
            }
            var result = SnapshotRewrite.Rebuild(t, Map); mapped.Add(t, result); return result;
        }
        foreach (var b in function.Blocks)
        {
            if (b.End is not Branch branch) continue;
            var condition = Map(branch.Condition);
            if (condition != branch.Condition)
                rewrite.Blocks[b.Identity] = b with { End = condition.ConstantValue is { } n ? new Jump(n == 0 ? branch.False : branch.True) : branch with { Condition = condition } };
        }
        return new(changed ? rewrite.Apply() : function, folded.ToImmutable(), failures.ToImmutable(), other);
    }
}
