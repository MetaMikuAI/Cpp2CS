using System.Collections.Immutable;
using System.Numerics;
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
        var selectorMerges = function.Blocks.SelectMany(block => block.Merges)
            .Where(merge => merge.Inputs.Any(input => SnapshotRewrite.Dependencies([input.Value]).Any(selectors.ContainsKey)))
            .Select(merge => merge.Result).ToHashSet();
        StateQueries? state = null; QueryContext? context = null; IncomingValuesQuery? incoming = null;
        bool Direct(Term value, BigInteger constant, out BlockIdentity? handler)
        {
            if (value.Kind == TermKind.Slice && value.SliceLow == 0) value = value.Operands[0];
            if (selectors.TryGetValue(value, out var entry) && constant == entry.Value)
            { handler = entry.Handler; return true; }
            handler = null; return false;
        }
        bool Selected(Term value, BigInteger constant, BlockIdentity at, out BlockIdentity[] sources)
        {
            if (Direct(value, constant, out var handler)) { sources = [handler!]; return true; }
            sources = [];
            if (!SnapshotRewrite.Dependencies([value]).Any(selectorMerges.Contains)) return false;
            state ??= new StateQueries(); context ??= state.CreateContext(function); incoming ??= new(state);
            var projected = context.Get(incoming, new(value, at));
            if (!projected.IsSuccess || projected.Value.IsEmpty) return false;
            var found = new HashSet<BlockIdentity>();
            foreach (var input in projected.Value)
            {
                if (!Direct(input.Value, constant, out handler)) return false;
                found.Add(handler!);
            }
            sources = found.ToArray(); return true;
        }
        var mapped = new Dictionary<(Term Value, BlockIdentity At), Term>();
        Term Map(Term t, BlockIdentity at)
        {
            if (mapped.TryGetValue((t, at), out var known)) return known;
            if (t.Operator is CoreOperator { Operation: CoreOperation.Equal or CoreOperation.NotEqual } op)
            {
                for (int i = 0; i < 2; i++)
                    if (t.Operands[1 - i].ConstantValue is { } constant && Selected(t.Operands[i], constant, at, out var sources))
                    {
                        folded.UnionWith(sources); changed = true;
                        var foldedValue = function.Terms.Constant(op.Operation == CoreOperation.Equal ? 1 : 0, 1);
                        mapped.Add((t, at), foldedValue); return foldedValue;
                    }
            }
            var result = SnapshotRewrite.Rebuild(t, value => Map(value, at)); mapped.Add((t, at), result); return result;
        }
        foreach (var b in function.Blocks)
        {
            if (b.End is not Branch branch) continue;
            var condition = Map(branch.Condition, b.Identity);
            if (condition != branch.Condition)
                rewrite.Blocks[b.Identity] = b with { End = condition.ConstantValue is { } n ? new Jump(n == 0 ? branch.False : branch.True) : branch with { Condition = condition } };
        }
        return new(changed ? rewrite.Apply() : function, folded.ToImmutable(), failures.ToImmutable(), other);
    }
}
