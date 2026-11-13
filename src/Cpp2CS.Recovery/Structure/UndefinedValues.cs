using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Structure;

public sealed partial class UnobservableEffects
{
    private static HashSet<Term> DefinedCallResults(ClassifiedCall classified, Call call) => classified.Result?.Source is TermSource value
        ? SnapshotRewrite.Dependencies([value.Term]) : classified.Function?.Signature?.ReturnType.Size == 0 ? []
        : call.Results.Select(r => r.Value).ToHashSet();

    // 对未定义位作精化；多个有定义来源仍须由调用者保留原合流。
    private static Term? MergeValue(IEnumerable<Term> inputs, out bool refined)
    {
        refined = false;
        var values = inputs.Distinct().ToArray();
        if (values.Length == 1) return values[0];
        var defined = values.Where(t => t.Kind != TermKind.Undefined).ToArray();
        if (defined.Length != 1) return null;
        refined = true; return defined[0];
    }

    private void RefineGuardResults(Cpp2CS.Kernel.Queries.QueryContext c, SnapshotRewrite edit,
        IEnumerable<Call> moved, ref bool assumed)
    {
        var undefined = new HashSet<Term>();
        foreach (var call in moved)
        {
            var classified = c.Get(calls, call.Identity);
            if (!classified.IsSuccess) continue;
            var defined = DefinedCallResults(classified.Value, call);
            foreach (var output in call.Results.Where(r => !defined.Contains(r.Value)))
            {
                undefined.Add(output.Value);
                edit.Replacements[output.Value] = c.Snapshot.Terms.Undefined(output.Value.Width);
            }
        }
        if (undefined.Count == 0) return;
        Term Map(Term value) => edit.Replacements.TryGetValue(value, out var replacement) ? replacement : SnapshotRewrite.Rebuild(value, Map);
        foreach (var merge in c.Snapshot.Blocks.SelectMany(b => b.Merges))
        {
            if (!SnapshotRewrite.Dependencies(merge.Inputs.Select(i => i.Value)).Overlaps(undefined)) continue;
            var value = MergeValue(merge.Inputs.Select(i => Map(i.Value)), out var refined);
            if (!refined || value is null) continue;
            // 入口值与纯输入表达式在删边后仍可用；不从将被删除的臂搬运定义。
            if (SnapshotRewrite.Dependencies([value]).Any(t => t.Identity is not null && t.Identity is not (EntryAtom or RootAtom or CallerValue))) continue;
            edit.Replacements[merge.Result] = value;
            assumed = true;
        }
    }
}
