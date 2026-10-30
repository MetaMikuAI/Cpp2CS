using Cpp2CS.Facts;
using Cpp2CS.Recovery;
using static Cpp2CS.Pipeline.RecoveryReport;

namespace Cpp2CS.Pipeline;

internal static class SelectionStage
{
    internal sealed record Selection(RecoveryTarget[] Targets, MethodDef[] Methods,
        Dictionary<MethodDef, ulong[]> NativeEntries, MethodDef[] Unselected);

    internal static Selection Select(RecoveryRequest request, ProgramFacts facts, Action<string> Log)
    {
        var namespaces = request.Namespaces;
        var assembliesFilter = request.Assemblies;
        var all = request.All || assembliesFilter is not null;
        var list = request.Methods;
        var limit = request.Limit;
        RecoveryTarget[] selected;
        if (list is null)
        {
            bool Included(MethodDef m) => (all || InNamespaces(m.Owner, namespaces))
                && (assembliesFilter is null || assembliesFilter.Contains(m.Owner.Assembly, StringComparer.Ordinal));
            var ordinary = facts.Model.Methods.Where(m => m.Address != 0 && Included(m)
                && facts.Code.RegionOf(m.Address) == CodeRegion.Managed).Select(m => new RecoveryTarget(new(m, [], []), m.Address));
            var shared = facts.Model.Code.SelectMany(p => p.Value.Where(o => o.IsInstance && Included(o.Method.Method))
                .Select(o => new RecoveryTarget(o.Method, p.Key))).Where(t => t.Instance.Method.Address == 0)
                .GroupBy(t => t.Instance.Method).Select(g => g.OrderBy(t => t.Instance.TypeArguments.Concat(t.Instance.MethodArguments)
                    .Any(a => !ManagedTypes.IsReferenceType(a) || FieldLayouts.IsFullyShared(a))).ThenBy(t => t.Entry).First());
            selected = ordinary.Concat(shared).Take(limit).ToArray();
            Log($"恢复 {selected.Length} 个方法（{(all ? assembliesFilter is null ? "全程序方法定义" : string.Join(", ", assembliesFilter) : string.Join(", ", namespaces))}）");
        }
        else
        {
            selected = File.ReadLines(list).Where(l => l.Length > 0 && !l.StartsWith('#')).Select(l => l.Split('\t'))
                .Select(f => RecoveryTarget.Find(facts, Convert.ToUInt64(f[0], 16), f[1])).ToArray();
            Log($"恢复 {selected.Length} 个方法（{list}）");
        }
        if (selected.GroupBy(t => t.Instance.Method).Any(g => g.Count() > 1))
            throw new InvalidDataException("同一方法定义只能选择一个原生入口，不能以多个实例体覆盖同一 CIL 方法");
        var methods = selected.Select(t => t.Instance.Method).ToArray();
        var selectedDefinitions = methods.ToHashSet();
        var selectedTypes = methods.Select(m => Top(m.Owner)).ToHashSet();
        var nativeEntries = facts.Model.Code.SelectMany(p => p.Value.Select(o => (Method: o.Method.Method, Entry: p.Key)))
            .Where(p => selectedTypes.Contains(Top(p.Method.Owner))).GroupBy(p => p.Method)
            .ToDictionary(g => g.Key, g => g.Select(p => p.Entry).Distinct().Order().ToArray());
        var unselected = facts.Model.Methods.Where(m => selectedTypes.Contains(Top(m.Owner)) && !selectedDefinitions.Contains(m))
            .OrderBy(m => m.Index).ToArray();

        return new(selected, methods, nativeEntries, unselected);
    }
}
