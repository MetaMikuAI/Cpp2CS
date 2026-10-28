using Cpp2CS.Calls;
using Cpp2CS.Facts;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

/// <summary>源码会话共享的程序索引与已完成的方法整理；不缓存缺失摘要或调用方状态。</summary>
public sealed class SourceLibraryIndex(ProgramFacts facts)
{
    private readonly Dictionary<MethodRequest, ManagedBody> preparedBodies = [];
    private readonly Lazy<ILookup<TypeRef, MethodDef>> staticFieldReaders = new(() => facts.Model.Methods
        .Where(m => m.IsStatic && m.Parameters.Count == 1 && m.Address != 0
            && m.Owner.GenericParameters.Count == 0 && m.GenericParameters.Count == 0 && !ManagedTypes.IsVoid(m.ReturnType))
        .ToLookup(m => m.Parameters[0].Type));
    private readonly Lazy<IReadOnlyDictionary<MethodRef, ulong>> genericEntries = new(() => facts.Code.Functions
        .SelectMany(fn => facts.EntriesAt(fn.Start).Where(e => e.Kind == EntryKind.GenericMethod && e.Method is not null)
            .Select(e => (Method: e.Method!, Entry: fn.Start)))
        .GroupBy(p => p.Method).ToDictionary(g => g.Key, g => g.First().Entry));

    internal IEnumerable<MethodDef> StaticFieldReaders(TypeRef type) => staticFieldReaders.Value[type];
    internal IReadOnlyDictionary<MethodRef, ulong> GenericEntries => genericEntries.Value;

    internal ManagedBody Prepare(MethodRequest request, ManagedBody original, ManagedTypes types)
    {
        if (!preparedBodies.TryGetValue(request, out var body))
            preparedBodies.Add(request, body = SourceRewriter.Rewrite(original, types));
        return body;
    }
}
