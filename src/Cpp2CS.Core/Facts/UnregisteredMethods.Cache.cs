using Cpp2CS.Model;

namespace Cpp2CS.Facts;

public sealed partial class UnregisteredMethods
{
    internal sealed record CachedWitness(ulong Caller, ulong Site, int Method);
    internal sealed record CachedMethod(ulong Address, int Definition, string Abi, CachedWitness[] Witnesses, ulong[] Matches, int[] Adjustors);
    internal sealed record Snapshot(CachedMethod[] Methods, OwnerDecision[] Decisions, FactCheck[] Checks);

    internal Snapshot Capture(ProgramFacts facts)
    {
        var specs = new Dictionary<MethodRef, int>();
        for (var i = 0; i < facts.Model.MethodSpecs.Count; i++) specs.TryAdd(facts.Model.MethodSpecs[i], i);
        var entries = new Dictionary<CodeEntry, int>(ReferenceEqualityComparer.Instance);
        for (var i = 0; i < facts.Registrations.Entries.Count; i++) entries.Add(facts.Registrations.Entries[i], i);
        int Token(MethodRef method) => method.TypeArguments.Count == 0 && method.MethodArguments.Count == 0
            ? ~method.Method.Index : specs[method];
        return new(All.Select(m => new CachedMethod(m.Address, m.Definition.Index, Shape(m.Abi),
            m.Witnesses.Select(w => new CachedWitness(w.Caller, w.Site, Token(w.Instance))).ToArray(),
            m.ShapeMatches.ToArray(), m.Adjustors.Select(e => entries[e]).ToArray())).ToArray(),
            decisions.ToArray(), facts.Checks.All.Where(c => c.Name.StartsWith("unregistered.", StringComparison.Ordinal)).ToArray());
    }

    internal static UnregisteredMethods Restore(Snapshot snapshot, ProgramFacts facts)
    {
        var result = new UnregisteredMethods();
        var abi = new ManagedAbi(facts.Layouts);
        MethodRef Method(int token) => token < 0 ? new(facts.Model.Methods[~token], [], []) : facts.Model.MethodSpecs[token];
        foreach (var item in snapshot.Methods)
        {
            var definition = facts.Model.Methods[item.Definition];
            var witnesses = item.Witnesses.Select(w => new MethodWitness(w.Caller, w.Site, Method(w.Method))).ToArray();
            // Build 使用第一个封闭见证的 ABI；重新分类使类型引用归属本次模型。
            var signature = abi.Classify(witnesses[0].Instance, out _);
            if (signature is null || Shape(signature) != item.Abi || witnesses.Any(w => w.Instance.Method != definition))
                throw new InvalidDataException($"未注册事实缓存的 ABI/定义不一致：0x{item.Address:x}");
            result.accepted.Add(item.Address, new(item.Address, definition, signature, witnesses, item.Matches,
                item.Adjustors.Select(i => facts.Registrations.Entries[i]).ToArray()));
        }
        result.decisions.AddRange(snapshot.Decisions);
        foreach (var check in snapshot.Checks) facts.Checks.Add(check);
        return result;
    }
}
