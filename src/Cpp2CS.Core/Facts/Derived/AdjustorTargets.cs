namespace Cpp2CS.Facts.Derived;

/// <summary>注册的非泛型值类型调整桩经精确跳转指明的方法体；身份来自注册表。</summary>
public sealed record AdjustorTarget(ulong Address, MethodRef Method, IReadOnlyList<CodeEntry> Thunks);

public sealed class AdjustorTargets
{
    public static AdjustorTargets Empty { get; } = new([]);
    private readonly Dictionary<ulong, AdjustorTarget> targets;
    private AdjustorTargets(IEnumerable<AdjustorTarget> entries) => targets = entries.ToDictionary(e => e.Address);
    public AdjustorTarget? At(ulong address) => targets.GetValueOrDefault(address);
    public IReadOnlyCollection<AdjustorTarget> All => targets.Values;

    public static AdjustorTargets Build(BaseFacts facts)
    {
        var abi = new ManagedAbi(facts.Layouts);
        var candidates = new List<(ulong Address, CodeEntry Thunk)>();
        foreach (var entry in facts.Registrations.Entries.Where(e => e.Kind == EntryKind.AdjustorThunk && e.Method is not null))
        {
            var method = entry.Method!;
            if (method.Method.IsStatic || !method.Method.Owner.IsValueType || method.Method.Owner.GenericParameters.Count != 0
                || method.Method.GenericParameters.Count != 0 || !UnregisteredMethods.IsClosed(method)
                || abi.Classify(method, out _)?.This?.Pieces is not [{ Register.Bank: Ir.Bank.Gpr, Register.Index: 0, Width: 64, Offset: 0 }]) continue;
            // add x0, x0, #16; b body。不得越过任何其他指令或改变其他实参。
            if (facts.Code.At(entry.Address) is not { Size: 8 } thunk || thunk.Start != entry.Address
                || facts.Code.Word(entry.Address) != 0x91004000 || facts.Code.Word(entry.Address + 4) is not { } jump || !A64.IsB(jump)) continue;
            var target = A64.Imm26Target(jump, entry.Address + 4);
            if (facts.Code.At(target) is not { Region: CodeRegion.Managed } body || body.Start != target || facts.EntriesAt(target).Length != 0) continue;
            candidates.Add((target, entry));
        }
        var proven = candidates.GroupBy(c => c.Address).Where(g => g.Select(c => c.Thunk.Method).Distinct().Count() == 1)
            .Select(g => new AdjustorTarget(g.Key, g.First().Thunk.Method!, g.Select(c => c.Thunk).ToArray()));
        return new(proven);
    }
}
