namespace Cpp2CS.Native;

public sealed record InterfaceCall(ulong Address, string Interface, int Slot, string Name, string ReturnType,
    string[] ParameterTypes, string Receiver, string Entry, ulong[] LookupLoop, string Evidence);

// 同时证明快路径的表查找和慢路径 helper，再把间接目标归约为接口槽。
public sealed class InterfaceDispatch(SsaSemantics semantics, HeaderLayout layouts, ManagedNames managed, RuntimeProfile runtime)
{
    public List<string> Diagnostics { get; } = [];
    private NativeSsaProgram Program => semantics.Program;
    private SsaValue Raw(string id) => semantics.Raw(semantics.Unalias(id));
    private string Strip(string id)
    {
        var value = Raw(id);
        while (value.Operation is "sign-extend" or "zero-extend" or "abi-extend" || value.Operation == "slice" && value.Immediate == 0)
            value = Raw(value.Inputs[0]);
        return value.Id;
    }
    private bool Same(string a, string b) => Strip(a) == Strip(b) || semantics.Resolve(a).Key == semantics.Resolve(b).Key;
    private bool Constant(string id, long number) => semantics.Resolve(id) is { Kind: "constant" } value && value.Offset == number;
    private string? Addend(string id, long offset)
    {
        if (offset == 0) return Strip(id);
        var value = Raw(Strip(id));
        return value.Operation == "add" && Constant(value.Inputs[1], offset) ? Strip(value.Inputs[0]) : null;
    }
    private string? LoadAddress(string id, int width)
    {
        var value = Raw(Strip(id));
        return value.Operation == "load" && value.Width == width ? value.Inputs[1] : null;
    }
    private string? LoadBase(string id, long offset, int width = 64) => LoadAddress(id, width) is { } address ? Addend(address, offset) : null;
    private SsaValue? Phi(string id) => Raw(Strip(id)) is { Operation: "phi" } phi ? phi : null;
    public InterfaceCall[] Recover()
    {
        var result = new List<InterfaceCall>();
        foreach (var instruction in Program.Instructions.Where(i => i.Call is not null))
        {
            var call = Raw(instruction.Call!);
            if (LoadAddress(call.Inputs[0], 64) is not { } entry || Phi(entry) is not { } join) continue;
            var incoming = join.Incoming!.Select(i => Raw(Strip(i.Value))).DistinctBy(v => v.Id).ToArray();
            if (incoming.Length != 2) continue;
            var fallback = incoming.SingleOrDefault(v => v.Operation == "clobber" && v.Register == "x0" && semantics.Helper(v.Inputs[0]) == "ResolveInterface");
            if (fallback is null) continue;
            Diagnostics.Add($"0x{instruction.Address:x}: interface entry phi identified");
            var slow = Raw(fallback.Inputs[0]);
            var receiver = slow.Inputs[2]; var interfaceType = semantics.Resolve(slow.Inputs[3]); var slot = SsaSemantics.Slice(semantics.Resolve(slow.Inputs[4]), 0, 16);
            var typeName = interfaceType.Kind == "runtime-class" ? interfaceType.Name :
                interfaceType.Kind == "metadata" && interfaceType.Name.EndsWith("_TypeInfo") ? interfaceType.Name[..^9] : null;
            if (typeName is null || slot.Kind != "constant") continue;
            var definition = managed.InterfaceSlot(typeName, (int)slot.Offset);
            Diagnostics.Add($"0x{instruction.Address:x}: {interfaceType.Name} slot {slot.Offset} => {definition?.Name ?? "unresolved"}");
            if (definition is null || semantics.InterfaceLayout(definition) is not { } layout || !Same(call.Inputs[2], receiver)) continue;
            var info = semantics.AbiArgument(instruction.Call!, layout.Arguments[^1]);
            var methodOffset = layouts.Members("VirtualInvokeData").Single(f => f.Name == "method").Offset;
            if (info is not { Kind: "load", Width: 64, Inputs: [var infoAddress] } ||
                infoAddress.Key != SsaSemantics.Add(semantics.Resolve(entry), methodOffset).Key) continue;
            var fast = incoming.Single(v => v != fallback);
            Diagnostics.Add($"0x{instruction.Address:x}: receiver and MethodInfo match");
            var loop = ProveLookup(fast.Id, receiver, slow.Inputs[3], (int)slot.Offset, slow.Address);
            if (loop is null) continue;
            var proof = new InterfaceCall(instruction.Address, definition.Type, definition.Slot, definition.Name, definition.ReturnType,
                definition.ParameterTypes, Strip(receiver), join.Id, loop,
                "Clang class/interface-pair/vtable layout; bounded cursor/count recurrence; interface equality branch; same receiver, slot and MethodInfo on both paths");
            result.Add(proof);
            semantics.Interfaces[instruction.Call!] = proof;
            semantics.Refresh();
        }
        return result.ToArray();
    }
    private ulong[]? ProveLookup(string fast, string receiver, string interfaceType, int slot, ulong fallback)
    {
        var fields = layouts.Flatten("Il2CppClass", 0).ToArray();
        var vtable = fields.Single(f => f.Name == "vtable").Offset;
        var table = fields.Single(f => f.Name == "interfaceOffsets").Offset;
        var count = runtime.Fields.SingleOrDefault(f => f.Record == "Il2CppClass" && f.Field == "interface_offsets_count")?.Offset ?? fields.Single(f => f.Name == "interface_offsets_count").Offset;
        var pair = layouts.Members("Il2CppRuntimeInterfaceOffsetPair");
        var pairOffset = pair.Single(f => f.Name == "offset").Offset;
        var pairType = pair.Single(f => f.Name == "interfaceType").Offset;
        var pairSize = layouts.Size("Il2CppRuntimeInterfaceOffsetPair");
        var entrySize = layouts.Size("VirtualInvokeData");
        if (Addend(fast, vtable) is not { } sumId || Raw(sumId) is not { Operation: "add" } sum) return Failed("vtable base");
        var klass = sum.Inputs[0];
        if (LoadBase(klass, 0) is not { } objectId || !Same(objectId, receiver)) return Failed("class receiver");
        var shift = Raw(sum.Inputs[1]);
        if (shift.Operation != "shift-left" || (1L << (int)shift.Immediate) != entrySize) return Failed("vtable stride");
        if (Addend(shift.Inputs[0], slot) is not { } offset || LoadAddress(offset, 32) is not { } cursor || Phi(cursor) is not { } cursorPhi) return Failed("slot offset");
        var cursorInputs = cursorPhi.Incoming!.Select(i => i.Value).DistinctBy(semantics.Unalias).ToArray();
        if (cursorInputs.Length != 2 || !cursorInputs.Any(i => Addend(i, pairSize) is { } prior && Same(prior, cursorPhi.Id))) return Failed("cursor recurrence");
        var seed = cursorInputs.SingleOrDefault(i => Addend(i, pairOffset) is { } tableLoad && LoadBase(tableLoad, table) is { } baseClass && Same(baseClass, klass));
        if (seed is null) return Failed("interface table base");
        Diagnostics.Add("lookup cursor and slot arithmetic proved");
        foreach (var cycle in Program.Flow.Cycles)
        {
            var nodes = Program.Flow.Nodes.Where(n => cycle.Contains(n.Instruction.Address)).ToArray();
            if (nodes.Any(n => n.Instruction.Mnemonic is "bl" or "blr" || n.Instruction.Mnemonic.StartsWith("st"))) continue;
            var equal = Only(nodes.Where(n => n.Instruction.Mnemonic == "b.eq"));
            var repeat = Only(nodes.Where(n => n.Instruction.Mnemonic == "b.ne"));
            if (equal is null || repeat is null) continue;
            var comparison = Compare(equal.Instruction.Address);
            if (comparison is null || !Same(comparison.Inputs[1], interfaceType) ||
                LoadAddress(comparison.Inputs[0], 64) is not { } typeAddress || Addend(typeAddress, pairType - pairOffset) is not { } typeCursor || !Same(typeCursor, cursorPhi.Id)) continue;
            Diagnostics.Add("lookup interface equality proved");
            var decrement = Compare(repeat.Instruction.Address);
            if (decrement is null || !Constant(decrement.Inputs[1], 1) || Phi(decrement.Inputs[0]) is not { } counter) continue;
            var counterInputs = counter.Incoming!.Select(i => i.Value).DistinctBy(semantics.Unalias).ToArray();
            if (counterInputs.Length != 2 || !counterInputs.Any(i => LoadBase(i, count, 16) is { } c && Same(c, klass)) ||
                !counterInputs.Any(i => Raw(Strip(i)) is { Operation: "sub" } sub && Same(sub.Inputs[0], counter.Id) && Constant(sub.Inputs[1], 1))) continue;
            Diagnostics.Add("lookup counter recurrence proved");
            var zeroGuard = Program.Instructions.Any(i => i.Condition is { } c && Raw(c) is { Operation: "zero" } test &&
                LoadBase(test.Inputs[0], count, 16) is { } countClass && Same(countClass, klass) &&
                EdgeReaches(i.Address, "taken", fallback) && EdgeReaches(i.Address, "not-taken", cycle[0]));
            if (!zeroGuard || !EdgeReaches(equal.Instruction.Address, "taken", Raw(fast).Address) ||
                !equal.Edges.Any(e => e.Kind == "not-taken" && e.Target is { } p && cycle.Contains(p)) ||
                !repeat.Edges.Any(e => e.Kind == "taken" && e.Target == cycle[0]) || !EdgeReaches(repeat.Instruction.Address, "not-taken", fallback)) continue;
            return cycle;
        }
        return null;
    }
    private ulong[]? Failed(string reason) { Diagnostics.Add("unproved: " + reason); return null; }
    private static T? Only<T>(IEnumerable<T> source) where T : class { var items = source.Take(2).ToArray(); return items.Length == 1 ? items[0] : null; }
    private bool EdgeReaches(ulong from, string kind, ulong target)
    {
        var nodes = Program.Flow.Nodes.ToDictionary(n => n.Instruction.Address);
        var edge = nodes[from].Edges.Single(e => e.Kind == kind);
        var seen = new HashSet<ulong>(); var pc = edge.Target;
        while (pc is { } address && seen.Add(address))
        {
            if (address == target) return true;
            if (!nodes.TryGetValue(address, out var node) || node.Edges.Length != 1) return false;
            pc = node.Edges[0].Target;
        }
        return false;
    }
    private SsaValue? Compare(ulong pc)
    {
        var condition = Program.Instructions.Single(i => i.Address == pc).Condition;
        return condition is not null && Raw(condition).Inputs is [var flags] && Raw(flags) is { Operation: "compare" } comparison ? comparison : null;
    }
}
