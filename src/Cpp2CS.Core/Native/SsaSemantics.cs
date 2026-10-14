using System.Text.Json.Serialization;

namespace Cpp2CS.Native;

public sealed record SemanticTerm(string Kind, int Width, string Name, long Offset, string? Type, SemanticTerm[] Inputs)
{
    public string? ReadIdentity { get; init; }
    public string[] FieldPath { get; init; } = [];
    [JsonIgnore] public string Key => $"{Kind}:{Width}:{Name}:{Offset}:{Type}:{ReadIdentity}({string.Join(',', Inputs.Select(v => v.Key))})";
}
public sealed record SsaManagedCall(ulong Address, string Kind, string Name, string? ReturnType, SemanticTerm[] Arguments, string Value);
public sealed record SsaManagedStore(ulong Address, SemanticTerm AddressValue, SemanticTerm Value);
public sealed record SsaCallStorage(string Call, string Kind, SemanticTerm Address, SemanticTerm Value);

// SSA 是值身份的唯一来源。此层给值添加含义，不修改寄存器和控制流。
public sealed class SsaSemantics(NativeSsaProgram program, NativeMethod method, Symbols symbols,
    HeaderLayout layouts, NativeAbi abi, ElfImage image, RuntimeProfile runtime, NativeBodyEquivalence equivalents)
{
    public NativeSsaProgram Program => program;
    private readonly Dictionary<string, SsaValue> values = program.Values.ToDictionary(v => v.Id);
    private readonly Dictionary<string, SemanticTerm> cache = [];
    private readonly HashSet<string> active = [];
    private readonly RuntimeTypes runtimeTypes = new(layouts, abi.Managed, runtime);
    public Dictionary<string, NativeMethod> VirtualMethods { get; } = [];
    private readonly Dictionary<(string, string, int), SemanticTerm> memoryCache = [];
    public Dictionary<string, InterfaceCall> Interfaces { get; } = [];
    private readonly Dictionary<string, NativeMethod?> interfaceSignatures = [];
    private readonly Dictionary<string, Abi.CallLayout?> interfaceLayouts = [];
    public void Refresh() { cache.Clear(); memoryCache.Clear(); }
    public static SemanticTerm Term(string kind, int width = 64, string name = "", long offset = 0, string? type = null, params SemanticTerm[] inputs) => new(kind, width, name, offset, type, inputs);
    public static SemanticTerm Number(long value, int width = 64) => Term("constant", width, offset: value);
    public SsaValue Raw(string id) => values[id];
    public string Unalias(string id)
    {
        var seen = new HashSet<string>();
        while (values[id] is { Operation: "alias", Inputs: [var next] } && seen.Add(id)) id = next;
        return id;
    }
    public static SemanticTerm Add(SemanticTerm value, long offset) => offset == 0 ? value : value.Kind switch
    {
        "constant" => Number(unchecked(value.Offset + offset)),
        "address" => Add(value.Inputs[0], unchecked(value.Offset + offset)),
        _ => Term("address", 64, offset: offset, type: value.Type, inputs: [value])
    };
    public static (SemanticTerm Root, long Offset) AddressParts(SemanticTerm value) => value.Kind == "address" ? (value.Inputs[0], value.Offset) : (value, 0);
    public static SemanticTerm Slice(SemanticTerm value, int offset, int width)
    {
        if (offset == 0 && value.Width == width) return value;
        if (value.Kind == "phi") return Join(value.Name, width, value.Inputs.Select(v => Slice(v, offset, width)).ToArray());
        if (value.Kind == "constant" && width <= 64) return Number(unchecked((long)(((ulong)value.Offset >> offset) & (width == 64 ? ulong.MaxValue : (1UL << width) - 1))), width);
        if (value.Kind == "slice") return Slice(value.Inputs[0], checked((int)value.Offset + offset), width);
        if (value.Kind is "zero-extend" or "abi-extend" or "sign-extend" && offset + width <= value.Inputs[0].Width) return Slice(value.Inputs[0], offset, width);
        return Term("slice", width, offset: offset, inputs: [value]);
    }
    public SemanticTerm Resolve(string id)
    {
        id = Unalias(id);
        if (cache.TryGetValue(id, out var found)) return found;
        if (!active.Add(id)) return Term("ssa", values[id].Width, id);
        var result = Evaluate(values[id]);
        active.Remove(id);
        // 不缓存构造中的回引用；查询按完整定义重新求值。
        if (!Contains(result, "ssa")) cache[id] = result;
        return result;
    }
    public static bool Contains(SemanticTerm value, string kind) => value.Kind == kind || value.Inputs.Any(v => Contains(v, kind));
    private SemanticTerm Evaluate(SsaValue value)
    {
        SemanticTerm Input(int index) => Resolve(value.Inputs[index]);
        switch (value.Operation)
        {
            case "constant": return Number(value.Immediate, value.Width);
            case "parameter": return Term("parameter", value.Width, method.Parameters[(int)value.Immediate].Name, value.Immediate, value.Type);
            case "stack-address": return Term("stack", 64, "frame", type: "stack*");
            case "slice": return Slice(Input(0), (int)value.Immediate, value.Width);
            case "zero-extend": case "sign-extend": case "abi-extend":
                var original = Input(0);
                if (original.Width == value.Width) return original;
                if (original.Kind == "constant")
                {
                    var number = original.Offset;
                    if (value.Operation == "sign-extend" && original.Width < 64) number = number << (64 - original.Width) >> (64 - original.Width);
                    return Number(number, value.Width);
                }
                return Term(value.Operation, value.Width, inputs: [original]);
            case "add": case "sub": case "orr":
                var left = Input(0); var right = Input(1);
                if (right.Kind == "constant" && value.Operation != "orr") return Add(left, value.Operation == "sub" ? -right.Offset : right.Offset) with { Width = value.Width };
                if (left.Kind == "constant" && right.Kind == "constant") return Number(left.Offset | right.Offset, value.Width);
                if (value.Operation == "orr" && right.Kind == "constant" && right.Offset is >= 0 and < 16 && AddressParts(left) is var address && address.Root.Kind == "stack")
                    return Add(address.Root, address.Offset | right.Offset);
                return Term(value.Operation, value.Width, inputs: [left, right]);
            case "phi":
                return Join(value.Id, value.Width, value.Incoming!.Select(i => Resolve(i.Value)).ToArray());
            case "load": return Load(value.Id, value.Inputs[0], Input(1), value.Width);
            case "call": return CallValue(value.Id);
            case "clobber":
                if (TargetMethod(value.Inputs[0]) is { } targetMethod && abi.Classify(targetMethod) is { Return.Indirect: false } callLayout)
                {
                    var piece = callLayout.Return.Pieces.FirstOrDefault(p => p.Location is Abi.RegisterLocation r && r.Name.Equals(value.Register, StringComparison.OrdinalIgnoreCase));
                    if (piece is not null) return Slice(CallValue(value.Inputs[0]), piece.ValueOffset * 8, piece.Size * 8);
                }
                if (value.Register == "x0" && (Helper(value.Inputs[0]) is "Allocate" or "ResolveInterface" or "ResolveMetadata" or "EnsureClassMetadata" or "IsAssignable" or "CxxBeginCatch" or "CxxAllocateException" || Interfaces.ContainsKey(value.Inputs[0]))) return CallValue(value.Inputs[0]);
                return Term("unknown", value.Width, value.Id);
            case "exception-object": return Term("exception", value.Width, value.Id, type: value.Type);
            case "exception-selector": return Term("exception-selector", value.Width, value.Id, type: value.Type);
            default: return Term(value.Operation, value.Width, value.Id, value.Immediate, value.Type, value.Inputs.Select(Resolve).ToArray());
        }
    }
    private static SemanticTerm Join(string id, int width, SemanticTerm[] incoming)
    {
        var distinct = incoming.DistinctBy(v => v.Key).ToArray();
        return distinct.Length == 1 ? distinct[0] : Term("phi", width, id, inputs: distinct);
    }
    public string? Helper(string call)
    {
        var target = Resolve(values[call].Inputs[0]);
        return target.Kind == "constant" ? runtime.Helpers.GetValueOrDefault((ulong)target.Offset)?.Kind : null;
    }
    public NativeMethod? TargetMethod(string call)
    {
        if (Interfaces.TryGetValue(call, out var dispatch))
            return InterfaceSignature(new(dispatch.Interface, dispatch.Slot, dispatch.Name, dispatch.ReturnType, dispatch.ParameterTypes));
        if (VirtualMethods.TryGetValue(call, out var virtualMethod)) return abi.Normalize(virtualMethod);
        var target = Resolve(values[call].Inputs[0]);
        if (target.Kind != "constant") return null;
        if (runtime.Helpers.ContainsKey((ulong)target.Offset)) return null;
        if (symbols.Unique((ulong)target.Offset) is { } unique) return abi.Normalize(unique);
        var candidates = symbols.Methods.GetValueOrDefault((ulong)target.Offset, []);
        if (candidates.Length == 0)
        {
            var metadataArguments = Enumerable.Range(0, 8).Select(n => Argument(call, n))
                .Where(a => a.Kind == "metadata" && symbols.Metadata.GetValueOrDefault((ulong)a.Offset)?.Kind == "ScriptMetadataMethod").ToArray();
            candidates = metadataArguments.SelectMany(a => symbols.Methods.GetValueOrDefault(symbols.Metadata[(ulong)a.Offset].MethodAddress, []))
                .Where(m => equivalents.Equivalent((ulong)target.Offset, m.Address)).ToArray();
        }
        // 共享代码地址不是方法身份；MethodInfo 的槽内容与地址共同约束候选。
        var matches = new List<NativeMethod>();
        foreach (var candidate in candidates)
        {
            var info = Array.FindIndex(candidate.Parameters, p => p.Name == "method" && p.Type.StartsWith("MethodInfo"));
            if (info < 0 || info > 7) continue;
            var argument = Argument(call, info);
            if (argument.Kind != "metadata" || !symbols.Metadata.TryGetValue((ulong)argument.Offset, out var reference) || !equivalents.Equivalent(reference.MethodAddress, (ulong)target.Offset)) continue;
            var fullName = candidate.Name.Replace("$$", ".");
            if (reference.Name == "Method$" + fullName + "()") matches.Add(candidate);
        }
        return matches.Count == 1 ? abi.Normalize(matches[0]) : null;
    }
    public SemanticTerm Argument(string call, int register) => Resolve(values[call].Inputs[register + 2]);
    public SemanticTerm AbiArgument(string call, Abi.AbiValue argument) => Compose(argument.Pieces.Select(p =>
        p.Location is Abi.RegisterLocation r ? Slice(RegisterArgument(call, r.Name), r.BitOffset, p.Size * 8) :
        p.Location is Abi.StackLocation s && values[call].Inputs.Length > NativeSsa.CallStackPointerIndex ?
            LoadAtCall(call, Add(Resolve(values[call].Inputs[NativeSsa.CallStackPointerIndex]), s.Offset), p.Size) :
            Term("unknown", p.Size * 8, "missing-call-stack")).ToArray());
    public NativeMethod? InterfaceSignature(InterfaceMethod definition)
    {
        var key = InterfaceKey(definition);
        if (!interfaceSignatures.TryGetValue(key, out var signature)) interfaceSignatures[key] = signature = BuildInterfaceSignature(definition);
        return signature;
    }
    private static string InterfaceKey(InterfaceMethod definition) => definition.Type + "$$" + definition.Name + ":" + definition.ReturnType + "(" + string.Join(',', definition.ParameterTypes) + ")";
    private NativeMethod? BuildInterfaceSignature(InterfaceMethod definition)
    {
        string? Native(string type)
        {
            var native = symbols.NativeType(type);
            if (native is null)
            {
                var matches = symbols.DisplayTypes.Where(p => p.Value.EndsWith("." + type, StringComparison.Ordinal)).ToArray();
                if (matches.Length != 1) return null;
                native = matches[0].Key;
                type = matches[0].Value;
            }
            if (native.EndsWith('*') || native is "void" or "bool" or "int16_t" or "int32_t" or "int64_t" or "float" or "double") return native;
            var parent = abi.Managed.BaseTypeOf(type);
            return parent is "System.ValueType" or "System.Enum" ? native : parent is not null ? native + "*" : null;
        }
        var result = Native(definition.ReturnType);
        var parameters = definition.ParameterTypes.Select(Native).ToArray();
        if (result is null || parameters.Any(p => p is null)) return null;
        return new(0, definition.Type + "$$" + definition.Name, result,
            [new("Il2CppObject*", "__this"), .. parameters.Select((t, i) => new NativeParameter(t!, "arg" + i)), new("MethodInfo*", "method")], "");
    }
    public Abi.CallLayout? InterfaceLayout(InterfaceMethod definition)
    {
        var key = InterfaceKey(definition);
        if (!interfaceLayouts.TryGetValue(key, out var layout)) interfaceLayouts[key] = layout = InterfaceSignature(definition) is { } signature ? abi.Classify(signature) : null;
        return layout;
    }
    public SemanticTerm ReadCallStorage(string call, SemanticTerm address, int width) =>
        Load("receiver_" + call, values[call].Inputs[1], address, width);
    public SemanticTerm RegisterArgument(string call, string register)
    {
        var index = int.Parse(register.AsSpan(1));
        var position = register[0] switch { 'X' => index + 2, 'V' => index + 11, _ => -1 };
        return position >= 0 && position < values[call].Inputs.Length ? Resolve(values[call].Inputs[position]) :
            Term("unknown", register.StartsWith('V') ? 128 : 64, "missing-call-register:" + register);
    }
    public SemanticTerm LoadAtCall(string call, SemanticTerm address, int bytes) => Load("call-input:" + call, values[call].Inputs[1], address, bytes * 8);
    private SemanticTerm CallValue(string id)
    {
        var helper = Helper(id);
        if (helper == "Allocate")
        {
            var type = Argument(id, 0);
            return Term("new-object", 64, id, type: type.Type?.Replace("_c*", "_o*"), inputs: [type]);
        }
        if (helper == "ResolveMetadata") return MetadataContent(Argument(id, 0));
        if (helper == "EnsureClassMetadata") return Argument(id, 0);
        if (helper == "ResolveInterface") return Term("interface-entry", 64, id, type: "VirtualInvokeData*", inputs: [Argument(id, 0), Argument(id, 1), Slice(Argument(id, 2), 0, 16)]);
        var target = TargetMethod(id);
        return Term("call-result", target is null ? 64 : layouts.Size(target.ReturnType == "void" ? "int64_t" : target.ReturnType) * 8,
            id, type: target?.ReturnType);
    }
    private SemanticTerm MetadataContent(SemanticTerm slot) => slot.Kind == "metadata-slot" ?
        Term("metadata", 64, slot.Name, slot.Offset, slot.Type) : Term("unknown", 64, "unresolved-metadata", inputs: [slot]);
    private SemanticTerm Load(string id, string memory, SemanticTerm address, int width)
    {
        if (address.Kind == "constant" && width == 64)
        {
            var pointer = image.ReadResolvedPointer(unchecked((ulong)address.Offset));
            if (pointer is { } slot && symbols.Metadata.TryGetValue(slot, out var metadata))
                return Term("metadata-slot", 64, metadata.Name, (long)slot, metadata.ValueType);
        }
        if (address.Kind == "metadata-slot" && width == 64) return MetadataContent(address);
        if (address.Kind == "constant" && image.ReadImmutableScalar(unchecked((ulong)address.Offset), width / 8) is { } constant)
            return Number(unchecked((long)constant), width);
        if (AddressParts(address).Root.Kind == "stack")
        {
            var bytes = Enumerable.Range(0, width / 8).Select(n => ReadByte(memory, Add(address, n), [])).ToArray();
            var packed = Pack(bytes, id);
            if (packed is { Kind: "slice", Inputs: [var aggregate] } && aggregate.Kind == "call-storage" &&
                aggregate.Type is { } aggregateType && layouts.Field(aggregateType, checked((int)packed.Offset / 8), width / 8) is { } valueField)
                return Term("value-field", width, valueField.Name, packed.Offset / 8, valueField.Type, aggregate) with { ReadIdentity = id, FieldPath = valueField.Path };
            return packed;
        }
        var (root, offset) = AddressParts(address);
        if (runtimeTypes.Load(root, offset, width) is { } runtimeValue) return runtimeValue;
        if (root.Type is { } type && type.EndsWith('*') && layouts.ContainingField(type, checked((int)offset), width / 8) is { } field)
            return Term("field", width, field.Name, offset, field.Type, root) with { ReadIdentity = id, FieldPath = field.Path };
        return Term("load", width, id, inputs: [address]);
    }
    private SemanticTerm ReadByte(string memory, SemanticTerm address, HashSet<string> visiting)
    {
        memory = Unalias(memory);
        var key = (memory, address.Key, 8);
        if (memoryCache.TryGetValue(key, out var found)) return found;
        if (!visiting.Add(memory)) return Term("memory-cycle", 8, memory);
        var value = values[memory];
        SemanticTerm result;
        if (value.Operation == "store")
        {
            var destination = Resolve(value.Inputs[1]);
            var (a, ao) = AddressParts(address); var (b, bo) = AddressParts(destination);
            var size = values[value.Inputs[2]].Width / 8;
            if (a.Key == b.Key && ao >= bo && ao < bo + size) result = Slice(Resolve(value.Inputs[2]), (int)(ao - bo) * 8, 8);
            else if (a.Key == b.Key || a.Kind == "stack" && b.Kind is "constant" or "metadata-slot" or "parameter" or "new-object") result = ReadByte(value.Inputs[0], address, visiting);
            else result = Term("unknown", 8, "possible-alias:" + memory);
        }
        else if (value.Operation == "phi")
        {
            var alternatives = value.Incoming!.Select(i => ReadByte(i.Value, address, new(visiting))).Where(t => t.Kind != "memory-cycle").ToArray();
            result = alternatives.Length == 0 ? Term("memory-cycle", 8, memory) : Join(memory, 8, alternatives);
        }
        else if (value.Operation is "call-memory" or "exception-memory")
        {
            var call = value.Inputs[1];
            var storage = CallStorage(call);
            var (root, offset) = AddressParts(address);
            var uncertainStorage = storage.Any(s => AddressParts(s.Address).Root is var destination && destination.Key != root.Key &&
                destination.Kind is not ("constant" or "metadata-slot" or "parameter" or "new-object"));
            var overlaps = storage.Where(s => AddressParts(s.Address) is var a && a.Root.Key == root.Key &&
                offset >= a.Offset && offset < a.Offset + s.Value.Width / 8).ToArray();
            if (overlaps.Length != 0)
            {
                // 正常返回才保证返回缓冲完整；异常出口可能只写入了部分内容。
                result = overlaps.Length == 1 && !uncertainStorage && value.Operation == "call-memory"
                    ? Slice(overlaps[0].Value, checked((int)(offset - AddressParts(overlaps[0].Address).Offset) * 8), 8)
                    : Term("unknown", 8, "call-storage-not-complete:" + call);
                visiting.Remove(memory);
                return result;
            }
            var helper = Helper(call);
            var pureStack = Arm64Calls.PreservesCallerStack(helper);
            var target = TargetMethod(call);
            if (!pureStack && target is not null)
            {
                var layout = abi.Classify(target);
                pureStack = layout is not null && layout.Arguments.Take(target.Parameters.LastOrDefault()?.Name == "method" ? layout.Arguments.Count - 1 : layout.Arguments.Count).All(a =>
                {
                    var argument = AbiArgument(call, a);
                    return !Contains(argument, "stack") && (!a.Pieces.Any(p => p.Location is Abi.StackLocation) ||
                        !Contains(argument, "unknown") && !Contains(argument, "ssa") && !Contains(argument, "memory-cycle"));
                });
            }
            // X8 不在显式实参列表中；未知返回目标仍可能与查询位置别名。
            if (uncertainStorage) pureStack = false;
            result = pureStack ? ReadByte(value.Inputs[0], address, visiting) : Term("unknown", 8, "call-may-write:" + call);
        }
        else result = Term("unknown", 8, "uninitialized-stack:" + memory);
        visiting.Remove(memory);
        if (!Contains(result, "memory-cycle") && !Contains(result, "ssa")) memoryCache[key] = result;
        return result;
    }
    public SsaCallStorage[] CallStorage(string call)
    {
        var target = TargetMethod(call);
        if (target is null || abi.Classify(target) is not { } layout) return [];
        var effects = new List<SsaCallStorage>();
        if (layout.Return is { Indirect: true, Pieces: var pieces } && pieces.Count == 1 && pieces[0].Location is Abi.RegisterLocation register)
            effects.Add(new(call, "indirect-return", RegisterArgument(call, register.Name), CallValue(call)));
        // 可变值类型接收者使用调用后的存储身份，不沿用调用前的值或字段常量。
        if (abi.MutableReceiverType(target) is { } type &&
            layout.Arguments[0].Pieces is var receiverPieces && receiverPieces.Count == 1 && receiverPieces[0].Location is Abi.RegisterLocation receiverRegister)
        {
            var address = RegisterArgument(call, receiverRegister.Name);
            effects.Add(new(call, "mutable-receiver", address, Term("call-storage", layouts.Size(type) * 8, call, type: type, inputs: [address])));
        }
        return effects.ToArray();
    }
    public SsaCallStorage[] CallStorages() => program.Instructions.Where(i => i.Call is not null).SelectMany(i => CallStorage(i.Call!)).ToArray();
    public static SemanticTerm Pack(SemanticTerm[] bytes, string name)
    {
        if (bytes.All(b => b.Kind == "phi" && b.Name == bytes[0].Name && b.Inputs.Length == bytes[0].Inputs.Length))
            return Join(bytes[0].Name, bytes.Length * 8, Enumerable.Range(0, bytes[0].Inputs.Length).Select(n => Pack(bytes.Select(b => b.Inputs[n]).ToArray(), name)).ToArray());
        if (bytes.All(b => b.Kind == "constant") && bytes.Length <= 8)
            return Number(unchecked((long)bytes.Select((b, n) => (ulong)(b.Offset & 255) << (n * 8)).Aggregate(0UL, (a, b) => a | b)), bytes.Length * 8);
        if (bytes[0].Kind == "slice" && bytes.Select((b, n) => b.Kind == "slice" && b.Inputs[0].Key == bytes[0].Inputs[0].Key && b.Offset == bytes[0].Offset + n * 8).All(b => b))
            return Slice(bytes[0].Inputs[0], (int)bytes[0].Offset, bytes.Length * 8);
        return Term("compose", bytes.Length * 8, name, inputs: bytes);
    }
    public static SemanticTerm Compose(SemanticTerm[] pieces) => pieces.Length == 1 ? pieces[0] :
        Pack(pieces.SelectMany(p => Enumerable.Range(0, p.Width / 8).Select(n => Slice(p, n * 8, 8))).ToArray(), "");
    public SsaManagedCall[] Calls() => program.Instructions.Where(i => i.Call is not null).Select(i =>
    {
        var id = i.Call!; var target = TargetMethod(id); var helper = Helper(id);
        var arguments = new List<SemanticTerm>();
        if (Interfaces.TryGetValue(id, out var dispatch) && InterfaceLayout(new(dispatch.Interface, dispatch.Slot, dispatch.Name, dispatch.ReturnType, dispatch.ParameterTypes)) is { } interfaceLayout)
            return new SsaManagedCall(i.Address, "interface", dispatch.Interface + "." + dispatch.Name, dispatch.ReturnType,
                interfaceLayout.Arguments.Take(interfaceLayout.Arguments.Count - 1).Select(a => AbiArgument(id, a)).ToArray(), id);
        if (target is not null && abi.Classify(target) is { } layout)
            foreach (var argument in layout.Arguments)
            {
                arguments.Add(AbiArgument(id, argument));
            }
        else arguments.AddRange(Enumerable.Range(0, Arm64Calls.HelperArgumentCount(helper) ?? 9).Select(n => Argument(id, n)));
        return new SsaManagedCall(i.Address, helper is null ? target is null ? "indirect" : VirtualMethods.ContainsKey(id) ? "virtual" : "managed" : "runtime", helper ?? target?.Name ?? "indirect", target?.ReturnType, arguments.ToArray(), id);
    }).ToArray();
    public SsaManagedStore[] Stores() => program.Instructions.SelectMany(i => i.Effects.SelectMany(id => StoreValues(id).Select(v =>
        new SsaManagedStore(i.Address, Resolve(v.Inputs[1]), Resolve(v.Inputs[2]))))).ToArray();
    private IEnumerable<SsaValue> StoreValues(string id)
    {
        var value = values[Unalias(id)];
        if (value.Operation != "store") yield break;
        if (values[Unalias(value.Inputs[0])] is { Operation: "store" } priorStore && priorStore.Id[..priorStore.Id.LastIndexOf('_')] == value.Id[..value.Id.LastIndexOf('_')])
            foreach (var prior in StoreValues(value.Inputs[0])) yield return prior;
        yield return value;
    }
}
