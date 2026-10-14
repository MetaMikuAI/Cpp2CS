using Cpp2CS.Abi;

namespace Cpp2CS.Native;

public sealed record SsaInput(ulong Predecessor, string Edge, string Value);
public sealed record SsaValue(string Id, string Operation, int Width, string[] Inputs, string? Type = null,
    long Immediate = 0, SsaInput[]? Incoming = null, ulong Address = 0, string? Register = null);
public sealed record SsaInstruction(ulong Address, string[] Effects, string? Condition, string? Call);
public sealed record NativeSsaProgram(NativeControlFlow Flow, SsaValue[] Values, SsaInstruction[] Instructions, string[] Problems);

// 值定义引用身份，不嵌套表达式。回边可引用尚未填完的 Phi，构造后再消除平凡合流。
public sealed class NativeSsa(NativeControlFlow flow, NativeMethod method, NativeAbi abi, Symbols symbols)
{
    // call 输入依次为目标、内存、X0..X8、V0..V7、SP。
    public const int CallStackPointerIndex = 19;
    private readonly Dictionary<ulong, MachineEffects> effects = flow.Nodes.ToDictionary(n => n.Instruction.Address, n => Arm64Effects.Lower(n.Instruction));
    private readonly Dictionary<string, SsaValue> values = [];
    private readonly Dictionary<(ulong, string), string> inputs = [];
    private readonly Queue<(ulong Pc, string Register)> pendingInputs = [];
    private readonly Dictionary<(ulong, string), string> outputs = [];
    private readonly Dictionary<ulong, NativeFlowNode> nodes = flow.Nodes.ToDictionary(n => n.Instruction.Address);
    private readonly Dictionary<ulong, NativeEdge[]> predecessors = flow.Nodes.SelectMany(n => n.Edges)
        .Where(e => e.Target.HasValue && e.Kind != "tail-call").GroupBy(e => e.Target!.Value).ToDictionary(g => g.Key, g => g.ToArray());
    private readonly Dictionary<string, string> entry = [];
    private readonly List<string> problems = [];

    public NativeSsaProgram Build()
    {
        method = abi.Normalize(method);
        var contract = NativeInterface.Describe(method, abi);
        if (contract is null) throw new InvalidDataException("SSA 入口 ABI 未确认");
        var layout = contract.Layout;
        entry["sp"] = Define("entry_sp", "stack-address", 64, [], "stack-address");
        entry["memory"] = Define("entry_memory", "memory", 0, []);
        if (flow.Nodes.Any(n => n.Edges.Any(e => e.Kind == "tail-call")))
            foreach (var register in TailCallProof.Registers.Where(r => r != "sp"))
                entry[register] = Define("entry_" + register, "unknown", Width(register), []);
        foreach (var binding in contract.Arguments)
        {
            var index = binding.Index;
            var argument = binding.Storage;
            var root = Define($"arg_{index}", "parameter", binding.ValueWidth, [], binding.Parameter.Type, index);
            if (argument.Indirect)
            {
                var address = Define($"arg_address_{index}", "parameter-address", 64, [root], binding.CarrierType, index);
                entry["memory"] = Define($"entry_argument_{index}", "store", 0, [entry["memory"], address, root]);
                root = address;
            }
            foreach (var piece in argument.Pieces)
            {
                var part = Slice(root, piece.ValueOffset * 8, piece.Size * 8);
                if (piece.Location is RegisterLocation register)
                    entry[register.Name.ToLowerInvariant()] = Extend(part, register.Name.StartsWith('V') ? 128 : 64, false, true);
                else if (piece.Location is StackLocation stack)
                {
                    var address = Define($"entry_stack_address_{stack.Offset}", "add", 64, [entry["sp"], Constant(stack.Offset)]);
                    entry["memory"] = Define($"entry_stack_{stack.Offset}", "store", 0, [entry["memory"], address, part]);
                }
            }
        }
        var instructions = new List<SsaInstruction>();
        foreach (var node in flow.Nodes.Where(n => n.Reachable))
        {
            var effect = effects[node.Instruction.Address];
            var pc = effect.Source.Address;
            if (effect.Unsupported is not null) problems.Add($"0x{pc:x}: {effect.Unsupported}");
            var outputs = effect.Writes.Select(register => Out(pc, register)).ToList();
            var condition = effect.Condition is null ? null : Value(pc, effect.Condition);
            var tail = node.Edges.Any(e => e.Kind == "tail-call");
            var call = effect.Call is not null || tail ? Call(pc) : null;
            if (tail)
                outputs.Add(Define($"tail_state_{pc:x}", "tail-state", 0, TailCallProof.Registers.Select(r => In(pc, r)).ToArray()));
            if (effect.Returns)
                outputs.Add(Define($"return_{pc:x}", "return", 0, layout.Return.Indirect ? [] : layout.Return.Pieces.Select(p =>
                    Slice(In(pc, ((RegisterLocation)p.Location).Name), ((RegisterLocation)p.Location).BitOffset, p.Size * 8)).ToArray()));
            instructions.Add(new(pc, outputs.Distinct().ToArray(), condition, call));
        }
        FillInputs();
        SimplifyPhis();
        return new(flow, values.Values.OrderBy(v => v.Id).ToArray(), instructions.ToArray(), problems.Distinct().ToArray());
    }
    private string Define(string id, string operation, int width, string[] arguments, string? type = null, long immediate = 0, SsaInput[]? incoming = null, ulong address = 0, string? register = null)
    {
        var previous = values.GetValueOrDefault(id);
        values[id] = new(id, operation, width, arguments, type, immediate, incoming, address == 0 ? previous?.Address ?? 0 : address, register ?? previous?.Register);
        return id;
    }
    private static string Canonical(string register) => Arm64Registers.Canonical(register);
    private static int Width(string register) => Arm64Registers.Width(register);
    private string Constant(long number, int width = 64) => Define($"constant_{width}_{number:x}", "constant", width, [], immediate: number);
    private string Slice(string value, int offset, int width) => offset == 0 && values[value].Width == width ? value :
        Define($"slice_{value}_{offset}_{width}", "slice", width, [value], immediate: offset);
    private string Extend(string value, int width, bool signed, bool undefined = false)
    {
        if (values[value].Width == width) return value;
        if (values[value].Width > width) return Slice(value, 0, width);
        return Define($"extend_{value}_{width}_{signed}_{undefined}", undefined ? "abi-extend" : signed ? "sign-extend" : "zero-extend", width, [value]);
    }
    private string In(ulong pc, string register)
    {
        register = Canonical(register);
        if (inputs.TryGetValue((pc, register), out var existing)) return existing;
        var id = $"in_{pc:x}_{register}";
        inputs[(pc, register)] = id;
        Define(id, "phi", Width(register), [], address: pc, register: register);
        pendingInputs.Enqueue((pc, register));
        return id;
    }
    // 前驱值按需填充；长指令链和回边都只引用已分配的身份，不递归遍历控制流。
    private void FillInputs()
    {
        while (pendingInputs.TryDequeue(out var item))
        {
            var (pc, register) = item;
            var incoming = new List<SsaInput>();
            if (pc == flow.Entry)
            {
                var seed = entry.GetValueOrDefault(register) ?? Define($"entry_{register}", "unknown", Width(register), []);
                incoming.Add(new(0, "entry", seed));
            }
            foreach (var edge in predecessors.GetValueOrDefault(pc, []))
            {
                if (!nodes.TryGetValue(edge.Source, out var source) || !source.Reachable) continue;
                incoming.Add(new(edge.Source, edge.Kind, edge.Kind.StartsWith("exception-") ? ExceptionValue(edge.Source, register) : Out(edge.Source, register)));
            }
            Define(inputs[item], incoming.Count == 0 ? "unknown" : "phi", Width(register), [], incoming: incoming.Count == 0 ? null : incoming.ToArray());
        }
    }
    private string ExceptionValue(ulong pc, string register)
    {
        if (register == "x0") return Define($"exception_{pc:x}", "exception-object", 64, [Call(pc)], "unwind-object*");
        if (register == "x1") return Define($"selector_{pc:x}", "exception-selector", 64, [Call(pc)], "intptr_t");
        if (register == "memory") return Define($"exception_memory_{pc:x}", "exception-memory", 0, [In(pc, "memory"), Call(pc)]);
        if (Arm64Registers.PreservedByCall(register) is > 0 and < 128 && Width(register) == 128)
            return Define($"exception_{pc:x}_{register}", "partial-clobber", 128, [In(pc, register), Call(pc)], immediate: 64, address: pc, register: register);
        return IsClobbered(register) ? Define($"exception_{pc:x}_{register}", "clobber", Width(register), [Call(pc)], address: pc, register: register) : In(pc, register);
    }
    private static bool IsClobbered(string register) => Arm64Registers.PreservedByCall(register) < Width(register);
    private string Value(ulong pc, MachineValue value)
    {
        if (value.Operation == "read") return In(pc, value.Register!);
        if (value.Operation == "constant") return Constant(value.Immediate, value.Width);
        var arguments = value.Inputs.Select(v => Value(pc, v)).ToArray();
        if (value.Operation == "slice") return Slice(arguments[0], checked((int)value.Immediate), value.Width);
        if (value.Operation is "zero-extend" or "sign-extend") return Extend(arguments[0], value.Width, value.Operation == "sign-extend");
        if (value.Operation == "reinterpret") return arguments[0];
        if (value.Operation == "address") return value.Immediate == 0 ? arguments[0] :
            Define(value.Id!, "add", 64, [arguments[0], Constant(value.Immediate)]);
        if (value.Operation == "load") return Define(value.Id!, "load", value.Width, [In(pc, "memory"), arguments[0]], address: pc);
        return Define(value.Id ?? $"machine_{pc:x}_{value.Operation}_{value.Width}_{value.Immediate}_{string.Join('_', arguments)}", value.Operation, value.Width, arguments,
            value.Type, value.Immediate, address: pc);
    }
    private string Call(ulong pc)
    {
        var id = $"call_{pc:x}";
        if (values.ContainsKey(id)) return id;
        Define(id, "call", 0, [], address: pc);
        var targetValue = effects[pc].Call?.Target ?? effects[pc].Branch!;
        var method = targetValue.Operation == "constant" ? symbols.Unique(unchecked((ulong)targetValue.Immediate)) : null;
        var layout = method is null ? null : abi.Classify(method);
        var target = Value(pc, targetValue);
        // 未知调用也保留调用前寄存器，不能使用调用后的返回寄存器补参数。
        var registers = Arm64Registers.CallInputs.Select(r => In(pc, r)).ToArray();
        return Define(id, "call", layout is null ? 0 : layout.Return.Shape.Size * 8, [target, In(pc, "memory"), .. registers], method?.ReturnType);
    }
    private string Out(ulong pc, string register)
    {
        register = Canonical(register);
        if (outputs.TryGetValue((pc, register), out var existing)) return existing;
        var effect = effects[pc];
        if (!effect.Writes.Contains(register)) return In(pc, register);
        var id = $"out_{pc:x}_{register}";
        outputs[(pc, register)] = id;
        Define(id, "pending", Width(register), [], address: pc, register: register);
        if (effect.Call is { } invocation)
        {
            var call = Call(pc);
            if (register == "memory") return Define(id, "call-memory", 0, [In(pc, "memory"), call]);
            var candidate = invocation.Target.Operation == "constant" ? symbols.Unique(unchecked((ulong)invocation.Target.Immediate)) : null;
            var layout = candidate is null ? null : abi.Classify(candidate);
            var piece = layout?.Return.Indirect == false ? layout.Return.Pieces.FirstOrDefault(p => p.Location is RegisterLocation r && r.Name.Equals(register, StringComparison.OrdinalIgnoreCase)) : null;
            if (piece is not null) return Define(id, "alias", Width(register), [Extend(Slice(call, piece.ValueOffset * 8, piece.Size * 8), Width(register), false, true)]);
            var preserved = Arm64Registers.PreservedByCall(register);
            return preserved > 0 ? Define(id, "partial-clobber", Width(register), [In(pc, register), call], immediate: preserved) :
                Define(id, "clobber", Width(register), [call]);
        }
        if (register == "memory" && effect.Stores.Length > 0)
        {
            var memory = In(pc, "memory");
            foreach (var store in effect.Stores)
                memory = Define(store.Id, "store", 0, [memory, Value(pc, store.Address), Value(pc, store.Value)], address: pc);
            return Define(id, "alias", 0, [memory]);
        }
        var assignment = effect.Assignments.Single(w => w.Register == register);
        var value = assignment.Value;
        // 保持标志定义在寄存器输出节点上，便于追踪条件的来源。
        if (value.Operation == "unknown") return Define(id, "unknown", Width(register), []);
        if (register == "nzcv") return Define(id, value.Operation, 4, value.Inputs.Select(v => Value(pc, v)).ToArray());
        return Define(id, "alias", Width(register), [Value(pc, value)]);
    }
    private void SimplifyPhis()
    {
        string Resolve(string id)
        {
            var visited = new HashSet<string>();
            while (values[id] is { Operation: "alias", Inputs: [var next] } && visited.Add(id)) id = next;
            return id;
        }
        bool changed;
        do
        {
            changed = false;
            foreach (var phi in values.Values.Where(v => v.Operation == "phi").ToArray())
            {
                var incoming = phi.Incoming!.Select(i => Resolve(i.Value)).Where(id => id != phi.Id).Distinct().ToArray();
                if (incoming.Length == 1) { Define(phi.Id, "alias", phi.Width, incoming); changed = true; }
            }
        } while (changed);
    }
}
