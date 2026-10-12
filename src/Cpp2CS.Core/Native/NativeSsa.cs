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
    private readonly Dictionary<string, SsaValue> values = [];
    private readonly Dictionary<(ulong, string), string> inputs = [];
    private readonly Dictionary<(ulong, string), string> outputs = [];
    private readonly Dictionary<ulong, NativeFlowNode> nodes = flow.Nodes.ToDictionary(n => n.Instruction.Address);
    private readonly Dictionary<ulong, NativeEdge[]> predecessors = flow.Nodes.SelectMany(n => n.Edges)
        .Where(e => e.Target.HasValue && e.Kind != "tail-call").GroupBy(e => e.Target!.Value).ToDictionary(g => g.Key, g => g.ToArray());
    private readonly Dictionary<string, string> entry = [];
    private readonly List<string> problems = [];

    public NativeSsaProgram Build()
    {
        method = abi.Normalize(method);
        var layout = abi.Classify(method);
        if (layout is null) throw new InvalidDataException("SSA 入口 ABI 未确认");
        entry["sp"] = Define("entry_sp", "stack-address", 64, [], "stack-address");
        entry["memory"] = Define("entry_memory", "memory", 0, []);
        for (var index = 0; index < method.Parameters.Length; index++)
        {
            var argument = layout.Arguments[index];
            var parameter = method.Parameters[index];
            var root = Define($"arg_{index}", "parameter", argument.Indirect ? 64 : argument.Shape.Size * 8, [], parameter.Type, index);
            foreach (var piece in argument.Pieces)
            {
                if (piece.Location is not RegisterLocation register)
                { problems.Add("SSA 入口栈参数未接通"); continue; }
                entry[register.Name.ToLowerInvariant()] = Extend(Slice(root, piece.ValueOffset * 8, piece.Size * 8), register.Name.StartsWith('V') ? 128 : 64, false, true);
            }
        }
        var instructions = new List<SsaInstruction>();
        foreach (var node in flow.Nodes.Where(n => n.Reachable))
        {
            var instruction = node.Instruction;
            var pc = instruction.Address;
            var effects = new List<string>();
            foreach (var register in Writes(instruction)) effects.Add(Out(pc, register));
            string? condition = null;
            if (NativeGraph.IsConditional(instruction))
            {
                var operands = instruction.Operands;
                if (instruction.Mnemonic is "cbz" or "cbnz") condition = Define($"condition_{pc:x}", instruction.Mnemonic == "cbz" ? "zero" : "nonzero", 1, [Operand(pc, operands[0])]);
                else if (instruction.Mnemonic is "tbz" or "tbnz")
                    condition = Define($"condition_{pc:x}", instruction.Mnemonic == "tbz" ? "zero" : "nonzero", 1,
                        [Slice(Operand(pc, operands[0]), checked((int)operands[1].Immediate), 1)]);
                else condition = Define($"condition_{pc:x}", instruction.Mnemonic, 1, [In(pc, "nzcv")]);
            }
            var call = instruction.Mnemonic is "bl" or "blr" ? Call(pc) : null;
            if (instruction.Mnemonic == "ret") effects.Add(Define($"return_{pc:x}", "return", 0, method.ReturnType == "void" ? [] : [In(pc, "x0"), In(pc, "x1")]));
            instructions.Add(new(pc, effects.Distinct().ToArray(), condition, call));
        }
        SimplifyPhis();
        return new(flow, values.Values.OrderBy(v => v.Id).ToArray(), instructions.ToArray(), problems.Distinct().ToArray());
    }
    private string Define(string id, string operation, int width, string[] arguments, string? type = null, long immediate = 0, SsaInput[]? incoming = null, ulong address = 0, string? register = null)
    {
        var previous = values.GetValueOrDefault(id);
        values[id] = new(id, operation, width, arguments, type, immediate, incoming, address == 0 ? previous?.Address ?? 0 : address, register ?? previous?.Register);
        return id;
    }
    private static string Canonical(string register) => register switch
    {
        "fp" => "x29", "lr" => "x30", "sp" or "wsp" => "sp", _ when register[0] == 'w' => "x" + register[1..],
        _ when register[0] is 's' or 'd' or 'q' && int.TryParse(register.AsSpan(1), out _) => "v" + register[1..], _ => register
    };
    private static int Width(string register) => register is "memory" ? 0 : register is "nzcv" ? 4 : register is "sp" ? 64 : register[0] is 'w' or 's' ? 32 : register[0] is 'v' or 'q' ? 128 : 64;
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
        if (incoming.Count == 0) return Define(id, "unknown", Width(register), []);
        return Define(id, "phi", Width(register), [], incoming: incoming.ToArray());
    }
    private string ExceptionValue(ulong pc, string register)
    {
        if (register == "x0") return Define($"exception_{pc:x}", "exception-object", 64, [Call(pc)], "unwind-object*");
        if (register == "x1") return Define($"selector_{pc:x}", "exception-selector", 64, [Call(pc)], "intptr_t");
        if (register == "memory") return Define($"exception_memory_{pc:x}", "exception-memory", 0, [In(pc, "memory"), Call(pc)]);
        if (register.StartsWith('v') && int.Parse(register.AsSpan(1)) is >= 8 and <= 15)
            return Define($"exception_{pc:x}_{register}", "partial-clobber", 128, [In(pc, register), Call(pc)], immediate: 64, address: pc, register: register);
        return IsClobbered(register) ? Define($"exception_{pc:x}_{register}", "clobber", Width(register), [Call(pc)], address: pc, register: register) : In(pc, register);
    }
    private static bool IsClobbered(string register) => register == "nzcv" || register == "x30" ||
        register.StartsWith('x') && int.TryParse(register.AsSpan(1), out var x) && x <= 18 || register.StartsWith('v');
    private static IEnumerable<string> Writes(Instruction i)
    {
        if (i.Mnemonic is "bl" or "blr") return Enumerable.Range(0, 19).Append(30).Select(n => $"x{n}")
            .Concat(Enumerable.Range(0, 32).Select(n => $"v{n}")).Concat(["nzcv", "memory"]);
        if (i.Mnemonic is "cmp" or "cmn") return ["nzcv"];
        if (i.Mnemonic.StartsWith("st")) return i.Writeback ? ["memory", Canonical(i.Operands.First(o => o.Kind == 3).Base!)] : ["memory"];
        if (i.Mnemonic is "ret" or "nop" or "b" or "br" || NativeGraph.IsConditional(i)) return [];
        var result = new List<string> { Canonical(i.Operands[0].Register!) };
        if (i.Mnemonic == "ldp") result.Add(Canonical(i.Operands[1].Register!));
        if (i.Mnemonic == "subs") result.Add("nzcv");
        if (i.Writeback) result.Add(Canonical(i.Operands.First(o => o.Kind == 3).Base!));
        return result;
    }
    private string Operand(ulong pc, Operand operand)
    {
        if (operand.Kind == 2) return Constant(operand.Immediate);
        if (operand.Kind != 1) throw new InvalidDataException("SSA 需要寄存器或立即数操作数");
        var register = operand.Register!;
        var value = register is "xzr" or "wzr" ? Constant(0, Width(register)) : Slice(In(pc, register), 0, Width(register));
        if (operand.Extend != 0)
        {
            var width = operand.Extend switch { 1 or 5 => 8, 2 or 6 => 16, 3 or 7 => 32, 4 or 8 => 64, _ => 0 };
            if (width == 0) throw new InvalidDataException("未知 ARM64 扩展操作");
            value = Extend(Slice(value, 0, width), 64, operand.Extend >= 5);
        }
        if (operand.Shift != 0)
        {
            if (operand.ShiftKind is not (0 or 1)) problems.Add($"0x{pc:x}: 尚未支持的移位类别 {operand.ShiftKind}");
            value = Define($"shift_{pc:x}_{register}_{operand.Shift}", "shift-left", values[value].Width, [value], immediate: operand.Shift);
        }
        return value;
    }
    private string Address(Instruction instruction, Operand memory, int displacement = 0)
    {
        var value = In(instruction.Address, memory.Base!);
        if (memory.Index is not null)
        {
            var index = Operand(instruction.Address, memory with { Kind = 1, Register = memory.Index });
            value = Define($"index_{instruction.Address:x}", "add", 64, [value, index]);
        }
        var offset = displacement + (instruction.PostIndex ? 0 : memory.Displacement);
        return offset == 0 ? value : Define($"address_{instruction.Address:x}_{offset}", "add", 64, [value, Constant(offset)]);
    }
    private string Call(ulong pc)
    {
        var id = $"call_{pc:x}";
        if (values.ContainsKey(id)) return id;
        Define(id, "call", 0, [], address: pc);
        var instruction = nodes[pc].Instruction;
        var method = instruction.Mnemonic == "bl" ? symbols.Unique(NativeGraph.Target(instruction)) : null;
        var layout = method is null ? null : abi.Classify(method);
        var target = instruction.Mnemonic == "bl" ? Constant((long)NativeGraph.Target(instruction)) : Operand(pc, instruction.Operands[0]);
        // 未知调用也保留调用前寄存器，不能使用调用后的返回寄存器补参数。
        var registers = Enumerable.Range(0, 9).Select(n => In(pc, $"x{n}"))
            .Concat(Enumerable.Range(0, 8).Select(n => In(pc, $"v{n}"))).ToArray();
        return Define(id, "call", layout is null ? 0 : layout.Return.Shape.Size * 8, [target, In(pc, "memory"), .. registers, In(pc, "sp")], method?.ReturnType);
    }
    private string Out(ulong pc, string register)
    {
        register = Canonical(register);
        if (outputs.TryGetValue((pc, register), out var existing)) return existing;
        var instruction = nodes[pc].Instruction;
        if (!Writes(instruction).Contains(register)) return In(pc, register);
        var id = $"out_{pc:x}_{register}";
        outputs[(pc, register)] = id;
        Define(id, "pending", Width(register), [], address: pc, register: register);
        var op = instruction.Mnemonic;
        var operands = instruction.Operands;
        if (op is "bl" or "blr")
        {
            var call = Call(pc);
            if (register == "memory") return Define(id, "call-memory", 0, [In(pc, "memory"), call]);
            var candidate = op == "bl" ? symbols.Unique(NativeGraph.Target(instruction)) : null;
            var layout = candidate is null ? null : abi.Classify(candidate);
            var piece = layout?.Return.Indirect == false ? layout.Return.Pieces.FirstOrDefault(p => p.Location is RegisterLocation r && r.Name.Equals(register, StringComparison.OrdinalIgnoreCase)) : null;
            if (piece is not null) return Define(id, "alias", Width(register), [Extend(Slice(call, piece.ValueOffset * 8, piece.Size * 8), Width(register), false, true)]);
            if (register.StartsWith('v') && int.Parse(register.AsSpan(1)) is >= 8 and <= 15)
                return Define(id, "partial-clobber", 128, [In(pc, register), call], immediate: 64);
            Define(id, "clobber", Width(register), [call]);
            values[id] = values[id] with { Address = pc, Register = register };
            return id;
        }
        if (op.StartsWith("st") || op.StartsWith("ld"))
        {
            var pair = op is "stp" or "ldp";
            var memory = operands[pair ? 2 : 1];
            if (instruction.Writeback && register == Canonical(memory.Base!))
                return Define(id, "add", 64, [In(pc, memory.Base!), Constant(instruction.PostIndex ? operands[^1].Immediate : memory.Displacement)]);
            var size = op.EndsWith('b') ? 8 : op.EndsWith('h') ? 16 : op == "ldrsw" ? 32 : Width(operands[0].Register!);
            if (op.StartsWith("st"))
            {
                var before = In(pc, "memory");
                for (var n = 0; n < (pair ? 2 : 1); n++) before = Define($"store_{pc:x}_{n}", "store", 0,
                    [before, Address(instruction, memory, n * size / 8), Slice(Operand(pc, operands[n]), 0, size)], address: pc);
                return Define(id, "alias", 0, [before]);
            }
            var index = pair && register == Canonical(operands[1].Register!) ? 1 : 0;
            var load = Define($"load_{pc:x}_{index}", "load", size, [In(pc, "memory"), Address(instruction, memory, index * size / 8)], address: pc);
            return Define(id, "alias", Width(register), [Extend(load, Width(register), op == "ldrsw")]);
        }
        if ((op is "cmp" or "cmn" or "subs") && register == "nzcv")
        {
            var start = op == "subs" ? 1 : 0;
            var left = Operand(pc, operands[start]); var right = Operand(pc, operands[start + 1]);
            return Define(id, op == "cmn" ? "compare-add" : "compare", 4, [left, Slice(right, 0, values[left].Width)]);
        }
        string value;
        if (op is "adr" or "adrp") value = Constant(operands[1].Immediate);
        else if (op == "movi" && operands[1].Kind == 2 && operands[1].Immediate == 0) value = Constant(0, Width(operands[0].Register!));
        else if (op == "mov") value = Operand(pc, operands[1]);
        else if (op == "fmov" && operands.Length == 2 && operands[0].Register?[0] is 's' or 'd' && operands[1].FloatingPoint is { } number)
            value = Constant(operands[0].Register![0] == 's' ? BitConverter.SingleToInt32Bits((float)number) : BitConverter.DoubleToInt64Bits(number), Width(operands[0].Register!));
        else if (op == "fmov" && operands.Length == 2 && operands.All(o => o.Kind == 1 && o.Register?[0] is 's' or 'd' or 'w' or 'x') && Width(operands[0].Register!) == Width(operands[1].Register!))
            value = Operand(pc, operands[1]);
        else if (op == "cset" && instruction.ConditionCode is >= 1 and <= 14) value = Define($"value_{pc:x}", "condition-value", Width(operands[0].Register!), [In(pc, "nzcv")], immediate: instruction.ConditionCode, address: pc);
        else if (op is "add" or "sub" or "subs" or "orr" or "and") value = Define($"value_{pc:x}", op is "subs" ? "sub" : op, Width(operands[0].Register!), [Operand(pc, operands[1]), Operand(pc, operands[2])], address: pc);
        else { problems.Add($"0x{pc:x}: SSA 不支持 {op}"); return Define(id, "unknown", Width(register), []); }
        if (operands[0].Register!.StartsWith('w')) value = Extend(Slice(value, 0, 32), 64, false);
        return Define(id, "alias", Width(register), [Extend(value, Width(register), false)]);
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
