using Cpp2CS.Abi;

namespace Cpp2CS.Native;

// 所有 read 都引用指令执行前的状态；写回在访存之后提交。
public sealed record MachineValue(string Operation, int Width, MachineValue[] Inputs,
    long Immediate = 0, string? Register = null, string? Id = null, string? Type = null);
public sealed record MachineWrite(string Register, MachineValue Value);
public sealed record MachineStore(MachineValue Address, MachineValue Value, string Id);
public sealed record MachineCall(MachineValue Target);
public sealed record MachineEffects(Instruction Source, MachineWrite[] Assignments, MachineStore[] Stores,
    MachineValue? Condition, MachineCall? Call, bool Returns, MachineValue? Branch, string? Unsupported)
{
    public IEnumerable<string> Writes => Assignments.Select(w => w.Register)
        .Concat(Stores.Length == 0 ? [] : new[] { "memory" })
        .Concat(Call is null ? [] : Arm64Registers.CallWrites).Distinct();
    public IEnumerable<string> Reads => Assignments.Select(w => w.Value).Concat(Stores.SelectMany(s => new[] { s.Address, s.Value }))
        .Concat(Condition is null ? [] : new[] { Condition }).Concat(Branch is null ? [] : new[] { Branch })
        .Concat(Call is null ? [] : new[] { Call.Target }).SelectMany(ReadRegisters).Distinct();
    private static IEnumerable<string> ReadRegisters(MachineValue value) =>
        (value.Operation == "read" ? new[] { value.Register! } : value.Operation == "load" ? new[] { "memory" } : [])
        .Concat(value.Inputs.SelectMany(ReadRegisters));
}

// ARM64 操作数、位宽、标志和地址写回只在这一层解释。
public static class Arm64Effects
{
    public static MachineEffects Lower(Instruction instruction)
    {
        var pc = instruction.Address;
        var o = instruction.Operands;
        var op = instruction.Mnemonic;
        var writes = new List<MachineWrite>();
        var stores = new List<MachineStore>();
        MachineValue? condition = null, branch = null;
        MachineCall? call = null;
        var returns = false;
        string? unsupported = null;
        MachineValue Node(string operation, int width, MachineValue[] inputs, long immediate = 0, string? id = null, string? type = null) =>
            new(operation, width, inputs, immediate, Id: id, Type: type);
        MachineValue Read(string register) => Arm64Registers.Zero(register) ? Constant(0, Arm64Registers.Width(register)) :
            Resize(new("read", Arm64Registers.Width(Arm64Registers.Canonical(register)), [], Register: Arm64Registers.Canonical(register)),
                Arm64Registers.Width(register));
        MachineValue Operand(Operand operand)
        {
            if (operand.Kind == 2) return Constant(operand.Immediate);
            if (operand.Kind != 1) { unsupported = "操作数类别未支持"; return Node("unknown", 64, []); }
            var value = Read(operand.Register!);
            if (operand.Extend != 0)
            {
                var width = operand.Extend switch { 1 or 5 => 8, 2 or 6 => 16, 3 or 7 => 32, 4 or 8 => 64, _ => 0 };
                if (width == 0) { unsupported = "扩展类别未支持"; return Node("unknown", 64, []); }
                value = Resize(Slice(value, 0, width), 64, operand.Extend >= 5);
            }
            if (operand.Shift != 0)
            {
                var shift = operand.ShiftKind switch { 0 or 1 => "shift-left", 3 => "shift-right", 4 => "shift-arithmetic", 5 => "rotate-right", _ => null };
                if (shift is null) { unsupported = "移位类别未支持"; return Node("unknown", value.Width, []); }
                value = Node(shift, value.Width, [value], operand.Shift, $"shift_{pc:x}_{operand.Register}_{operand.Shift}");
            }
            return value;
        }
        void Write(string register, MachineValue value)
        {
            if (Arm64Registers.Zero(register)) return;
            var width = Arm64Registers.Width(register);
            // W 写入清零 X 高位；标量 S/D 指令清零 V 的剩余位。
            writes.Add(new(Arm64Registers.Canonical(register), Resize(Resize(value, width), Arm64Registers.Width(Arm64Registers.Canonical(register)))));
        }
        MachineValue Flags() => Read("nzcv");
        MachineValue Condition(int code, string id) => Node("condition-value", 1, [Flags()], code, id);
        MachineValue Address(Operand memory, int extra = 0)
        {
            var value = Read(memory.Base!);
            if (memory.Index is not null)
                value = Node("add", 64, [value, Operand(memory with { Kind = 1, Register = memory.Index })], id: $"index_{pc:x}");
            var offset = extra + (instruction.PostIndex ? 0 : memory.Displacement);
            // 保留基址与位移，投影层不用反解 ARM64 寻址模式。
            return Node("address", 64, [value], offset, $"address_{pc:x}_{offset}");
        }
        switch (op)
        {
            case "nop": break;
            case "adr": case "adrp": Write(o[0].Register!, Constant(o[1].Immediate) with { Type = "address" }); break;
            case "mov": Write(o[0].Register!, Operand(o[1])); break;
            case "movi" when (o[1] is { Kind: 2, Immediate: 0 }): Write(o[0].Register!, Constant(0, Arm64Registers.Width(o[0].Register!))); break;
            case "add": case "sub": case "subs": case "adds": case "orr": case "and": case "eor":
            {
                var width = Arm64Registers.Width(o[0].Register!);
                var left = Resize(Operand(o[1]), width); var right = Resize(Operand(o[2]), width);
                Write(o[0].Register!, Node(op is "subs" ? "sub" : op is "adds" ? "add" : op, width, [left, right], id: $"value_{pc:x}"));
                if (op is "subs" or "adds") Write("nzcv", Node(op == "subs" ? "compare" : "compare-add", 4, [left, right]));
                break;
            }
            case "lsl": case "lsr": case "asr":
            {
                var width = Arm64Registers.Width(o[0].Register!);
                if (o[2].Kind != 2 || o[2].Immediate < 0 || o[2].Immediate >= width) { unsupported = "移位位数未支持"; break; }
                Write(o[0].Register!, Node(op == "lsl" ? "shift-left" : op == "lsr" ? "shift-right" : "shift-arithmetic", width,
                    [Resize(Operand(o[1]), width)], o[2].Immediate, $"value_{pc:x}")); break;
            }
            case "neg": case "negs":
            {
                var width = Arm64Registers.Width(o[0].Register!);
                if (o.Length != 2 || width is not (32 or 64) || o.Any(p => p.Kind != 1 || p.Register?[0] is not ('w' or 'x') || Arm64Registers.Width(p.Register!) != width))
                { unsupported = "取负操作数不是同宽整数寄存器"; break; }
                var zero = Constant(0, width); var source = Operand(o[1]);
                Write(o[0].Register!, Node("sub", width, [zero, source], id: $"value_{pc:x}"));
                if (op == "negs") Write("nzcv", Node("compare", 4, [zero, source]));
                break;
            }
            case "sxtb": case "sxth": case "sxtw": case "uxtb": case "uxth": case "uxtw":
            {
                var width = Arm64Registers.Width(o[0].Register!);
                var part = op[^1] == 'b' ? 8 : op[^1] == 'h' ? 16 : 32;
                if (o.Length != 2 || width is not (32 or 64) || o[0].Register?[0] is not ('w' or 'x') ||
                    o[1].Kind != 1 || o[1].Register?[0] != 'w')
                { unsupported = "整数扩展操作数未支持"; break; }
                Write(o[0].Register!, Resize(Slice(Operand(o[1]), 0, part), width, op[0] == 's'));
                break;
            }
            case "ubfx": case "sbfx": case "ubfiz": case "sbfiz": case "bfi": case "bfxil": case "bfc":
            case "ubfm": case "sbfm": case "bfm":
            {
                var width = Arm64Registers.Width(o[0].Register!);
                var clear = op == "bfc";
                if (width is not (32 or 64) || o.Length != (clear ? 3 : 4) || o[0].Register?[0] is not ('w' or 'x') ||
                    !clear && (o[1].Kind != 1 || o[1].Register?[0] is not ('w' or 'x') || Arm64Registers.Width(o[1].Register!) != width) ||
                    o[^2].Kind != 2 || o[^1].Kind != 2)
                { unsupported = "位域操作数未支持"; break; }
                var kind = op;
                var lsb = o[^2].Immediate; var count = o[^1].Immediate;
                if (op is "ubfm" or "sbfm" or "bfm")
                {
                    if (lsb < 0 || lsb >= width || count < 0 || count >= width) { unsupported = "位域编码超出寄存器范围"; break; }
                    var wraps = lsb > count;
                    kind = op == "ubfm" ? wraps ? "ubfiz" : "ubfx" : op == "sbfm" ? wraps ? "sbfiz" : "sbfx" : wraps ? "bfi" : "bfxil";
                    (lsb, count) = wraps ? (width - lsb, count + 1) : (lsb, count - lsb + 1);
                }
                if (lsb < 0 || lsb >= width || count <= 0 || count > width - lsb) { unsupported = "位域范围未支持"; break; }
                var insert = kind is "ubfiz" or "sbfiz" or "bfi" or "bfc";
                var source = clear ? Constant(0, width) : Operand(o[1]);
                var field = Resize(Slice(source, insert ? 0 : (int)lsb, (int)count), width, kind is "sbfx" or "sbfiz");
                if (insert && lsb != 0) field = Node("shift-left", width, [field], lsb);
                if (kind is "bfi" or "bfxil" or "bfc")
                {
                    var mask = (ulong.MaxValue >> (64 - (int)count)) << (insert ? (int)lsb : 0);
                    var preserved = Node("and", width, [Read(o[0].Register!), Constant(unchecked((long)~mask), width)]);
                    field = Node("orr", width, [preserved, field]);
                }
                Write(o[0].Register!, field);
                break;
            }
            case "mul": case "mneg": case "madd": case "msub":
            {
                var width = Arm64Registers.Width(o[0].Register!);
                if (o.Length != (op is "mul" or "mneg" ? 3 : 4) ||
                    o.Any(p => p.Kind != 1 || p.Register?[0] is not ('w' or 'x') || Arm64Registers.Width(p.Register!) != width))
                { unsupported = "乘法操作数不是同宽整数寄存器"; break; }
                var product = Node("multiply", width, [Operand(o[1]), Operand(o[2])], id: $"product_{pc:x}");
                Write(o[0].Register!, op == "mul" ? product : Node(op == "madd" ? "add" : "sub", width,
                    [op == "mneg" ? Constant(0, width) : Operand(o[3]), product], id: $"value_{pc:x}"));
                break;
            }
            case "cmp": case "cmn": case "tst": case "fcmp":
            {
                var left = Operand(o[0]);
                var right = op == "fcmp" && o[1].FloatingPoint is 0 ? Constant(0, left.Width) : Resize(Operand(o[1]), left.Width);
                Write("nzcv", Node(op switch { "cmn" => "compare-add", "tst" => "compare-and", "fcmp" => "compare-float", _ => "compare" }, 4, [left, right])); break;
            }
            case "cset" when (instruction.ConditionCode is >= 1 and <= 14):
                Write(o[0].Register!, Node("condition-value", Arm64Registers.Width(o[0].Register!), [Flags()], instruction.ConditionCode, $"value_{pc:x}")); break;
            case "csel" when (instruction.ConditionCode is >= 1 and <= 14):
                Write(o[0].Register!, Node("select", Arm64Registers.Width(o[0].Register!),
                    [Condition(instruction.ConditionCode, $"select_condition_{pc:x}"), Operand(o[1]), Operand(o[2])], id: $"value_{pc:x}")); break;
            case "scvtf" when (o.Length == 2 && o[0].Register?[0] is 's' or 'd' && o[1].Register?[0] is 'w' or 'x'):
                Write(o[0].Register!, Node("signed-to-float", Arm64Registers.Width(o[0].Register!), [Operand(o[1])], id: $"value_{pc:x}", type: o[0].Register![0] == 's' ? "float" : "double")); break;
            case "fdiv" when (o.Length == 3 && o[0].Register?[0] is 's' or 'd' && o.Skip(1).All(p => p.Register?[0] == o[0].Register![0])):
                Write(o[0].Register!, Node("float-divide", Arm64Registers.Width(o[0].Register!), [Operand(o[1]), Operand(o[2])], id: $"value_{pc:x}", type: o[0].Register![0] == 's' ? "float" : "double")); break;
            case "frintp" when (o.Length == 2 && o[0].Register?[0] is 's' or 'd' && o[1].Register?[0] == o[0].Register![0]):
                Write(o[0].Register!, Node("float-ceiling", Arm64Registers.Width(o[0].Register!), [Operand(o[1])], id: $"value_{pc:x}", type: o[0].Register![0] == 's' ? "float" : "double")); break;
            case "fcvtps" when (o.Length == 2 && o[0].Register?[0] is 'w' or 'x' && o[1].Register?[0] is 's' or 'd'):
                Write(o[0].Register!, Node("float-to-signed-ceiling", Arm64Registers.Width(o[0].Register!), [Operand(o[1])], id: $"value_{pc:x}", type: o[0].Register![0] == 'w' ? "int32_t" : "int64_t")); break;
            case "fmov" when (o.Length == 2 && o[0].Register?[0] is 's' or 'd' && o[1].FloatingPoint is { } number):
                Write(o[0].Register!, Constant(o[0].Register![0] == 's' ? BitConverter.SingleToInt32Bits((float)number) : BitConverter.DoubleToInt64Bits(number), Arm64Registers.Width(o[0].Register!)) with { Type = o[0].Register![0] == 's' ? "float" : "double" }); break;
            case "fmov" when (o.Length == 2 && o.All(p => p.Kind == 1 && p.Register?[0] is 's' or 'd' or 'w' or 'x') && Arm64Registers.Width(o[0].Register!) == Arm64Registers.Width(o[1].Register!)):
                Write(o[0].Register!, Node("reinterpret", Arm64Registers.Width(o[0].Register!), [Operand(o[1])], id: $"value_{pc:x}",
                    type: o[0].Register![0] switch { 's' => "float", 'd' => "double", 'w' => "int32_t", _ => "int64_t" })); break;
            case "stp": case "ldp": case "str": case "strb": case "strh": case "ldr": case "ldrb": case "ldrh":
            case "ldur": case "stur": case "ldrsw": case "ldurb": case "ldurh": case "sturb": case "sturh":
            {
                var pair = op is "stp" or "ldp";
                var memory = o[pair ? 2 : 1];
                if (memory.Kind != 3) { unsupported = "访存操作数未支持"; break; }
                var width = op.EndsWith('b') ? 8 : op.EndsWith('h') ? 16 : op == "ldrsw" ? 32 : Arm64Registers.Width(o[0].Register!);
                for (var n = 0; n < (pair ? 2 : 1); n++)
                {
                    var address = Address(memory, n * width / 8);
                    if (op.StartsWith("ld"))
                        Write(o[n].Register!, Resize(Node("load", width, [address], id: $"load_{pc:x}_{n}"), Arm64Registers.Width(o[n].Register!), op == "ldrsw"));
                    else stores.Add(new(address, Resize(Operand(o[n]), width), $"store_{pc:x}_{n}"));
                }
                if (instruction.Writeback)
                    Write(memory.Base!, Node("add", 64, [Read(memory.Base!), Constant(instruction.PostIndex ? o[^1].Immediate : memory.Displacement)], id: $"writeback_{pc:x}"));
                break;
            }
            case "cbz": case "cbnz":
                condition = Node(op == "cbz" ? "zero" : "nonzero", 1, [Operand(o[0])], id: $"condition_{pc:x}"); break;
            case "tbz": case "tbnz":
                condition = Node(op == "tbz" ? "zero" : "nonzero", 1, [Slice(Operand(o[0]), checked((int)o[1].Immediate), 1)], id: $"condition_{pc:x}"); break;
            case "bl": case "blr": call = new(Operand(o[0])); break;
            case "b": case "br": branch = Operand(o[0]); break;
            case "ret": returns = true; break;
            default:
                if (op.StartsWith("b.") && instruction.ConditionCode is >= 1 and <= 14)
                    condition = Node(op, 1, [Flags()], instruction.ConditionCode, $"condition_{pc:x}");
                else unsupported = "指令尚未支持：" + op;
                break;
        }
        if (unsupported is not null)
        {
            var affected = instruction.Writes.Select(Arm64Registers.Canonical).Concat(writes.Select(w => w.Register))
                .Where(r => !Arm64Registers.Zero(r)).Append("memory").Distinct().ToArray();
            writes.Clear(); stores.Clear(); condition = null; call = null;
            // 未知效果不能让旧值继续传播；保留解码器的写集合，内存也保守失效。
            foreach (var register in affected) writes.Add(new(register, Node("unknown", Arm64Registers.Width(register), [])));
        }
        return new(instruction, writes.ToArray(), stores.ToArray(), condition, call, returns, branch, unsupported);
    }
    public static MachineValue Constant(long value, int width = 64) => new("constant", width, [], value);
    public static MachineValue Slice(MachineValue value, int offset, int width) =>
        offset == 0 && value.Width == width ? value : new("slice", width, [value], offset);
    public static MachineValue Resize(MachineValue value, int width, bool signed = false) =>
        value.Width == width ? value : value.Width > width ? Slice(value, 0, width) : new(signed ? "sign-extend" : "zero-extend", width, [value]);
}
