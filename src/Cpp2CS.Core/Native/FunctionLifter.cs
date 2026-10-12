using Cpp2CS.Abi;
using Cpp2CS.IR;
using Cpp2CS.Model;

namespace Cpp2CS.Native;

public sealed partial class FunctionLifter(ElfImage image, Arm64Decoder decoder, Symbols symbols, HeaderLayout layouts, ManagedNames managed, RuntimeProfile runtime)
{
    private readonly Dictionary<(string Type, int Offset, int Width), string?> getters = [];
    private readonly RegionId stackRegion = new("frame", RegionKind.Stack);
    public LiftResult Lift(ulong address)
    {
        aggregateValues.Clear();
        mutableStack.Clear();
        aggregateLogicalTypes.Clear();
        var method = new NativeAbi(layouts, managed).Normalize(symbols.Unique(address) ?? throw new InvalidDataException("入口没有唯一符号签名"));
        var managedSignature = managed.SignatureOf(method.Name.Split("$$")[0], method.Name.Split("$$")[1]);
        var managedParameters = method.Parameters.Where(p => p.Name != "__this" && !(p.Name == "method" && p.Type.Contains("MethodInfo"))).ToArray();
        if (managedSignature is { } signature && signature.ParameterTypes.Length == managedParameters.Length)
            for (var p = 0; p < managedParameters.Length; p++)
                if (managedParameters[p].Type.EndsWith('*')) symbols.DisplayTypes.TryAdd(managedParameters[p].Type.TrimEnd('*'), signature.ParameterTypes[p]);
        foreach (var parameter in method.Parameters.Where(p => p.Type.EndsWith("_o*")))
        {
            var nativeType = parameter.Type.TrimEnd('*');
            var logicalType = symbols.Display(nativeType);
            while (layouts.ParentFields(nativeType) is { } parent && managed.BaseTypeOf(logicalType) is { } logicalParent)
            {
                nativeType = parent.EndsWith("_Fields") ? parent[..^7] + "_o" : parent;
                symbols.DisplayTypes.TryAdd(nativeType, logicalParent);
                logicalType = logicalParent;
            }
        }
        var boundary = UnwindBoundary.Read(image, address);
        var end = boundary.Start == address && boundary.End > address ? boundary.End : symbols.Ceiling(address);
        if (end <= address || end - address > 16384) throw new InvalidDataException("候选函数范围超出当前限制");
        var instructions = decoder.Decode(image.Read(address, (int)(end - address)), address);
        var graph = new NativeGraph(instructions, runtime.NoReturn, target => symbols.Unique(target) is not null || runtime.Helpers.ContainsKey(target));
        var result = new LiftResult(method, instructions, [], [.. graph.Problems], [], graph);
        var asyncStateMachine = managed.Implements(method.Name.Split("$$")[0], "System.Runtime.CompilerServices.IAsyncStateMachine");
        if (!asyncStateMachine && boundary.Unsupported is null && boundary.Lsda is not null && graph.Problems.Length == 0)
        {
            var nativeAbi = new NativeAbi(layouts, managed);
            var flow = NativeControlFlow.Build(instructions, boundary, runtime.NoReturn);
            var semantics = new SsaSemantics(new NativeSsa(flow, method, nativeAbi, symbols).Build(), method, symbols, layouts, nativeAbi, image, runtime, new(image, decoder));
            if (FinallyLoops.Recover(graph, semantics, nativeAbi, runtime, result.Problems.Add) is { } cleanup)
            {
                graph = new NativeGraph(instructions, runtime.NoReturn, target => symbols.Unique(target) is not null || runtime.Helpers.ContainsKey(target), [cleanup.Cleanup, cleanup.Continuation]);
                result = result with { Graph = graph, Finally = cleanup };
                result.Proofs.Add(new(address, "FinallyLoopProtocol", "SSA confirms identical IDisposable receiver and method on normal/exception exits; handler paths invoke cleanup once; no handler business stores or extra calls"));
            }
        }
        if (boundary.Unsupported is not null || boundary.Lsda is not null && result.Finally is null)
        {
            result.Problems.Add(boundary.Unsupported ?? (asyncStateMachine ? "async 异常区域需由 SSA 托管语义层证明" : "普通方法的异常清理区域尚未接通结构化输出（LSDA）"));
            return result;
        }
        if (boundary.Lsda is null) result.Proofs.Add(new(address, "UnwindBoundary", $"FDE 0x{boundary.Start:x}..0x{boundary.End:x}; zR CIE has no LSDA field; no local handler table in this FDE"));
        if (graph.Problems.Length > 0) return result;
        var order = graph.TopologicalOrder();
        var entry = new NativeState();
        var incoming = new Dictionary<ulong, List<(ulong Predecessor, NativeState State)>> { [address] = [(address, entry)] };
        var abi = Classify(method);
        if (abi is null) { result.Problems.Add("入口 ABI 尚不支持"); return result; }
        for (var p = 0; p < method.Parameters.Length; p++)
        {
            var parameter = method.Parameters[p];
            var value = new NativeValue(new InputBits($"arg:{p}", checked(layouts.Size(parameter.Type) * 8)), parameter.Type,
                new NameExpression(parameter.Name == "__this" ? "this" : parameter.Name));
            if (abi.Arguments[p].Shape.Kind is ShapeKind.Composite or ShapeKind.HomogeneousFloat)
            {
                aggregateValues[value.Bits] = (parameter.Type, value.Expression);
                value = value with { Expression = new AggregateExpression(parameter.Type, value.Expression) };
            }
            if (abi.Arguments[p].Indirect || abi.Arguments[p].Pieces.Any(piece => piece.Location is not RegisterLocation))
            { result.Problems.Add("入口间接/栈参数尚未接通"); return result; }
            foreach (var piece in abi.Arguments[p].Pieces)
                Set(entry, ((RegisterLocation)piece.Location).Name.ToLowerInvariant(), NativeValues.Slice(value, piece.ValueOffset * 8, piece.Size * 8));
        }
        if (order is null) return LiftLoops(result, entry);
        foreach (var blockAddress in order)
        {
            if (!incoming.TryGetValue(blockAddress, out var states)) continue;
            var state = Merge(blockAddress, states);
            var block = graph.Blocks[blockAddress];
            var lifted = new LiftedBlock(blockAddress, [], null, block.Successors);
            result.Blocks.Add(blockAddress, lifted);
            foreach (var instruction in block.Instructions)
            {
                var condition = Step(instruction, state, lifted.Statements, result);
                if (condition is not null) lifted = lifted with { Condition = condition };
            }
            result.Blocks[blockAddress] = lifted;
            foreach (var successor in block.Successors)
            {
                if (!incoming.TryGetValue(successor, out var list)) incoming[successor] = list = [];
                list.Add((blockAddress, state.Copy()));
            }
        }
        PhiLowering.Apply(result);
        SemanticValidation.Check(result);
        return result;
    }
    private static string Canonical(string name) => name switch { "fp" => "x29", "lr" => "x30", _ when name.StartsWith('w') => "x" + name[1..],
        _ when name[0] is 'q' or 'd' or 's' => "v" + name[1..], _ => name };
    private static int RegisterWidth(string name) => name.StartsWith('w') || name.StartsWith('s') ? 32 : name.StartsWith('q') || name.StartsWith('v') ? 128 : 64;
    private NativeValue Read(NativeState state, string name)
    {
        if (name is "xzr" or "wzr") return Constant(0, RegisterWidth(name));
        if (name == "sp") return new(new InputBits($"stack-address:{state.StackOffset}", 64), "stack-address", new StackAddressExpression(state.StackOffset));
        var key = Canonical(name);
        var value = state.Registers.GetValueOrDefault(key) ?? new(new UnknownBits(key, "寄存器没有到达定义", RegisterWidth(key)), "unknown", new UnknownExpression(key));
        value = RegisterWidth(name) < value.Bits.Width ? NativeValues.Slice(value, 0, RegisterWidth(name), value.Type) : value;
        if (value.Expression is SliceExpression { Value: AggregateExpression aggregate } slice && slice.BitOffset % 8 == 0 && slice.BitWidth % 8 == 0 &&
            layouts.Field(aggregate.Type, slice.BitOffset / 8, slice.BitWidth / 8) is { } field)
            value = value with { Type = field.Type, Expression = new MemberExpression(aggregate.Bits, field, field.Name, null) };
        return Project(value);
    }
    private void Set(NativeState state, string name, NativeValue value)
    {
        if (name is "xzr" or "wzr") return;
        if (name.StartsWith('w') && value.Expression is ConstantExpression) value = value with { Type = "int32_t" };
        if (RegisterWidth(name) == 32 && value.Bits.Width > 32) value = value with { Bits = BitOps.Slice(value.Bits, 0, 32) };
        if (RegisterWidth(name) == 32 && value.Bits.Width < 32) value = value with { Bits = BitOps.Concat([value.Bits, BitOps.Constant(0, 32 - value.Bits.Width)]) };
        if (RegisterWidth(name) == 32 && value.Bits.Width == 32) value = value with { Bits = BitOps.Concat([value.Bits, BitOps.Constant(0, 32)]) };
        var physicalWidth = Canonical(name).StartsWith('v') ? 128 : 64;
        if (value.Bits.Width < physicalWidth)
            value = value with { Bits = BitOps.Concat([value.Bits, new UnknownBits("unused-register-bits", "ABI 未定义的高位", physicalWidth - value.Bits.Width)]) };
        state.Registers[Canonical(name)] = value;
    }
    private static NativeValue Constant(long value, int width = 64) => new(BitOps.Constant(value, width), width == 32 ? "int32_t" : "int64_t", new ConstantExpression(value));
    private NativeValue OperandValue(NativeState state, Operand operand) => operand.Kind switch
    {
        1 => Read(state, operand.Register!), 2 => Constant(operand.Immediate), _ => new(new UnknownBits("operand", "未知操作数", 64), "unknown", new UnknownExpression("operand"))
    };
    private static Expression Unwrap(Expression expression) => expression is CapturedExpression c ? Unwrap(c.Value) : expression;
    private NativeState Merge(ulong address, List<(ulong Predecessor, NativeState State)> incoming)
    {
        var states = incoming.Select(i => i.State).ToArray();
        if (states.Length == 1) return states[0].Copy();
        var output = states[0].Copy();
        foreach (var key in states.SelectMany(s => s.Registers.Keys).Distinct())
        {
            var values = states.Select(s => Read(s, key)).ToArray();
            if (values.All(v => v == values[0])) output.Registers[key] = values[0];
            else if (values[0].Type is "float" or "double" && values.All(v => v.Type == values[0].Type && v.Expression == values[0].Expression))
                output.Registers[key] = values[0] with { Bits = BitOps.Phi($"{address:x}:{key}", values.Select(v => v.Bits)) };
            else
            {
                var type = values.Select(v => v.Type).Distinct().Count() == 1 ? values[0].Type : "unknown";
                output.Registers[key] = new(BitOps.Phi($"{address:x}:{key}", values.Select(v => v.Bits)), type,
                    new PhiExpression($"phi_{address:x}_{key}", type, incoming.Select((item, index) => new PhiInput(item.Predecessor, values[index].Expression)).ToArray()));
            }
        }
        output.Stack = MemoryState.Merge($"{address:x}", states.Select(s => s.Stack).ToArray());
        foreach (var key in output.StackViews.Keys.ToArray())
            if (states.Any(s => s.StackViews.GetValueOrDefault(key) != output.StackViews[key])) output.StackViews.Remove(key);
        output.Comparison = states.All(s => s.Comparison == states[0].Comparison) ? states[0].Comparison : null;
        return output;
    }
    private Expression? Step(Instruction i, NativeState s, List<Statement> statements, LiftResult result)
    {
        var o = i.Operands;
        if (i.Mnemonic == "add" && o.Length == 3 && o[2] is { Kind: 1, Extend: 7, ShiftKind: 1 } &&
            layouts.ArrayElements(OperandValue(s, o[1]).Type) is { } elements && (1L << (int)o[2].Shift) == layouts.Size(elements.Type))
        {
            var array = OperandValue(s, o[1]); var index = OperandValue(s, o[2]);
            if (index.Type != "int32_t") { Unsupported("数组索引类型未确定"); return null; }
            Set(s, o[0].Register!, new(new InputBits($"indexed:{i.Address:x}", 64), array.Type, new IndexedArrayAddress(array.Expression, index.Expression, elements)));
            return null;
        }
        if (o.Any(p => p.Shift != 0 || p.Extend != 0)) { Unsupported("带移位或扩展的操作数"); return null; }
        switch (i.Mnemonic)
        {
            case "nop": break;
            case "adrp": case "adr":
                Set(s, o[0].Register!, new(BitOps.Constant(o[1].Immediate, 64), "address", new AddressExpression((ulong)o[1].Immediate))); break;
            case "mov": Set(s, o[0].Register!, OperandValue(s, o[1])); break;
            case "and":
            {
                var left = OperandValue(s, o[1]); var width = RegisterWidth(o[0].Register!);
                if (o[2].Kind != 2) { Unsupported("寄存器按位与尚未接通"); break; }
                var mask = unchecked((ulong)o[2].Immediate);
                if (left.Type == "bool" && mask == 1)
                {
                    var boolean = left.Expression;
                    while (boolean is SliceExpression { BitOffset: 0, BitWidth: >= 8 } slice) boolean = slice.Value;
                    Set(s, o[0].Register!, new(BitOps.Concat([BitOps.Slice(left.Bits, 0, 1), BitOps.Constant(0, width - 1)]), "bool", boolean)); break;
                }
                var bits = System.Numerics.BitOperations.PopCount(mask);
                if (bits == 0 || bits > width || (mask & (mask + 1)) != 0) { Unsupported("非连续低位掩码尚未接通"); break; }
                var low = Project(NativeValues.Slice(left, 0, bits));
                Set(s, o[0].Register!, low with { Bits = bits == width ? low.Bits : BitOps.Concat([low.Bits, BitOps.Constant(0, width - bits)]) });
                break;
            }
            case "lsr":
            {
                var width = RegisterWidth(o[0].Register!); var shift = checked((int)o[2].Immediate);
                if (o[2].Kind != 2 || shift < 0 || shift >= width) { Unsupported("逻辑右移的位数未确认"); break; }
                var low = Project(NativeValues.Slice(OperandValue(s, o[1]), shift, width - shift));
                Set(s, o[0].Register!, low with { Bits = shift == 0 ? low.Bits : BitOps.Concat([low.Bits, BitOps.Constant(0, shift)]) });
                break;
            }
            case "cset":
                if (s.Comparison is not { } compared || i.ConditionCode is not (1 or 2 or 11 or 12 or 13 or 14)) { Unsupported("条件置位的标志或条件码未支持"); break; }
                if (!(compared.Left.Type == "int32_t" && compared.Left.Bits.Width == 32 || compared.Left.Type == "int64_t" && compared.Left.Bits.Width == 64) ||
                    !(compared.Right.Expression is ConstantExpression || compared.Right.Type == compared.Left.Type && compared.Right.Bits.Width == compared.Left.Bits.Width))
                { Unsupported("条件置位需要匹配位宽的有符号整数比较"); break; }
                var op = i.ConditionCode switch { 1 => "==", 2 => "!=", 11 => ">=", 12 => "<", 13 => ">", _ => "<=" };
                Numeric(ValueOperation.Select, "int32_t", Compare(op, compared.Left, compared.Right), new ConstantExpression(1), new ConstantExpression(0));
                break;
            case "add": case "sub":
            {
                var left = OperandValue(s, o[1]); var right = OperandValue(s, o[2]);
                if (o[0].Register == "sp" && o[1].Register == "sp" && right.Expression is ConstantExpression sp)
                    s.StackOffset = checked(s.StackOffset + (i.Mnemonic == "add" ? sp.Value : -sp.Value));
                else if (left.Expression is StackAddressExpression stack && right.Expression is ConstantExpression delta)
                {
                    var offset = checked(stack.Offset + (i.Mnemonic == "add" ? delta.Value : -delta.Value));
                    Set(s, o[0].Register!, new(new InputBits($"stack-address:{offset}", 64), "stack-address", new StackAddressExpression(offset)));
                }
                else if (left.Expression is AddressExpression a && right.Expression is ConstantExpression c)
                {
                    var sum = checked((ulong)((long)a.Address + (i.Mnemonic == "add" ? c.Value : -c.Value)));
                    Set(s, o[0].Register!, new(BitOps.Constant(sum, 64), "address", new AddressExpression(sum)));
                }
                else if (i.Mnemonic == "add" && right.Expression is ConstantExpression displacement &&
                    layouts.FieldAt(left.Type, checked((int)displacement.Value)) is { } field && Location(left, field.Offset, field.Size) is { } location)
                    Set(s, o[0].Register!, new(new InputBits($"field-address:{i.Address:x}", 64), field.Type + "*", new AddressOfExpression(location) { RootType = (left.Expression as AddressOfExpression)?.RootType ?? left.Type }));
                else if (o[0].Register is { } destination && destination[0] is 'w' or 'x' && left.Type is "int32_t" or "int64_t" or "uint32_t" or "uint64_t" &&
                    (RegisterWidth(destination) == 32 || left.Type is "int64_t" or "uint64_t"))
                    Numeric(i.Mnemonic == "add" ? ValueOperation.Add : ValueOperation.Subtract, RegisterWidth(destination) == 32 ? "int32_t" : "int64_t", left.Expression, right.Expression);
                else Unsupported("算术操作数类型未确定");
                break;
            }
            case "scvtf":
            {
                if (o.Length != 2 || o[0].Register?[0] is not ('s' or 'd') || o[1].Register?[0] is not ('w' or 'x')) { Unsupported("不支持的 SCVTF 变体"); break; }
                var input = OperandValue(s, o[1]);
                if (input.Type is not ("int32_t" or "int64_t" or "uint32_t" or "uint64_t")) { Unsupported("整数转浮点的输入类型未确定"); break; }
                var expression = input.Expression;
                if (o[1].Register![0] == 'x' && input.Type is "int32_t" or "uint32_t")
                {
                    if (BitOps.Slice(input.Bits, 32, 32) is not ConstantBits { Value.IsZero: true }) { Unsupported("64 位整数转换的高位未确定"); break; }
                    expression = new OperationExpression(ValueOperation.ZeroExtendWord, "int64_t", [expression]);
                }
                Numeric(ValueOperation.SignedToFloat, o[0].Register![0] == 's' ? "float" : "double", expression, new ConstantExpression(RegisterWidth(o[1].Register!))); break;
            }
            case "fdiv":
                if (o.Length != 3 || o[0].Register?[0] is not ('s' or 'd') || o.Skip(1).Any(p => p.Register?[0] != o[0].Register![0])) { Unsupported("不支持的 FDIV 变体"); break; }
                if (!o.Skip(1).All(FloatOperand)) { Unsupported("浮点除法的输入类型未确定"); break; }
                Numeric(ValueOperation.FloatDivide, o[0].Register![0] == 's' ? "float" : "double", OperandValue(s, o[1]).Expression, OperandValue(s, o[2]).Expression); break;
            case "frintp":
                if (o.Length != 2 || o[0].Register?[0] is not ('s' or 'd') || o[1].Register?[0] != o[0].Register![0]) { Unsupported("不支持的 FRINTP 变体"); break; }
                if (!FloatOperand(o[1])) { Unsupported("浮点取整的输入类型未确定"); break; }
                Numeric(ValueOperation.Ceiling, o[0].Register![0] == 's' ? "float" : "double", OperandValue(s, o[1]).Expression); break;
            case "fcvtps":
                if (o.Length != 2 || o[0].Register?[0] is not ('w' or 'x') || o[1].Register?[0] is not ('s' or 'd')) { Unsupported("不支持的 FCVTPS 变体"); break; }
                if (!FloatOperand(o[1])) { Unsupported("浮点转整数的输入类型未确定"); break; }
                Numeric(ValueOperation.FloatToSignedCeiling, o[0].Register![0] == 'w' ? "int32_t" : "int64_t", OperandValue(s, o[1]).Expression); break;
            case "fmov":
                if (o.Length != 2 || o[1].Kind != 1 || RegisterWidth(o[0].Register!) != RegisterWidth(o[1].Register!)) { Unsupported("不支持的 FMOV 变体"); break; }
                if (RegisterWidth(o[0].Register!) == 64 && o[0].Register![0] != o[1].Register![0]) { Unsupported("64 位跨寄存器组 FMOV 尚未接通"); break; }
                if (o[1].Register![0] is 's' or 'd' && !FloatOperand(o[1])) { Unsupported("FMOV 浮点源的位解释未确定"); break; }
                if (o[0].Register![0] == o[1].Register![0]) Set(s, o[0].Register!, OperandValue(s, o[1]));
                else Numeric(ValueOperation.BitCast, o[0].Register![0] switch { 's' => "float", 'd' => "double", 'w' => "int32_t", _ => "int64_t" }, OperandValue(s, o[1]).Expression);
                break;
            case "fcmp":
                if (o.Length != 2 || !o.All(FloatOperand)) { Unsupported("浮点比较的输入类型未确定"); s.Comparison = null; break; }
                s.Comparison = (OperandValue(s, o[0]), OperandValue(s, o[1])); break;
            case "csel":
                if (s.Comparison is not { } comparison || i.ConditionCode is not (1 or 2)) { Unsupported("条件选择的标志或条件码未支持"); break; }
                if (o.Skip(1).Any(p => OperandValue(s, p).Type is not ("int32_t" or "int64_t" or "uint32_t" or "uint64_t"))) { Unsupported("条件选择的操作数不是已知整数"); break; }
                Numeric(ValueOperation.Select, RegisterWidth(o[0].Register!) == 32 ? "int32_t" : "int64_t",
                    new BinaryExpression(i.ConditionCode == 1 ? "==" : "!=", comparison.Left.Expression, comparison.Right.Expression), OperandValue(s, o[1]).Expression, OperandValue(s, o[2]).Expression);
                break;
            case "stp": case "ldp": case "str": case "strb": case "strh": case "ldr": case "ldrb": case "ldrh": case "ldur": case "stur":
            {
                var pair = i.Mnemonic is "stp" or "ldp";
                var mem = o[pair ? 2 : 1];
                if (mem.Kind != 3 || mem.Index is not null) { Unsupported("索引内存寻址"); break; }
                var load = i.Mnemonic.StartsWith("ld");
                var size = i.Mnemonic.EndsWith('b') ? 1 : i.Mnemonic.EndsWith('h') ? 2 : RegisterWidth(o[0].Register!) / 8;
                var baseValue = Read(s, mem.Base!);
                var offset = mem.Displacement;
                if (mem.Base == "sp" && i.Writeback && !i.PostIndex) { s.StackOffset += offset; offset = 0; }
                for (var n = 0; n < (pair ? 2 : 1); n++)
                {
                    var at = offset + n * size;
                    if (mem.Base == "sp")
                    {
                        var slot = new StorageAddress(stackRegion, s.StackOffset + at);
                        if (load)
                        {
                            var loaded = NativeValues.LoadStack(s, stackRegion, slot.Offset, size);
                            if (mutableStack.Any(p => slot.Offset >= p.Key && slot.Offset + size <= p.Key + layouts.Size(p.Value.Type)))
                            {
                                loaded = Project(loaded);
                                loaded = Capture(i.Address, size, loaded.Type, loaded.Expression, statements);
                            }
                            Set(s, o[n].Register!, loaded);
                        }
                        else
                        {
                            var value = Read(s, o[n].Register!);
                            NativeValues.StoreStack(s, stackRegion, slot.Offset, NativeValues.Slice(value, 0, size * 8, value.Type), $"store_{i.Address:x}_{n}");
                        }
                    }
                    else if (load) Set(s, o[n].Register!, Load(i.Address, baseValue, at, size, statements, result));
                    else
                    {
                        if (baseValue.Expression is AddressExpression address)
                            statements.Add(new StoreStatement(i.Address, new AddressExpression(checked(address.Address + (ulong)at)), Read(s, o[n].Register!).Expression));
                        else if (Location(baseValue, at, size) is { } location)
                        {
                            var value = Read(s, o[n].Register!).Expression;
                            if (location is MemberExpression member && member.Field.Type.EndsWith("_o*") && value is ConstantExpression { Value: 0 }) value = new NameExpression("null");
                            statements.Add(new StoreStatement(i.Address, location, value));
                            result.Proofs.Add(new(i.Address, "FieldStore", "typed field address from Clang layout; store and GC barrier remain separate operations"));
                        }
                        else Unsupported("存储地址未解析");
                    }
                }
                if (mem.Base == "sp" && i.Writeback && i.PostIndex) s.StackOffset += o[^1].Immediate;
                if (mem.Base != "sp" && i.Writeback)
                {
                    var displacement = i.PostIndex ? checked((int)o[^1].Immediate) : mem.Displacement;
                    if (Location(baseValue, displacement, size) is { } location)
                        Set(s, mem.Base!, new(new InputBits($"field-address:{i.Address:x}", 64), "field-address", new AddressOfExpression(location) { RootType = (baseValue.Expression as AddressOfExpression)?.RootType ?? baseValue.Type }));
                    else Unsupported("写回地址未解析");
                }
                break;
            }
            case "cmp": s.Comparison = (OperandValue(s, o[0]), OperandValue(s, o[1])); break;
            case "cbz": case "cbnz":
            {
                var value = Read(s, o[0].Register!);
                var reference = value.Type.EndsWith("_o*") || value.Type.EndsWith("_array*") || value.Type == "Il2CppObject*";
                return new BinaryExpression(reference ? (i.Mnemonic == "cbz" ? "is" : "is not") : (i.Mnemonic == "cbz" ? "==" : "!="),
                    value.Expression, reference ? new NameExpression("null") : new ConstantExpression(0));
            }
            case "tbz": case "tbnz":
                var bitValue = Read(s, o[0].Register!);
                if (bitValue.Type == "bool" && o[1].Immediate == 0)
                {
                    var expression = bitValue.Expression;
                    while (expression is SliceExpression { BitOffset: 0 } slice) expression = slice.Value;
                    return new BinaryExpression(i.Mnemonic == "tbz" ? "==" : "!=", expression, new NameExpression("false"));
                }
                return new BinaryExpression(i.Mnemonic == "tbz" ? "==" : "!=", new BinaryExpression("&", Read(s, o[0].Register!).Expression, new ConstantExpression(1L << (int)o[1].Immediate)), new ConstantExpression(0));
            case "b.eq": case "b.ne":
                if (s.Comparison is { } compare) return Compare(i.Mnemonic == "b.eq" ? "==" : "!=", compare.Left, compare.Right);
                Unsupported("条件标志来源未确定"); break;
            case "b.ge": case "b.gt": case "b.lt": case "b.le": case "b.hs": case "b.lo": case "b.hi": case "b.ls":
                if (s.Comparison is not { } integer || integer.Left.Type is not ("int32_t" or "uint32_t" or "int64_t" or "uint64_t") ||
                    !(integer.Right.Expression is ConstantExpression || integer.Right.Type == integer.Left.Type && integer.Right.Bits.Width == integer.Left.Bits.Width))
                { Unsupported("整数分支的类型或位宽未确定"); break; }
                var unsigned = i.Mnemonic is "b.hs" or "b.lo" or "b.hi" or "b.ls";
                Expression Cast(NativeValue v) => unsigned ? new OperationExpression(ValueOperation.Unsigned, integer.Left.Bits.Width == 32 ? "uint32_t" : "uint64_t", [v.Expression]) : v.Expression;
                return new BinaryExpression(i.Mnemonic switch { "b.ge" or "b.hs" => ">=", "b.gt" or "b.hi" => ">", "b.lt" or "b.lo" => "<", _ => "<=" }, Cast(integer.Left), Cast(integer.Right));
            case "bl": DirectCall(i, s, statements, result); break;
            case "br": DelegateCall(i, s, statements, result); break;
            case "b":
                if (NativeGraph.Target(i) < result.Method.Address || NativeGraph.Target(i) > result.Instructions[^1].Address)
                {
                    DirectCall(i, s, statements, result);
                    statements.Add(new ReturnStatement(i.Address, ReturnValue(result.Method, s)));
                    result.Proofs.Add(new(i.Address, "DirectTailCall", "external branch to a known method or runtime helper; existing call semantics retained; no fallthrough"));
                }
                break;
            case "ret": statements.Add(new ReturnStatement(i.Address, ReturnValue(result.Method, s))); break;
            default: Unsupported("指令尚未支持：" + i.Mnemonic); break;
        }
        return null;
        Expression Compare(string operation, NativeValue left, NativeValue right)
        {
            string? EnumType(Expression expression)
            {
                expression = Unwrap(expression);
                if (expression is MemberExpression m) return managed.BaseTypeOf(m.ManagedType ?? "") == "System.Enum" ? m.ManagedType : null;
                var parameters = result.Method.Parameters.Where(p => p.Name != "__this" && p.Name != "method").ToArray();
                var signature = managed.SignatureOf(result.Method.Name.Split("$$")[0], result.Method.Name.Split("$$")[1]);
                var index = expression is NameExpression n ? Array.FindIndex(parameters, p => p.Name == n.Name) : -1;
                var type = index >= 0 && signature is { } sig && index < sig.ParameterTypes.Length ? sig.ParameterTypes[index] : null;
                return type is not null && managed.BaseTypeOf(type) == "System.Enum" ? type : null;
            }
            var leftEnum = EnumType(left.Expression); var rightEnum = EnumType(right.Expression);
            if (operation is "==" or "!=" && leftEnum is not null && right.Expression is ConstantExpression number)
                return new BinaryExpression(operation, left.Expression, number with { EnumType = leftEnum, EnumMember = managed.EnumNames.GetValueOrDefault((leftEnum, number.Value)) });
            if (leftEnum is null && rightEnum is null) return new BinaryExpression(operation, left.Expression, EnumConstant(left, right));
            Expression Cast(NativeValue v, string? type) => type is null ? v.Expression : new OperationExpression(ValueOperation.IntegerCast, v.Bits.Width == 32 ? "int32_t" : "int64_t", [v.Expression]);
            return new BinaryExpression(operation, Cast(left, leftEnum), Cast(right, rightEnum));
        }
        bool FloatOperand(Operand operand) => operand.Register?[0] is 's' or 'd' &&
            OperandValue(s, operand).Type == (operand.Register[0] == 's' ? "float" : "double");
        void Numeric(ValueOperation operation, string type, params Expression[] arguments)
        {
            var expression = new OperationExpression(operation, type, arguments);
            var value = Capture(i.Address, RegisterWidth(o[0].Register!) / 8, type, expression, statements);
            Set(s, o[0].Register!, value);
        }
        void Unsupported(string reason)
        {
            result.Problems.Add($"0x{i.Address:x}: {reason}");
            statements.Add(new UnresolvedStatement(i.Address, reason));
        }
    }
    private Expression? ReturnValue(NativeMethod method, NativeState state)
    {
        if (method.ReturnType == "void") return null;
        var layout = Classify(method);
        if (layout is null || layout.Return.Indirect) return new UnknownExpression("return-abi");
        var pieces = layout.Return.Pieces.Select(p => NativeValues.Slice(Read(state, ((RegisterLocation)p.Location).Name.ToLowerInvariant()), 0, p.Size * 8)).ToArray();
        var value = pieces.Length == 1 ? pieces[0] : NativeValues.Compose(pieces, method.ReturnType);
        if (layout.Return.Shape.Kind is ShapeKind.Composite or ShapeKind.HomogeneousFloat)
            return new AggregateExpression(symbols.Display(method.ReturnType), value.Expression);
        return method.ReturnType == "bool" && value.Type != "bool" ? BooleanValue(value.Expression) : value.Expression;
    }
    private NativeValue Load(ulong pc, NativeValue receiver, int offset, int size, List<Statement> statements, LiftResult result)
    {
        if (receiver.Expression is IndexedArrayAddress indexed && offset == indexed.Elements.Offset && size == layouts.Size(indexed.Elements.Type))
            return Capture(pc, size, indexed.Elements.Type, new OperationExpression(ValueOperation.ArrayElement, indexed.Elements.Type, [indexed.Array, indexed.Index]), statements);
        if (layouts.ArrayElements(receiver.Type) is not null)
        {
            var length = layouts.Members(receiver.Type).Single(f => f.Name == "max_length");
            if (offset == length.Offset && size is 4 or 8)
                return Capture(pc, size, size == 4 ? "int32_t" : "int64_t", new InvocationExpression(size == 4 ? "Length" : "LongLength", receiver.Expression, [], true), statements);
            if (Location(receiver, offset, size) is OperationExpression element)
                return Capture(pc, size, element.Type, element, statements);
        }
        if (receiver.Expression is AddressOfExpression && Location(receiver, offset, size) is MemberExpression indirect)
            return Capture(pc, size, indirect.Field.Type, indirect, statements);
        if (receiver.Expression is AddressExpression address)
        {
            var at = checked((ulong)((long)address.Address + offset));
            if (size == 8 && image.TryRelativePointer(at, out var target))
            {
                result.Proofs.Add(new(pc, "ELF_RELATIVE", $"0x{at:x} -> 0x{target:x}"));
                if (symbols.Metadata.TryGetValue(target, out var metadata))
                    return new(new InputBits($"slot:{target:x}", 64), "metadata-slot", new MetadataExpression(metadata, true));
                return new(BitOps.Constant(target, 64), "address", new AddressExpression(target));
            }
            return Capture(pc, size, size == 1 ? "uint8_t" : "unknown", new AddressExpression(at), statements);
        }
        if (receiver.Expression is MetadataExpression { IsSlot: true } slot && offset == 0 && size == 8)
        {
            result.Proofs.Add(new(pc, "MetadataSlotLoad", slot.Reference.Name));
            return new(new InputBits($"metadata:{slot.Reference.Slot:x}", 64), slot.Reference.Type.Length > 0 ? slot.Reference.Type : "MethodInfo*", slot with { IsSlot = false });
        }
        var field = layouts.Field(receiver.Type, offset, size);
        if (field is not null)
        {
            if (field.Name == "klass" && field.DeclaringRecord == "Il2CppObject")
                return Capture(pc, size, field.Type, new InvocationExpression("Runtime.ClassOf", null, [receiver.Expression], false), statements);
            if (field.Name == "element_class" && field.DeclaringRecord == "Il2CppClass_1")
                return Capture(pc, size, field.Type, new InvocationExpression("Runtime.ElementClass", null, [receiver.Expression], false), statements);
            var owner = field.DeclaringRecord.EndsWith("_Fields") ? field.DeclaringRecord[..^7] + "_o" : field.DeclaringRecord;
            var managedOwner = symbols.Display(owner);
            var rawField = field.Name.Contains("_k__BackingField") ? "<" + field.Name.TrimStart('_').Replace("_k__BackingField", ">k__BackingField") : field.Name;
            managed.FieldTypes.TryGetValue((ManagedNames.SplitGeneric(managedOwner).Name, rawField), out var fieldType);
            if (fieldType is not null && !fieldType.Contains('!') && (field.Type.EndsWith("_o*") || field.Type.EndsWith("_array*"))) symbols.DisplayTypes.TryAdd(field.Type.TrimEnd('*'), fieldType);
            var display = Getter(receiver.Type, offset, size) ?? field.Name;
            result.Proofs.Add(new(pc, "ClangFieldLayout", $"{receiver.Type}+0x{offset:x}/{size} = {field.DeclaringRecord}.{field.Name}"));
            return Capture(pc, size, field.Type, new MemberExpression(receiver.Expression, field, display, fieldType), statements);
        }
        result.Problems.Add($"0x{pc:x}: 无法将 {receiver.Type}+0x{offset:x}/{size} 映射为字段");
        return Capture(pc, size, "unknown", new UnknownExpression($"load({receiver.Type}+0x{offset:x})"), statements);
    }
    private static NativeValue Capture(ulong pc, int size, string type, Expression expression, List<Statement> statements)
    {
        var count = statements.OfType<AssignStatement>().Count(a => a.Address == pc);
        var name = $"v_{pc:x}" + (count == 0 ? "" : $"_{count}");
        statements.Add(new AssignStatement(pc, name, expression, type));
        return new(new InputBits(name, size * 8), type, new CapturedExpression(name, expression));
    }
    private string? Getter(string type, int offset, int size)
    {
        var key = (type, offset, size);
        if (getters.TryGetValue(key, out var cached)) return cached;
        var fields = layouts.Field(type, offset, size);
        if (fields is null) return null;
        var owner = fields.DeclaringRecord.EndsWith("_Fields") ? fields.DeclaringRecord[..^7] + "_o" : fields.DeclaringRecord;
        var name = ManagedNames.SplitGeneric(symbols.Display(owner)).Name;
        foreach (var candidate in symbols.Methods.Values.SelectMany(m => m).Where(m => m.Name.Contains("$$get_") && ManagedNames.SplitGeneric(m.Name.Split("$$")[0]).Name == name))
        {
            var instructions = decoder.Decode(image.Read(candidate.Address, 8), candidate.Address);
            var load = instructions[0];
            if (instructions.Length == 2 && load.Mnemonic == "ldr" && instructions[1].Mnemonic == "ret" && load.Operands.Length == 2 &&
                load.Operands[0].Register is "x0" or "w0" && load.Operands[1] is { Kind: 3, Base: "x0", Index: null } mem &&
                mem.Displacement == offset && RegisterWidth(load.Operands[0].Register!) / 8 == size)
                return getters[key] = candidate.Name.Split("$$get_")[1];
        }
        return getters[key] = null;
    }
    private Expression EnumConstant(NativeValue left, NativeValue right)
    {
        if (Unwrap(left.Expression) is MemberExpression { ManagedType: { } type } && right.Expression is ConstantExpression c && managed.EnumNames.TryGetValue((type, c.Value), out var name))
            return new NameExpression(type + "." + name);
        return right.Expression;
    }
    private CallLayout? Classify(NativeMethod method) => new NativeAbi(layouts, managed).Classify(method);
    private void Clobber(NativeState state, ulong pc)
    {
        var registers = new RegisterState($"before:{pc:x}");
        foreach (var pair in state.Registers.Where(p => p.Key.StartsWith('x') && p.Value.Bits.Width == 64)) registers = registers.Set(pair.Key.ToUpperInvariant(), pair.Value.Bits);
        foreach (var pair in state.Registers.Where(p => p.Key.StartsWith('v') && p.Value.Bits.Width == 128)) registers = registers.Set(pair.Key.ToUpperInvariant(), pair.Value.Bits);
        registers = registers.AfterCall($"call:{pc:x}");
        for (var i = 0; i <= 18; i++) state.Registers[$"x{i}"] = new(registers.Read($"X{i}"), "unknown", new UnknownExpression($"clobber_{pc:x}_x{i}"));
        state.Registers["x30"] = new(registers.Read("X30"), "unknown", new UnknownExpression("link-register"));
        for (var i = 0; i < 32; i++)
        {
            var old = state.Registers.GetValueOrDefault($"v{i}");
            state.Registers[$"v{i}"] = i is >= 8 and <= 15 && old?.Type is "float" or "double" ?
                old with { Bits = registers.Read($"V{i}") } : new(registers.Read($"V{i}"), "unknown", new UnknownExpression($"clobber_{pc:x}_v{i}"));
        }
        state.Comparison = null;
    }
    private void DirectCall(Instruction instruction, NativeState state, List<Statement> statements, LiftResult result, NativeMethod? resolvedVirtual = null)
    {
        var target = resolvedVirtual?.Address ?? NativeGraph.Target(instruction);
        if (runtime.Helpers.TryGetValue(target, out var helper))
        {
            RuntimeCall(instruction, helper, state, statements, result); return;
        }
        var candidate = resolvedVirtual ?? symbols.Unique(target);
        var method = candidate is null ? null : new NativeAbi(layouts, managed).Normalize(candidate);
        var layout = method is null ? null : Classify(method);
        if (method is null || layout is null)
        {
            result.Problems.Add($"0x{instruction.Address:x}: 调用 0x{target:x} 的 ABI 未确认");
            statements.Add(new UnresolvedStatement(instruction.Address, $"raw_call 0x{target:x}; 原始操作数保留于机器码")); Clobber(state, instruction.Address); return;
        }
        var arguments = new List<NativeValue>();
        foreach (var value in layout.Arguments)
        {
            if (value.Indirect)
            { result.Problems.Add($"0x{instruction.Address:x}: 调用包含尚未接通的间接聚合参数"); Clobber(state, instruction.Address); return; }
            var parts = value.Pieces.Select(piece => piece.Location is RegisterLocation register ?
                NativeValues.Slice(Read(state, register.Name.ToLowerInvariant()), register.BitOffset, piece.Size * 8) :
                NativeValues.LoadStack(state, stackRegion, state.StackOffset + ((StackLocation)piece.Location).Offset, piece.Size)).ToArray();
            var argumentType = method.Parameters[arguments.Count].Type;
            var argumentValue = Project(NativeValues.Compose(parts, argumentType));
            if (argumentType == "bool" && parts.Length == 1 && parts[0].Type != "bool" && argumentValue.Expression is not ConstantExpression)
                argumentValue = argumentValue with { Expression = BooleanValue(argumentValue.Expression) };
            if (value.Shape.Kind is ShapeKind.Composite or ShapeKind.HomogeneousFloat && argumentValue.Expression is SliceExpression or ComposeExpression)
                argumentValue = argumentValue with { Expression = new AggregateExpression(symbols.Display(argumentType), argumentValue.Expression) };
            arguments.Add(argumentValue);
        }
        if (ConstructOnStack(method, arguments.ToArray(), instruction.Address, state, statements, result)) return;
        var name = method.Name.Replace("$$", ".");
        var instanceName = method.Name.Split("$$")[1];
        var returnType = method.ReturnType;
        string? managedReturn = null;
        var methodInfo = arguments.LastOrDefault()?.Expression as MetadataExpression;
        if (methodInfo is { IsSlot: false, Reference.Kind: "ScriptMetadataMethod" })
        {
            var metadataName = methodInfo.Reference.Name;
            var logicalReturn = managed.ReturnOf(metadataName);
            var bodyType = ManagedNames.SplitGeneric(method.Name.Split("$$")[0]).Name;
            var refText = metadataName.StartsWith("Method$") ? metadataName[7..] : metadataName;
            var paren = refText.IndexOf('('); if (paren >= 0) refText = refText[..paren];
            var separator = ManagedNames.LastTopLevelDot(refText);
            if (separator >= 0 && (methodInfo.Reference.MethodAddress == 0 || methodInfo.Reference.MethodAddress == target) &&
                ManagedNames.SplitGeneric(refText[..separator]).Name == bodyType &&
                ManagedNames.SplitGeneric(refText[(separator + 1)..]).Name == ManagedNames.SplitGeneric(method.Name.Split("$$")[1]).Name &&
                ManagedNames.SplitGeneric(refText[(separator + 1)..]).Arguments.Length == ManagedNames.SplitGeneric(method.Name.Split("$$")[1]).Arguments.Length)
            {
                var shortReturn = logicalReturn is null ? null : logicalReturn.Contains('.') ? logicalReturn : symbols.DisplayTypes.Values.FirstOrDefault(t => t.EndsWith("." + logicalReturn));
                var concrete = symbols.DisplayTypes.FirstOrDefault(t => t.Value == shortReturn).Key;
                if (concrete is not null && method.ReturnType.EndsWith('*')) returnType = concrete + "*";
                name = refText;
                managedReturn = logicalReturn;
                instanceName = refText[(separator + 1)..];
                result.Proofs.Add(new(instruction.Address, "SharedGenericContext", $"body={method.Name}; MethodInfo={metadataName}; native target=0x{target:x} and ABI retained; metadata target=0x{methodInfo.Reference.MethodAddress:x}"));
            }
        }
        var isInstance = method.Parameters.FirstOrDefault()?.Name == "__this";
        var visible = new List<Expression>();
        var managedCall = managed.SignatureOf(method.Name.Split("$$")[0], method.Name.Split("$$")[1]);
        for (var p = isInstance ? 1 : 0; p < arguments.Count; p++)
        {
            if (method.Parameters[p].Name == "method" && method.Parameters[p].Type.Contains("MethodInfo")) continue;
            var argument = arguments[p];
            if (Unwrap(argument.Expression) is UnknownExpression) result.Problems.Add($"0x{instruction.Address:x}: 参数 {p} 的值未确定");
            var expression = argument.Expression;
            if (expression is ConstantExpression constant)
            {
                var index = p - (isInstance ? 1 : 0);
                var logicalType = managedCall is { } signature && index < signature.ParameterTypes.Length ? signature.ParameterTypes[index] : null;
                if (logicalType is not null && managed.EnumNames.TryGetValue((logicalType, constant.Value), out var enumName)) expression = new NameExpression(logicalType + "." + enumName);
                else if (method.Parameters[p].Type == "bool") expression = new NameExpression(constant.Value == 0 ? "false" : "true");
                else if (constant.Value == 0 && (method.Parameters[p].Type.EndsWith("_o*") || method.Parameters[p].Type == "Il2CppObject*")) expression = new NameExpression("null");
            }
            visible.Add(expression);
        }
        var variable = returnType == "void" ? null : $"call_{instruction.Address:x}";
        var returnBuffer = layout.Return.Indirect && layout.Return.Pieces[0].Location is RegisterLocation bufferRegister ? Read(state, bufferRegister.Name.ToLowerInvariant()).Expression as StackAddressExpression : null;
        var property = visible.Count == 0 && managed.IsPropertyGetter(method.Name.Split("$$")[0], method.Name.Split("$$")[1]);
        Expression? receiver = isInstance ? arguments[0].Expression : null;
        if (receiver is StackAddressExpression stackReceiver && mutableStack.TryGetValue(stackReceiver.Offset, out var local)) receiver = new NameExpression(local.Name);
        if (isInstance && arguments[0].Expression is SliceExpression && method.Name.Split("$$")[0] == result.Method.Name.Split("$$")[0] && result.Method.Parameters.FirstOrDefault()?.Name == "__this")
        {
            var boundary = UnwindBoundary.Read(image, target);
            if (boundary.Start == target && boundary.End > target && boundary.End - target <= 16384)
            {
                var body = new NativeGraph(decoder.Decode(image.Read(target, (int)(boundary.End - target)), target), runtime.NoReturn);
                if (UnusedReceiver.Prove(body))
                {
                    receiver = new NameExpression("this");
                    result.Proofs.Add(new(instruction.Address, "UnusedReceiver", "all callee paths overwrite X0 before reading it; same-owner instance call uses current this"));
                }
            }
        }
        statements.Add(new CallStatement(instruction.Address, isInstance ? instanceName : name, visible.ToArray(), variable, returnType, isInstance, receiver, property)
        { DeclaringType = method.Name.Split("$$")[0] });
        Clobber(state, instruction.Address);
        if (variable is not null)
        {
            if (layout.Return.Indirect)
            {
                if (returnBuffer is null) result.Problems.Add($"0x{instruction.Address:x}: 返回缓冲尚未绑定存储区域");
                else
                {
                    var returned = new NativeValue(new InputBits(variable, layout.Return.Shape.Size * 8), returnType, new NameExpression(variable));
                    aggregateValues[returned.Bits] = (returnType, returned.Expression);
                    if (managedReturn is not null) aggregateLogicalTypes[returned.Bits] = managedReturn;
                    NativeValues.StoreStack(state, stackRegion, returnBuffer.Offset, returned, variable);
                }
            }
            else
            {
                var returned = new NativeValue(new InputBits(variable, layout.Return.Shape.Size * 8), returnType, new NameExpression(variable));
                if (layout.Return.Shape.Kind is ShapeKind.Composite or ShapeKind.HomogeneousFloat)
                    aggregateValues[returned.Bits] = (returnType, returned.Expression);
                foreach (var piece in layout.Return.Pieces)
                    Set(state, ((RegisterLocation)piece.Location).Name.ToLowerInvariant(), Project(NativeValues.Slice(returned, piece.ValueOffset * 8, piece.Size * 8, layout.Return.Pieces.Count == 1 ? returnType : "native-bits")));
            }
        }
        result.Proofs.Add(new(instruction.Address, "CallArguments", $"{method.Name}; {arguments.Count} native arguments incl. MethodInfo; return pieces={layout.Return.Pieces.Count}"));
    }
    private void DelegateCall(Instruction instruction, NativeState state, List<Statement> statements, LiftResult result)
    {
        if (TryVirtualTailCall(instruction, state, statements, result)) return;
        var target = Read(state, instruction.Operands[0].Register!).Expression;
        var receiver = Read(state, "x0").Expression;
        var method = Read(state, "x2").Expression;
        if (Unwrap(target) is MemberExpression { Field.Name: "invoke_impl" } invoke &&
            Unwrap(receiver) is MemberExpression { Field.Name: "method_code" } code &&
            Unwrap(method) is MemberExpression { Field.Name: "method" } info && invoke.Receiver == code.Receiver && invoke.Receiver == info.Receiver)
        {
            // 这一适配器仅支持一个显式参数；签名由具体 delegate 字段类型验证。
            var field = Unwrap(invoke.Receiver) as MemberExpression;
            if (field?.ManagedType is not { } delegateType || !managed.IsVoidSingleArgumentDelegate(delegateType))
            { Reject("委托 Invoke 签名未唯一确定：" + (field?.ManagedType ?? field?.Field.DeclaringRecord ?? "unknown")); return; }
            var names = new[] { target, receiver, method }.OfType<CapturedExpression>().Select(c => c.Name).ToHashSet();
            statements.RemoveAll(s => s is AssignStatement a && names.Contains(a.Name));
            statements.Add(new CallStatement(instruction.Address, "Invoke", [Read(state, "x1").Expression], null, "void", true, invoke.Receiver));
            statements.Add(new ReturnStatement(instruction.Address, null));
            result.Proofs.Add(new(instruction.Address, "DelegateInvoke", "same delegate invoke_impl/method_code/method; exact Invoke signature; tail transfer retains invocation and exceptions"));
        }
        else Reject("间接尾调用尚未证明为委托调用");
        void Reject(string reason) { result.Problems.Add($"0x{instruction.Address:x}: {reason}"); statements.Add(new UnresolvedStatement(instruction.Address, reason)); }
    }
}
