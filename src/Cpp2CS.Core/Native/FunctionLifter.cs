using Cpp2CS.Abi;
using Cpp2CS.IR;
using Cpp2CS.Model;

namespace Cpp2CS.Native;

public sealed partial class FunctionLifter(ElfImage image, Arm64Decoder decoder, Symbols symbols, HeaderLayout layouts, ManagedNames managed, RuntimeProfile runtime)
{
    private readonly Dictionary<(string Type, int Offset, int Width), string?> getters = [];
    private readonly RegionId stackRegion = new("frame", RegionKind.Stack);
    private SsaSemantics? sharedSemantics;
    public LiftResult Lift(ulong address) => Lift(new Arm64MethodReader(image, decoder, symbols).Read(address));
    public LiftResult Lift(DecodedMethod machine, SsaSemantics? sharedSemantics = null)
    {
        var address = machine.Address;
        this.sharedSemantics = sharedSemantics;
        getters.Clear();
        aggregateValues.Clear();
        mutableStack.Clear();
        unusedArguments.Clear();
        aggregateLogicalTypes.Clear();
        var method = new NativeAbi(layouts, managed).Normalize(symbols.Unique(address) ?? throw new InvalidDataException("入口没有唯一符号签名"));
        ManagedTypeBindings.Bind(method, symbols, layouts, managed);
        var boundary = machine.Boundary;
        var instructions = machine.Instructions;
        var graph = new NativeGraph(instructions, runtime.NoReturn, target => symbols.Unique(target) is not null || runtime.Helpers.ContainsKey(target));
        var result = new LiftResult(method, instructions, [], [.. graph.Problems], [], graph);
        var asyncStateMachine = managed.Implements(method.Name.Split("$$")[0], "System.Runtime.CompilerServices.IAsyncStateMachine");
        if (!asyncStateMachine && boundary.Unsupported is null && boundary.Lsda is not null && graph.Problems.Length == 0)
        {
            var nativeAbi = new NativeAbi(layouts, managed);
            var flow = sharedSemantics?.Program.Flow ?? NativeControlFlow.Build(instructions, boundary, runtime.NoReturn);
            var semantics = sharedSemantics ?? new SsaSemantics(new NativeSsa(flow, method, nativeAbi, symbols).Build(), method, symbols, layouts, nativeAbi, image, runtime, new(image, decoder));
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
                BindAbiValue(entry, ((RegisterLocation)piece.Location).Name.ToLowerInvariant(), NativeValues.Slice(value, piece.ValueOffset * 8, piece.Size * 8));
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
    private static string Canonical(string name) => Arm64Registers.Canonical(name);
    private static int RegisterWidth(string name) => Arm64Registers.Width(name);
    private NativeValue Read(NativeState state, string name)
    {
        if (name is "xzr" or "wzr") return Constant(0, RegisterWidth(name));
        if (Canonical(name) == "sp") return state.StackPointerKnown
            ? new(new InputBits($"stack-address:{state.StackOffset}", 64), "stack-address", new StackAddressExpression(state.StackOffset))
            : new(new UnknownBits("sp", "栈指针未确定", 64), "unknown", new UnknownExpression("sp"));
        var key = Canonical(name);
        var value = state.Registers.GetValueOrDefault(key) ?? new(new UnknownBits(key, "寄存器没有到达定义", RegisterWidth(key)), "unknown", new UnknownExpression(key));
        value = RegisterWidth(name) < value.Bits.Width ? NativeValues.Slice(value, 0, RegisterWidth(name), value.Type) : value;
        if (value.Expression is SliceExpression { Value: AggregateExpression aggregate } slice && slice.BitOffset % 8 == 0 && slice.BitWidth % 8 == 0 &&
            layouts.Field(aggregate.Type, slice.BitOffset / 8, slice.BitWidth / 8) is { } field)
            value = value with { Type = field.Type, Expression = new MemberExpression(aggregate.Bits, field, field.Name, null) };
        return Project(value);
    }
    private static void BindAbiValue(NativeState state, string name, NativeValue value)
    {
        var register = Canonical(name);
        var width = RegisterWidth(register);
        if (value.Bits.Width > width) throw new InvalidOperationException("ABI 分片超过寄存器宽度");
        if (value.Bits.Width < width)
            value = value with { Bits = BitOps.Concat([value.Bits, new UnknownBits("unused-register-bits", "ABI 未定义的高位", width - value.Bits.Width)]) };
        state.Registers[register] = value;
    }
    private static NativeValue Constant(long value, int width = 64) => new(BitOps.Constant(value, width), width == 32 ? "int32_t" : "int64_t", new ConstantExpression(value));
    private static Expression Unwrap(Expression expression) => expression is CapturedExpression c ? Unwrap(c.Value) : expression;
    private NativeState Merge(ulong address, List<(ulong Predecessor, NativeState State)> incoming)
    {
        var states = incoming.Select(i => i.State).ToArray();
        if (states.Length == 1) return states[0].Copy();
        var output = states[0].Copy();
        output.StackPointerKnown = states.All(s => s.StackPointerKnown && s.StackOffset == states[0].StackOffset);
        output.StackEscaped = states.Any(s => s.StackEscaped);
        foreach (var key in states.SelectMany(s => s.Registers.Keys).Distinct())
        {
            var values = states.Select(s => Read(s, key)).ToArray();
            values = NativeValues.JoinReferences(values) ?? values;
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
        output.Comparison = states.All(s => s.Comparison == states[0].Comparison && s.ComparisonKind == states[0].ComparisonKind) ? states[0].Comparison : null;
        return output;
    }
    private Expression Compare(LiftResult result, string operation, NativeValue left, NativeValue right)
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
    private Expression? ReturnValue(NativeMethod method, NativeState state)
    {
        if (method.ReturnType == "void") return null;
        var layout = Classify(method);
        if (layout is null || layout.Return.Indirect) return new UnknownExpression("return-abi");
        var pieces = layout.Return.Pieces.Select(p => NativeValues.Slice(Read(state, ((RegisterLocation)p.Location).Name.ToLowerInvariant()), 0, p.Size * 8)).ToArray();
        var value = pieces.Length == 1 ? pieces[0] : NativeValues.Compose(pieces, method.ReturnType);
        if (NativeValues.ReferenceAs(value, method.ReturnType) is { } reference) return reference.Expression;
        if (NativeValues.IsManagedReference(method.ReturnType) && value.Type == "native-bits") return new UnknownExpression("引用返回的位表示尚未恢复");
        if (layout.Return.Shape.Kind is ShapeKind.Composite or ShapeKind.HomogeneousFloat)
            return new AggregateExpression(symbols.Display(method.ReturnType), value.Expression);
        if (IntegerProjection.Width(method.ReturnType) > 0)
            return IntegerProjection.Bits(value) is { } integer
                ? new OperationExpression(ValueOperation.IntegerCast, method.ReturnType, [integer])
                : new UnknownExpression("整数返回的位宽或高位未确定");
        return method.ReturnType == "bool" && value.Type != "bool" ? BooleanValue(value.Expression) : value.Expression;
    }
    private NativeValue Load(ulong pc, NativeValue receiver, int offset, int size, List<Statement> statements, LiftResult result, string identity)
    {
        if (receiver.Expression is IndexedArrayAddress or AddressOfExpression)
            return Location(receiver, offset, size) switch
            {
                OperationExpression { Operation: ValueOperation.ArrayElement } element => Capture(pc, size, element.Type, element, statements),
                MemberExpression member => Capture(pc, size, member.Field.Type, member, statements),
                _ => Missing()
            };
        if (layouts.ArrayElements(receiver.Type) is not null)
        {
            var length = layouts.Members(receiver.Type).Single(f => f.Name == "max_length");
            if (offset == length.Offset && size is 4 or 8)
                return Capture(pc, size, size == 4 ? "int32_t" : "int64_t", new InvocationExpression(size == 4 ? "Length" : "LongLength", receiver.Expression, [], true), statements);
            if (Location(receiver, offset, size) is OperationExpression element)
                return Capture(pc, size, element.Type, element, statements);
        }
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
            return new(new InputBits($"metadata:{slot.Reference.Slot:x}", 64), slot.Reference.ValueType, slot with { IsSlot = false });
        }
        var field = layouts.Field(receiver.Type, offset, size);
        if (field is not null)
        {
            if (field is { Name: "rgctx_data", Type: "Il2CppRGCTXData*" } &&
                sharedSemantics?.Resolve(identity) is { Kind: "runtime-context", Type: { } contextType })
            {
                field = field with { Type = contextType };
                result.Proofs.Add(new(pc, "SharedSsaRuntimeType", $"{identity}: bound generic context {contextType}; same machine load and declared field"));
            }
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
        return Missing();
        NativeValue Missing()
        {
            result.Problems.Add($"0x{pc:x}: 无法将 {receiver.Type}+0x{offset:x}/{size} 映射为字段");
            return Capture(pc, size, "unknown", new UnknownExpression($"load({receiver.Type}+0x{offset:x})"), statements);
        }
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
        foreach (var register in Arm64Registers.CallWrites.Where(r => r[0] is 'x' or 'v'))
        {
            var old = state.Registers.GetValueOrDefault(register);
            var bits = registers.Read(register.ToUpperInvariant());
            state.Registers[register] = Arm64Registers.PreservedByCall(register) >= 64 && old?.Type is "float" or "double" ?
                old with { Bits = bits } : new(bits, "unknown", new UnknownExpression($"clobber_{pc:x}_{register}"));
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
            statements.Add(new UnresolvedStatement(instruction.Address, $"raw_call 0x{target:x}; 原始操作数保留于机器码")); InvalidateCallMemory(state, instruction.Address); Clobber(state, instruction.Address); return;
        }
        if (!state.StackPointerKnown && layout.Arguments.Any(a => a.Pieces.Any(p => p.Location is StackLocation)))
        {
            result.Problems.Add($"0x{instruction.Address:x}: 调用栈参数的地址未确定");
            InvalidateCallMemory(state, instruction.Address); Clobber(state, instruction.Address); return;
        }
        var arguments = new List<NativeValue>();
        foreach (var value in layout.Arguments)
        {
            if (value.Indirect)
            { result.Problems.Add($"0x{instruction.Address:x}: 调用包含尚未接通的间接聚合参数"); InvalidateCallMemory(state, instruction.Address); Clobber(state, instruction.Address); return; }
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
        TransferCallMemory(instruction.Address, method, layout, arguments, returnBuffer, state, result);
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
                    BindAbiValue(state, ((RegisterLocation)piece.Location).Name.ToLowerInvariant(), Project(NativeValues.Slice(returned, piece.ValueOffset * 8, piece.Size * 8, layout.Return.Pieces.Count == 1 ? returnType : "native-bits")));
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
