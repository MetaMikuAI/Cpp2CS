using Cpp2CS.IR;
using Cpp2CS.Abi;

namespace Cpp2CS.Native;

public sealed partial class FunctionLifter
{
    // 机器效果到有类型的表达式投影。这里不再解释助记符或 ARM64 操作数。
    private Expression? Step(Instruction instruction, NativeState state, List<Statement> statements, LiftResult result)
    {
        var effect = Arm64Effects.Lower(instruction);
        var pc = instruction.Address;
        var before = state.Copy();
        if (effect.Unsupported is not null) Reject(effect.Unsupported);
        if (effect.Call is { } invocation)
        {
            if (invocation.Target.Operation == "constant") DirectCall(instruction, state, statements, result);
            else
            {
                Reject("间接调用的托管目标未确定");
                InvalidateCallMemory(state, pc);
                Clobber(state, pc);
            }
            return null;
        }
        if (effect.Branch is { } branch)
        {
            if (branch.Operation != "constant") DelegateCall(instruction, state, statements, result);
            else if (unchecked((ulong)branch.Immediate) < result.Method.Address || unchecked((ulong)branch.Immediate) > result.Instructions[^1].Address)
            {
                DirectCall(instruction, state, statements, result);
                statements.Add(new ReturnStatement(pc, ReturnValue(result.Method, state)));
                result.Proofs.Add(new(pc, "DirectTailCall", "external branch to a known method or runtime helper; existing call semantics retained; no fallthrough"));
            }
            return null;
        }
        if (effect.Returns) statements.Add(new ReturnStatement(pc, ReturnValue(result.Method, state)));
        var condition = effect.Condition is null ? null : Predicate(effect.Condition);
        // LDP/STP 和基址写回的所有输入都来自同一份执行前状态。
        var assigned = effect.Assignments.Where(w => w.Register is not ("nzcv" or "memory"))
            .Select(w => (w.Register, Value: Evaluate(w.Value))).ToArray();
        var stored = effect.Stores.Select(s => (Store: s, Base: Evaluate(s.Address.Inputs[0]), Value: Evaluate(s.Value))).ToArray();
        foreach (var item in stored)
        {
            var offset = checked((int)item.Store.Address.Immediate);
            var size = item.Store.Value.Width / 8;
            if (item.Base.Expression is StackAddressExpression stack)
                NativeValues.StoreStack(state, stackRegion, stack.Offset + offset, item.Value, item.Store.Id);
            else if (item.Base.Expression is AddressExpression address)
                statements.Add(new StoreStatement(pc, new AddressExpression(unchecked((ulong)((long)address.Address + offset))), item.Value.Expression));
            else if (Location(item.Base, offset, size) is { } location)
            {
                var value = item.Value.Expression;
                if (location is MemberExpression member && member.Field.Type.EndsWith("_o*") && value is ConstantExpression { Value: 0 }) value = new NameExpression("null");
                statements.Add(new StoreStatement(pc, location, value));
                result.Proofs.Add(new(pc, "FieldStore", "typed field address from Clang layout; store and GC barrier remain separate operations"));
            }
            else Reject("存储地址未解析");
        }
        foreach (var (register, value) in assigned)
        {
            if (register == "sp")
            {
                if (value.Expression is StackAddressExpression stack) { state.StackOffset = stack.Offset; state.StackPointerKnown = true; }
                else { state.StackPointerKnown = false; Reject("栈指针未确定"); state.Stack = state.Stack.Invalidate($"unknown-sp:{pc:x}"); state.StackViews.Clear(); }
            }
            else state.Registers[register] = value;
        }
        foreach (var assignment in effect.Assignments.Where(w => w.Register is "nzcv" or "memory"))
        {
            if (assignment.Register == "memory") { state.Stack = state.Stack.Invalidate($"unknown-memory:{pc:x}"); state.StackViews.Clear(); }
            else
            {
                state.ComparisonKind = assignment.Value.Operation;
                state.Comparison = assignment.Value.Inputs.Length == 2 ? (Evaluate(assignment.Value.Inputs[0]), Evaluate(assignment.Value.Inputs[1])) : null;
            }
        }
        return condition;

        NativeValue Unknown(int width, string reason)
        {
            Reject(reason);
            return new(new UnknownBits($"machine:{pc:x}", reason, width), "unknown", new UnknownExpression(reason));
        }
        void Reject(string reason)
        {
            result.Problems.Add($"0x{pc:x}: {reason}");
            statements.Add(new UnresolvedStatement(pc, reason));
        }
        NativeValue Numeric(MachineValue value, ValueOperation operation, string type, params Expression[] arguments) =>
            Capture(pc, value.Width / 8, type, new OperationExpression(operation, type, arguments), statements);
        NativeValue Evaluate(MachineValue value)
        {
            var width = value.Width;
            if (value.Operation == "read") return Read(before, value.Register!);
            if (value.Operation == "constant")
            {
                if (value.Type == "address") return new(BitOps.Constant(value.Immediate, width), "address", new AddressExpression(unchecked((ulong)value.Immediate)));
                if (value.Type is "float" or "double") return new(BitOps.Constant(value.Immediate, width), value.Type,
                    new OperationExpression(ValueOperation.BitCast, value.Type, [new ConstantExpression(value.Immediate)]));
                return Constant(value.Immediate, width);
            }
            if (value.Operation == "unknown") return Unknown(width, "机器效果未确定");
            if (value.Operation == "load")
            {
                var address = value.Inputs[0];
                var receiver = Evaluate(address.Inputs[0]);
                var offset = checked((int)address.Immediate);
                if (receiver.Expression is not StackAddressExpression stack) return Load(pc, receiver, offset, width / 8, statements, result);
                var slot = stack.Offset + offset;
                var loaded = NativeValues.LoadStack(before, stackRegion, slot, width / 8);
                if (mutableStack.Any(p => slot >= p.Key && slot + width / 8 <= p.Key + layouts.Size(p.Value.Type)))
                {
                    loaded = Project(loaded);
                    return Capture(pc, width / 8, loaded.Type, loaded.Expression, statements);
                }
                return loaded;
            }
            if (value.Operation == "condition-value")
                return Numeric(value with { Width = Math.Max(8, width) }, ValueOperation.Select, "int32_t", FlagCondition((int)value.Immediate), new ConstantExpression(1), new ConstantExpression(0));
            if (value.Operation == "select")
                return Numeric(value, ValueOperation.Select, width == 32 ? "int32_t" : "int64_t", Predicate(value.Inputs[0]),
                    Evaluate(value.Inputs[1]).Expression, Evaluate(value.Inputs[2]).Expression);
            // 数组缩放寻址是 add(array, shift(sign-extend(index))) 的有类型投影。
            if (value.Operation == "add" && value.Inputs[1] is { Operation: "shift-left", Inputs: [var extended] } scale &&
                extended is { Operation: "sign-extend", Inputs: [var indexValue] } && indexValue.Width == 32)
            {
                var array = Evaluate(value.Inputs[0]);
                if (layouts.ArrayElements(array.Type) is { } elements && (1L << (int)scale.Immediate) == layouts.Size(elements.Type))
                {
                    var index = Evaluate(indexValue);
                    if (index.Type != "int32_t") return Unknown(width, "数组索引类型未确定");
                    return new(new InputBits($"indexed:{pc:x}", 64), array.Type, new IndexedArrayAddress(array.Expression, index.Expression, elements));
                }
            }
            var inputs = value.Inputs.Select(Evaluate).ToArray();
            var first = inputs[0];
            switch (value.Operation)
            {
                case "slice":
                    if (first.Expression is ConstantExpression slicedNumber && value.Immediate == 0 && width == 32)
                        return Constant(unchecked((int)slicedNumber.Value), 32);
                    return Project(NativeValues.Slice(first, checked((int)value.Immediate), width,
                        value.Inputs[0].Operation == "read" ? first.Type : null));
                case "zero-extend":
                    return first with { Bits = BitOps.Concat([first.Bits, BitOps.Constant(0, width - first.Bits.Width)]) };
                case "sign-extend":
                    if (first.Bits is ConstantBits constantBits)
                    {
                        var number = (long)constantBits.Value;
                        if ((number & (1L << (first.Bits.Width - 1))) != 0) number -= 1L << first.Bits.Width;
                        return Constant(number, width);
                    }
                    return Unknown(width, "有符号扩展的 C# 投影未接通");
                case "add": case "sub":
                {
                    var right = inputs[1];
                    var add = value.Operation == "add";
                    if (first.Expression is StackAddressExpression stack && right.Expression is ConstantExpression delta)
                    {
                        var offset = checked(stack.Offset + (add ? delta.Value : -delta.Value));
                        return new(new InputBits($"stack-address:{offset}", 64), "stack-address", new StackAddressExpression(offset));
                    }
                    if (first.Expression is AddressExpression address && right.Expression is ConstantExpression constant)
                    {
                        var sum = unchecked((ulong)((long)address.Address + (add ? constant.Value : -constant.Value)));
                        return new(BitOps.Constant(sum, 64), "address", new AddressExpression(sum));
                    }
                    if (add && right.Expression is ConstantExpression elementOffset && layouts.ArrayElements(first.Type) is { } element &&
                        Location(first, checked((int)elementOffset.Value), layouts.Size(element.Type)) is OperationExpression { Operation: ValueOperation.ArrayElement } elementAddress)
                        return new(new InputBits($"element-address:{pc:x}", 64), element.Type + "*", new AddressOfExpression(elementAddress) { RootType = first.Type });
                    if (add && right.Expression is ConstantExpression displacement &&
                        layouts.FieldAt(first.Type, checked((int)displacement.Value)) is { } field && Location(first, field.Offset, field.Size) is { } location)
                        return new(new InputBits($"field-address:{pc:x}", 64), field.Type + "*", new AddressOfExpression(location) { RootType = (first.Expression as AddressOfExpression)?.RootType ?? first.Type });
                    if (first.Type is "int32_t" or "int64_t" or "uint32_t" or "uint64_t" && (width == 32 || first.Type is "int64_t" or "uint64_t"))
                        return Numeric(value, add ? ValueOperation.Add : ValueOperation.Subtract, width == 32 ? "int32_t" : "int64_t", first.Expression, right.Expression);
                    return Unknown(width, "算术操作数类型未确定");
                }
                case "and":
                {
                    if (inputs[1].Expression is not ConstantExpression maskValue) return Unknown(width, "寄存器按位与的 C# 投影未接通");
                    var mask = unchecked((ulong)maskValue.Value);
                    if (first.Type == "bool" && mask == 1)
                    {
                        var expression = first.Expression;
                        while (expression is SliceExpression { BitOffset: 0, BitWidth: >= 8 } slice) expression = slice.Value;
                        return new(BitOps.Concat([BitOps.Slice(first.Bits, 0, 1), BitOps.Constant(0, width - 1)]), "bool", expression);
                    }
                    var bits = System.Numerics.BitOperations.PopCount(mask);
                    if (bits == 0) return Constant(0, width);
                    if (bits > width || (mask & (mask + 1)) != 0) return Unknown(width, "非连续低位掩码的 C# 投影未接通");
                    var low = Project(NativeValues.Slice(first, 0, bits));
                    return low with { Bits = bits == width ? low.Bits : BitOps.Concat([low.Bits, BitOps.Constant(0, width - bits)]) };
                }
                case "shift-right":
                {
                    var shift = checked((int)value.Immediate);
                    var low = Project(NativeValues.Slice(first, shift, width - shift));
                    return low with { Bits = shift == 0 ? low.Bits : BitOps.Concat([low.Bits, BitOps.Constant(0, shift)]) };
                }
                case "signed-to-float":
                {
                    if (first.Type is not ("int32_t" or "int64_t" or "uint32_t" or "uint64_t")) return Unknown(width, "整数转浮点的输入类型未确定");
                    var expression = first.Expression;
                    if (first.Bits.Width == 64 && first.Type is "int32_t" or "uint32_t")
                    {
                        if (BitOps.Slice(first.Bits, 32, 32) is not ConstantBits { Value.IsZero: true }) return Unknown(width, "64 位整数转换的高位未确定");
                        expression = new OperationExpression(ValueOperation.ZeroExtendWord, "int64_t", [expression]);
                    }
                    return Numeric(value, ValueOperation.SignedToFloat, value.Type!, expression, new ConstantExpression(first.Bits.Width));
                }
                case "float-divide": case "float-ceiling": case "float-to-signed-ceiling":
                    if (inputs.Any(v => v.Type != (v.Bits.Width == 32 ? "float" : "double"))) return Unknown(width, "浮点输入类型未确定");
                    return Numeric(value, value.Operation switch { "float-divide" => ValueOperation.FloatDivide, "float-ceiling" => ValueOperation.Ceiling, _ => ValueOperation.FloatToSignedCeiling }, value.Type!, inputs.Select(v => v.Expression).ToArray());
                case "reinterpret":
                    if (first.Type == value.Type) return first;
                    if (width == 64) return Unknown(width, "64 位跨寄存器组位转换的 C# 投影未接通");
                    return Numeric(value, ValueOperation.BitCast, value.Type!, first.Expression);
                default: return Unknown(width, "机器操作的 C# 投影未接通：" + value.Operation);
            }
        }
        Expression Predicate(MachineValue value)
        {
            if (value.Operation == "condition-value" || value.Operation.StartsWith("b.")) return FlagCondition((int)value.Immediate);
            if (value.Operation is not ("zero" or "nonzero")) { Reject("条件效果未支持"); return new UnknownExpression("condition"); }
            var zero = value.Operation == "zero";
            var operand = value.Inputs[0];
            if (operand is { Operation: "slice", Width: 1 })
            {
                var input = Evaluate(operand.Inputs[0]);
                if (input.Type == "bool" && operand.Immediate == 0)
                {
                    var expression = input.Expression;
                    while (expression is SliceExpression { BitOffset: 0 } slice) expression = slice.Value;
                    return new BinaryExpression(zero ? "==" : "!=", expression, new NameExpression("false"));
                }
                return new BinaryExpression(zero ? "==" : "!=", new BinaryExpression("&", input.Expression, new ConstantExpression(1L << (int)operand.Immediate)), new ConstantExpression(0));
            }
            var tested = Evaluate(operand);
            var reference = tested.Type.EndsWith("_o*") || tested.Type.EndsWith("_array*") || tested.Type == "Il2CppObject*";
            return new BinaryExpression(reference ? zero ? "is" : "is not" : zero ? "==" : "!=", tested.Expression, reference ? new NameExpression("null") : new ConstantExpression(0));
        }
        Expression FlagCondition(int code)
        {
            if (before.Comparison is not { } compare || before.ComparisonKind is not ("compare" or "compare-float"))
            { Reject("条件标志来源未确定"); return new UnknownExpression("flags"); }
            if (code is 1 or 2) return Compare(result, code == 1 ? "==" : "!=", compare.Left, compare.Right);
            if (before.ComparisonKind == "compare-float" || code is not (3 or 4 or 9 or 10 or 11 or 12 or 13 or 14) ||
                compare.Left.Type is not ("int32_t" or "uint32_t" or "int64_t" or "uint64_t") ||
                !(compare.Right.Expression is ConstantExpression || compare.Right.Type == compare.Left.Type && compare.Right.Bits.Width == compare.Left.Bits.Width))
            { Reject("整数分支的类型或位宽未确定"); return new UnknownExpression("flags"); }
            var unsigned = code is 3 or 4 or 9 or 10;
            Expression Cast(NativeValue v) => unsigned ? new OperationExpression(ValueOperation.Unsigned, compare.Left.Bits.Width == 32 ? "uint32_t" : "uint64_t", [v.Expression]) : v.Expression;
            return new BinaryExpression(code switch { 3 or 11 => ">=", 4 or 12 => "<", 9 or 13 => ">", _ => "<=" }, Cast(compare.Left), Cast(compare.Right));
        }
    }
    private static void InvalidateCallMemory(NativeState state, ulong pc)
    {
        state.Stack = state.Stack.Invalidate($"call:{pc:x}");
        state.StackViews.Clear();
    }
}
