using Cpp2CS.IR;

namespace Cpp2CS.Native;

public sealed partial class FunctionLifter
{
    private Expression? Location(NativeValue receiver, int offset, int size)
    {
        if (receiver.Expression is IndexedArrayAddress or AddressOfExpression { Target: OperationExpression { Operation: ValueOperation.ArrayElement } })
            return ArrayAddressProjection.Element(receiver, offset, size, layouts);
        if (receiver.Expression is AddressOfExpression address)
        {
            if (address.Target is not MemberExpression member) return null;
            if (offset == 0 && member.Field.Size == size) return member;
            return address.RootType is { } rootType ? Location(receiver with { Type = rootType, Expression = member.Receiver }, checked(member.Field.Offset + offset), size) : null;
        }
        if (ArrayAddressProjection.Element(receiver, offset, size, layouts) is { } element) return element;
        var field = layouts.Field(receiver.Type, offset, size);
        if (field is null) return null;
        var owner = field.DeclaringRecord.EndsWith("_Fields") ? field.DeclaringRecord[..^7] + "_o" : field.DeclaringRecord;
        managed.FieldTypes.TryGetValue((ManagedNames.SplitGeneric(symbols.Display(owner)).Name, field.Name), out var fieldType);
        return new MemberExpression(receiver.Expression, field, field.Name, fieldType);
    }
    private (string Native, string Display)? RuntimeType(Expression expression)
    {
        if (expression is MetadataExpression { IsSlot: false, Reference: { Kind: "ScriptMetadata" } array } && array.Name.EndsWith("[]_TypeInfo"))
        {
            var display = array.Name[..^9];
            var element = display[..^2];
            var nativeElement = element is "object" or "System.Object" ? "Il2CppObject*" : symbols.NativeType(element);
            if (nativeElement is null || layouts.ArrayType(nativeElement) is not { } nativeArray) return null;
            symbols.DisplayTypes.TryAdd(nativeArray, display);
            return (nativeArray + "*", display);
        }
        if (expression is not MetadataExpression { IsSlot: false, Reference: { Kind: "ScriptMetadata" } reference } ||
            !reference.Name.EndsWith("_TypeInfo") || !reference.Type.EndsWith("_c*")) return null;
        var native = reference.Type[..^3] + "_o*";
        return (native, symbols.DisplayTypes.GetValueOrDefault(native.TrimEnd('*'), reference.Name[..^9]));
    }
    private void RuntimeCall(Instruction instruction, RuntimeHelper helper, NativeState state, List<Statement> statements, LiftResult result)
    {
        var pc = instruction.Address;
        var first = Read(state, "x0"); var second = Read(state, "x1");
        string? name = null; string? returnType = null;
        Expression[] arguments = [];
        switch (helper.Kind)
        {
            case "ThrowNullReference": statements.Add(new ThrowStatement(pc, "System.NullReferenceException")); break;
            case "ThrowIndexOutOfRange": statements.Add(new ThrowStatement(pc, "System.IndexOutOfRangeException")); break;
            case "RaiseException": name = "Runtime.RaiseException"; arguments = [first.Expression]; break;
            case "RethrowException": name = "Runtime.RethrowException"; arguments = [first.Expression]; break;
            case "CreateArrayTypeMismatchException": name = "Runtime.CreateArrayTypeMismatchException"; returnType = "Il2CppException*"; break;
            case "ThrowInvalidCast": name = "Runtime.ThrowInvalidCast"; arguments = [first.Expression]; break;
            case "InitializeMetadata":
                if (first.Expression is not MetadataExpression { IsSlot: true }) Reject("元数据初始化参数未解析");
                name = "Runtime.InitializeMetadata"; arguments = [first.Expression]; break;
            case "InitializeClass":
                if (RuntimeType(first.Expression) is null) Reject("类初始化目标类型未解析");
                name = "Runtime.InitializeClass"; arguments = [first.Expression]; break;
            case "WriteBarrier":
                if (first.Expression is not AddressOfExpression) Reject("GC 写屏障的槽位地址未解析");
                name = "Runtime.GCWriteBarrier"; arguments = [first.Expression]; break;
            case "IsInstance":
                if (RuntimeType(second.Expression) is not { } castType)
                {
                    if (second.Type == "Il2CppClass*") { name = "Runtime.IsInstance"; arguments = [first.Expression, second.Expression]; returnType = "Il2CppObject*"; }
                    else Reject("类型检查的目标类型未解析");
                    break;
                }
                name = $"Runtime.IsInstance<{castType.Display}>"; arguments = [first.Expression]; returnType = castType.Native; break;
            case "AllocateArray":
                if (RuntimeType(first.Expression) is not { } arrayType || !arrayType.Display.EndsWith("[]")) { Reject("数组分配类型未解析"); break; }
                var length = Read(state, "w1");
                var arrayValue = Capture(pc, 8, arrayType.Native, new OperationExpression(ValueOperation.NewArray, arrayType.Display[..^2], [length.Expression]), statements);
                Clobber(state, pc);
                BindAbiValue(state, "x0", arrayValue);
                result.Proofs.Add(new(pc, "RuntimeHelper", helper.Evidence));
                return;
            case "Allocate":
                if (RuntimeType(first.Expression) is not { } newType) { Reject("分配对象的类型未解析"); break; }
                name = $"Runtime.Allocate<{newType.Display}>"; returnType = newType.Native; break;
            case "Box":
                if (RuntimeType(first.Expression) is not { } boxed) { Reject("装箱类型未解析"); break; }
                var size = boxed.Native switch
                {
                    "System_Int64_o*" or "System_UInt64_o*" or "System_Double_o*" => 8,
                    "System_Int32_o*" or "System_UInt32_o*" or "System_Single_o*" => 4,
                    "System_Int16_o*" or "System_UInt16_o*" or "System_Char_o*" => 2,
                    "System_Byte_o*" or "System_SByte_o*" or "System_Boolean_o*" => 1,
                    _ => 0
                };
                if (size == 0 || second.Expression is not StackAddressExpression stack ||
                    !state.StackViews.TryGetValue(stack.Offset, out var value) ||
                    value.Bits.Width != size * 8 || state.Stack.Load(new(stackRegion, stack.Offset), size) != value.Bits)
                { Reject("装箱源的完整值及存储宽度尚未确认"); break; }
                name = $"Runtime.Box<{boxed.Display}>"; arguments = [value.Expression]; returnType = "Il2CppObject*";
                result.Proofs.Add(new(pc, "BoxValueSnapshot", $"{boxed.Display}; {size} bytes from stack {stack.Offset}; value copied at call, never treat x1 address as payload"));
                break;
            default: Reject("未实现的运行时摘要 " + helper.Kind); break;
        }
        var variable = returnType is null ? null : $"call_{pc:x}";
        if (name is not null) statements.Add(new CallStatement(pc, name, arguments, variable, returnType, false, null, NoReturn: helper.NoReturn));
        result.Proofs.Add(new(pc, "RuntimeHelper", helper.Evidence));
        if (!Arm64Calls.PreservesCallerStack(helper.Kind)) InvalidateCallMemory(state, pc);
        Clobber(state, pc);
        if (variable is not null) BindAbiValue(state, "x0", new(new InputBits(variable, 64), returnType!, new NameExpression(variable)));
        void Reject(string reason)
        {
            result.Problems.Add($"0x{pc:x}: {reason}");
            statements.Add(new UnresolvedStatement(pc, reason));
        }
    }
}
