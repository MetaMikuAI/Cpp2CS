using Cpp2CS.Facts;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

/// <summary>Cecil 引用 → 程序模型的引用（在内存中的骨架上解析，定义对象与骨架一一对应）。</summary>
internal sealed class CecilModel
{
    private readonly Dictionary<TypeDefinition, TypeDef> types = new();
    private readonly Dictionary<MethodDefinition, MethodDef> methods = new();
    private readonly Dictionary<FieldDefinition, FieldDef> fields = new();
    public MethodRef? Context { get; set; }

    public CecilModel(ProgramModel model, Skeleton skeleton)
    {
        foreach (var type in model.Types) types.Add(skeleton.Type(type), type);
        foreach (var method in model.Methods) methods.Add(skeleton.Method(method), method);
        foreach (var field in model.Fields) fields.Add(skeleton.Field(field), field);
    }

    public TypeRef Type(TypeReference type) => type switch
    {
        GenericInstanceType g => new DefinitionRef(Definition(g.ElementType), g.GenericArguments.Select(Type).ToArray()),
        ArrayType a => new ArrayRef(Type(a.ElementType), a.Rank) { IsVector = a.IsVector },
        PointerType p => new PointerRef(Type(p.ElementType)),
        ByReferenceType r => new ByRefRef(Type(r.ElementType)),
        GenericParameter p when Context is { } context => new GenericParameterRef(p.Name, p.Type == GenericParameterType.Method, p.Position)
            .Substitute(context.TypeArguments, context.MethodArguments),
        GenericParameter => throw new Unsupported($"泛型参数 {type}"),
        _ => new DefinitionRef(Definition(type), []),
    };

    private TypeDef Definition(TypeReference type) =>
        type.Resolve() is { } definition && types.TryGetValue(definition, out var found) ? found : throw new Unsupported($"无法解析类型 {type}");

    public MethodRef Method(MethodReference method)
    {
        var element = method is GenericInstanceMethod generic ? generic.ElementMethod : method;
        var definition = element.Resolve() is { } d && methods.TryGetValue(d, out var found) ? found : throw new Unsupported($"无法解析方法 {method}");
        TypeRef[] typeArguments = method.DeclaringType is GenericInstanceType g ? g.GenericArguments.Select(Type).ToArray() : [];
        TypeRef[] methodArguments = method is GenericInstanceMethod m ? m.GenericArguments.Select(Type).ToArray() : [];
        return new MethodRef(definition, typeArguments, methodArguments);
    }

    public FieldRef Field(FieldReference field) =>
        new(field.Resolve() is { } d && fields.TryGetValue(d, out var found) ? found : throw new Unsupported($"无法解析字段 {field}"), Type(field.DeclaringType));
}

internal enum StackKind { I4, I8, F, O, Struct }

/// <summary>求值栈上的值：I4 保存 32 位位型，I8 为 64 位（含 native int），F 为 double，O 为对象或托管指针地址，Struct 保存不可变的值类型字节。</summary>
internal readonly record struct StackValue(StackKind Kind, ulong Bits, byte[]? Data = null)
{
    public static StackValue I4(long value) => new(StackKind.I4, (uint)value);
    public static StackValue I8(ulong value) => new(StackKind.I8, value);
    public static StackValue F(double value) => new(StackKind.F, BitConverter.DoubleToUInt64Bits(value));
    public static StackValue O(ulong address) => new(StackKind.O, address);
    public int Int32 => unchecked((int)(uint)Bits);
    public double Double => BitConverter.UInt64BitsToDouble(Bits);
    public long Integer => Kind == StackKind.I4 ? Int32 : unchecked((long)Bits);
}

/// <summary>CIL 一侧：内存为 World 初始字节之上的覆盖层。</summary>
internal sealed class CilSide(World world) : Side(world)
{
    private readonly Dictionary<ulong, byte> overlay = new();
    private ulong temporaryTop = World.StackBase;
    public ulong Temporary(int size)
    {
        var address = temporaryTop;
        temporaryTop = (temporaryTop + (ulong)Math.Max(size, 1) + 15) & ~15UL;
        if (temporaryTop >= World.StackBase + World.StackSize / 2) throw new Unsupported("CIL 临时存储已满");
        Store(address, new byte[size]);
        return address;
    }

    /// <summary>依次调用的方法（已按运行时类型分派）。</summary>
    public List<MethodRef> Callees { get; } = [];
    /// <summary>诊断实际完成的数组读写；不参与执行结果或事件比较。</summary>
    public HashSet<Instruction>? ArrayAccesses { get; } = Environment.GetEnvironmentVariable("EXECUTION_ARRAY_COVERAGE") == "1" ? [] : null;
    /// <summary>仅供输入计划枚举：实际发生且位于 try 内的调用事件序号，不参与事件比较。</summary>
    public HashSet<int> ProtectedCallEvents { get; } = [];

    public override void Read(ulong address, Span<byte> bytes)
    {
        for (var i = 0; i < bytes.Length; i++)
        {
            var a = address + (ulong)i;
            if (overlay.TryGetValue(a, out var b)) bytes[i] = b;
            else if (World.Compared(a) || InExceptionRegion(a)) bytes[i] = World.Initial(a);
            else throw new Unsupported($"CIL 侧读取了合成区域之外的地址 0x{a:x}");
        }
    }

    protected override void Store(ulong address, ReadOnlySpan<byte> bytes)
    {
        for (var i = 0; i < bytes.Length; i++) overlay[address + (ulong)i] = bytes[i];
    }
}

/// <summary>CIL 语义抛出的异常（判空、越界、类型不符）。</summary>
internal sealed class CilThrow(TypeRef type, ulong value = 0) : Exception(type.ToString())
{
    public TypeRef Type { get; } = type;
    public ulong Object { get; set; } = value;
}

/// <summary>
/// 解释 BodyEmitter 写出的 CIL（只实现它用到的指令）。内存操作按字段布局读写与原生侧相同的合成内存；
/// 调用不进入被调方法：记录调用事件，返回值取 World 按调用序号给出的值。
/// </summary>
[ShapeModel("CIL 基本语义", Basis = "ECMA-335 第 III 部分的指令语义，由解释器逐条实现；托管对象、数组与静态字段按 L1 运行时布局放在两侧共用的合成内存里")]
internal sealed partial class CilInterpreter(CecilModel model, WorldIndex index)
{
    // 高于原生侧的指令数上限：原生能结束的执行，正确的 CIL 也能在这个步数内结束
    private const int StepLimit = 1_000_000;
    private ManagedTypes Types => index.Types;

    public CilSide Run(World world, MethodDefinition method, MethodRef tested, IReadOnlyList<StackValue> arguments)
    {
        var side = new CilSide(world);
        world.Active = side;
        try
        {
            Execute(side, method, tested, arguments);
        }
        catch (CilThrow e)
        {
            side.ThrowObject(e.Object == 0 ? side.ExceptionObject(e.Type) : e.Object);
        }
        finally
        {
            world.Active = null;
        }
        return side;
    }

    private StackValue? Execute(CilSide side, MethodDefinition method, MethodRef tested, IReadOnlyList<StackValue> arguments, bool transparent = false)
    {
        var world = side.World;
        var instructions = method.Body.Instructions;
        var positions = new Dictionary<Instruction, int>();
        for (var i = 0; i < instructions.Count; i++) positions.Add(instructions[i], i);
        var localTypes = method.Body.Variables.Select(v => model.Type(v.VariableType)).ToArray();
        var locals = localTypes.Select(t => FromBytes(t, new byte[world.StorageSize(t)])).ToArray();
        var localAddresses = new Dictionary<int, ulong>();
        var argumentTypes = StructAbi.ArgumentTypes(tested);
        var argumentAddresses = new Dictionary<int, ulong>();
        StackValue Local(int i) => localAddresses.TryGetValue(i, out var address) ? ReadValue(side, localTypes[i], address) : locals[i];
        StackValue Argument(int i) => argumentAddresses.TryGetValue(i, out var address) ? ReadValue(side, argumentTypes[i], address) : arguments[i];
        ulong LocalAddress(int i)
        {
            if (localAddresses.TryGetValue(i, out var address)) return address;
            localAddresses.Add(i, address = side.Temporary(world.StorageSize(localTypes[i])));
            WriteValue(side, localTypes[i], address, locals[i]);
            return address;
        }
        ulong ArgumentAddress(int i)
        {
            if (argumentAddresses.TryGetValue(i, out var address)) return address;
            argumentAddresses.Add(i, address = side.Temporary(world.StorageSize(argumentTypes[i])));
            WriteValue(side, argumentTypes[i], address, arguments[i]);
            side.ArgumentCopy(address, argumentTypes[i], i);
            return address;
        }
        void StoreLocal(int i, StackValue value)
        {
            locals[i] = Coerce(localTypes[i], value);
            if (localAddresses.TryGetValue(i, out var address)) WriteValue(side, localTypes[i], address, locals[i]);
        }
        int ArgIndex(object operand) => ((ParameterDefinition)operand).Index + (method.HasThis ? 1 : 0);
        var stack = new Stack<StackValue>();
        StackValue Pop() => stack.Pop();
        StackValue[] PopMany(int count)
        {
            var values = new StackValue[count];
            for (var i = count - 1; i >= 0; i--) values[i] = stack.Pop();
            return values;
        }
        var returnType = tested.Method.ReturnType.Substitute(tested.TypeArguments, tested.MethodArguments);
        var pc = 0;
        var exceptionFlow = method.Body.HasExceptionHandlers ? new CilExceptionFlow(method.Body) : null;
        var escaping = false;
        for (var steps = 0; ; steps++)
        {
            if (steps > StepLimit)
            {
                side.Diverge();
                return null;
            }
            var at = pc;
            var instruction = instructions[pc++];
            var operand = instruction.Operand;
            var callsBefore = side.CallEvents;
            try
            {
            switch (instruction.OpCode.Code)
            {
                case Code.Nop: break;
                case Code.Ldarg_0: stack.Push(Argument(0)); break;
                case Code.Ldarg_1: stack.Push(Argument(1)); break;
                case Code.Ldarg_2: stack.Push(Argument(2)); break;
                case Code.Ldarg_3: stack.Push(Argument(3)); break;
                case Code.Ldarg or Code.Ldarg_S: stack.Push(Argument(ArgIndex(operand))); break;
                case Code.Ldloc_0 or Code.Ldloc_1 or Code.Ldloc_2 or Code.Ldloc_3: stack.Push(Local(instruction.OpCode.Code - Code.Ldloc_0)); break;
                case Code.Ldloc or Code.Ldloc_S: stack.Push(Local(((VariableDefinition)operand).Index)); break;
                case Code.Stloc_0 or Code.Stloc_1 or Code.Stloc_2 or Code.Stloc_3:
                {
                    var i = instruction.OpCode.Code - Code.Stloc_0;
                    StoreLocal(i, Pop());
                    break;
                }
                case Code.Stloc or Code.Stloc_S:
                {
                    var i = ((VariableDefinition)operand).Index;
                    StoreLocal(i, Pop());
                    break;
                }
                case Code.Ldloca or Code.Ldloca_S: stack.Push(StackValue.O(LocalAddress(((VariableDefinition)operand).Index))); break;
                case Code.Ldarga or Code.Ldarga_S: stack.Push(StackValue.O(ArgumentAddress(ArgIndex(operand)))); break;
                case Code.Ldobj:
                    stack.Push(ReadValue(side, model.Type((TypeReference)operand), NotNull(Pop()))); break;
                case Code.Stobj:
                {
                    var value = Pop();
                    WriteValue(side, model.Type((TypeReference)operand), NotNull(Pop()), value);
                    break;
                }
                case Code.Initobj:
                {
                    var type = model.Type((TypeReference)operand);
                    side.Write(NotNull(Pop()), new byte[world.StorageSize(type)]);
                    break;
                }
                case Code.Ldc_I4_M1: stack.Push(StackValue.I4(-1)); break;
                case >= Code.Ldc_I4_0 and <= Code.Ldc_I4_8: stack.Push(StackValue.I4(instruction.OpCode.Code - Code.Ldc_I4_0)); break;
                case Code.Ldc_I4_S: stack.Push(StackValue.I4((sbyte)operand)); break;
                case Code.Ldc_I4: stack.Push(StackValue.I4((int)operand)); break;
                case Code.Ldc_I8: stack.Push(StackValue.I8(unchecked((ulong)(long)operand))); break;
                case Code.Ldc_R4: stack.Push(StackValue.F((float)operand)); break;
                case Code.Ldc_R8: stack.Push(StackValue.F((double)operand)); break;
                case Code.Ldnull: stack.Push(StackValue.O(0)); break;
                case Code.Ldstr: stack.Push(StackValue.O(world.String((string)operand))); break;
                case Code.Ldtoken: stack.Push(StackValue.I8(world.TypePointer(model.Type((TypeReference)operand)))); break;
                case Code.Pop: Pop(); break;
                case Code.Dup: stack.Push(stack.Peek()); break;

                case Code.Ldfld:
                {
                    var field = model.Field((FieldReference)operand);
                    var receiver = Pop();
                    var type = world.FieldType(field);
                    if (receiver.Kind == StackKind.Struct)
                        stack.Push(FromBytes(type, receiver.Data!.AsSpan(world.FieldOffset(field) - RuntimeLayout.ObjectHeaderSize, world.StorageSize(type)).ToArray()));
                    else stack.Push(ReadValue(side, type, FieldAddress(world, field, receiver)));
                    break;
                }
                case Code.Ldflda:
                {
                    var field = model.Field((FieldReference)operand);
                    stack.Push(StackValue.O(FieldAddress(world, field, Pop())));
                    break;
                }
                case Code.Stfld:
                {
                    var value = Pop();
                    var field = model.Field((FieldReference)operand);
                    WriteValue(side, world.FieldType(field), FieldAddress(world, field, Pop()), value);
                    break;
                }
                case Code.Ldsfld:
                {
                    var field = model.Field((FieldReference)operand);
                    side.RunClassConstructor(field.DeclaringType);
                    var type = world.FieldType(field);
                    // ECMA-335 III.4.15：值类型的静态字段整体读出（与 ldfld 相同的结构体表示）。
                    stack.Push(ReadValue(side, type, world.StaticAddress(field)));
                    break;
                }
                // ECMA-335 III.4.14：静态字段的地址；与 ldsfld 一样先保证类型初始化。
                case Code.Ldsflda:
                {
                    var field = model.Field((FieldReference)operand);
                    side.RunClassConstructor(field.DeclaringType);
                    stack.Push(StackValue.O(world.StaticAddress(field)));
                    break;
                }
                case Code.Stsfld:
                {
                    var field = model.Field((FieldReference)operand);
                    side.RunClassConstructor(field.DeclaringType);
                    var type = world.FieldType(field);
                    WriteValue(side, type, world.StaticAddress(field), Pop());
                    break;
                }

                case Code.Newarr:
                {
                    var length = Pop().Integer;
                    stack.Push(StackValue.O(side.NewArray(new ArrayRef(model.Type((TypeReference)operand), 1), length)));
                    break;
                }
                case Code.Ldlen:
                {
                    var array = NotNull(Pop());
                    stack.Push(StackValue.I8(side.Read64(array + RuntimeLayout.ArrayMaxLength)));
                    break;
                }
                case Code.Ldelem_Any:
                {
                    var type = model.Type((TypeReference)operand);
                    var address = Element(side, type, Pop(), Pop());
                    stack.Push(Load(type, side.ReadValue(address, world.StorageSize(type))));
                    side.ArrayAccesses?.Add(instruction);
                    break;
                }
                case Code.Stelem_Any:
                {
                    var type = model.Type((TypeReference)operand);
                    var value = Pop();
                    var address = Element(side, type, Pop(), Pop());
                    if (ManagedTypes.IsReferenceType(type) && value.Bits != 0 && !Types.IsAssignable(side.TypeOf(value.Bits), type))
                        throw new CilThrow(Types.Corlib("System.ArrayTypeMismatchException"));
                    side.WriteValue(address, Raw(type, value), world.StorageSize(type));
                    side.ArrayAccesses?.Add(instruction);
                    break;
                }
                case Code.Box:
                {
                    var type = model.Type((TypeReference)operand);
                    if (type is DefinitionRef { Definition.FullName: "System.Nullable" }) throw new Unsupported("Nullable 装箱");
                    var value = Pop();
                    var size = world.StorageSize(type);
                    var box = side.New(type, RuntimeLayout.ObjectHeaderSize + size);
                    side.RunClassConstructor(type);
                    // ECMA-335 III.4.1：box 将完整值复制到新对象，结构体不能缩成一个整数。
                    WriteValue(side, type, box + RuntimeLayout.ObjectHeaderSize, value);
                    stack.Push(StackValue.O(box));
                    break;
                }
                case Code.Isinst:
                {
                    var value = Pop();
                    var type = model.Type((TypeReference)operand);
                    stack.Push(StackValue.O(value.Bits != 0 && Types.IsAssignable(side.TypeOf(value.Bits), type) ? value.Bits : 0));
                    break;
                }
                case Code.Ldftn:
                    // 原生委托 ctor 第三个参数为 Method<M>，与 ldftn 的方法身份一一对应。
                    stack.Push(StackValue.I8(world.MethodInfo(model.Method((MethodReference)operand))));
                    break;
                case Code.Ldvirtftn:
                {
                    // ECMA-335 III.4.18：先判空，再按接收者的运行时类型解析虚方法。
                    var receiver = NotNull(Pop());
                    var target = model.Method((MethodReference)operand);
                    var implementation = target.Method.IsVirtual ? Dispatch(side, receiver, target) : target;
                    stack.Push(StackValue.I8(world.MethodInfo(implementation)));
                    break;
                }
                case Code.Newobj:
                {
                    var constructor = model.Method((MethodReference)operand);
                    if (constructor.DeclaringType is not DefinitionRef { Definition.IsValueType: false } type) throw new Unsupported("值类型的 newobj");
                    var values = PopMany(constructor.Method.Parameters.Count);
                    var layout = index.Facts.Layouts.Of(type) ?? throw new Unsupported($"对象 {type} 的布局");
                    var created = side.New(type, layout.InstanceSize);
                    side.RunClassConstructor(type);
                    InvokeAt(side, instruction, constructor, [StackValue.O(created), .. values]);
                    stack.Push(StackValue.O(created));
                    break;
                }
                case Code.Call or Code.Callvirt:
                {
                    var target = model.Method((MethodReference)operand);
                    var values = PopMany(target.Method.Parameters.Count + (target.Method.IsStatic ? 0 : 1));
                    if (instruction.OpCode.Code == Code.Callvirt) NotNull(values[0]);
                    // beforefieldinit 值类型的实例方法与构造函数不是初始化触发点（ECMA-335 II.10.5.3：只保证在首次访问静态字段之前）；
                    // 原生代码在这些调用前的显式初始化由 L3 照原样写出（MethodRecovery.Implied 不再删去它）。
                    // System.Math 的浮点内建函数对应单条 FABS/FSQRT/FRINT 指令，不访问 Math 的静态字段，不是初始化触发点。
                    if (target.Method.IsStatic && !(target.Method is { Owner.FullName: "System.Math", Name: "Abs" or "Sqrt" or "Floor" or "Ceiling" or "Truncate" or "Round", Parameters.Count: 1 }
                        or { Owner.FullName: "System.BitConverter", Name: "SingleToInt32Bits" or "Int32BitsToSingle" or "DoubleToInt64Bits" or "Int64BitsToDouble", Parameters.Count: 1 })
                        || target.Method.Name == ".ctor" && !BeforeFieldInitValue(target.DeclaringType)
                        || target.DeclaringType is DefinitionRef { Definition.IsValueType: true } && !BeforeFieldInitValue(target.DeclaringType))
                        side.RunClassConstructor(target.DeclaringType);
                    var callee = instruction.OpCode.Code == Code.Callvirt && target.Method.IsVirtual ? Dispatch(side, values[0].Bits, target) : target;
                    if (InvokeAt(side, instruction, callee, values) is { } result) stack.Push(result);
                    break;
                }

                case Code.Add: stack.Push(Arithmetic(Pop(), Pop(), (a, b) => a + b, (a, b) => a + b)); break;
                case Code.Sub: stack.Push(Arithmetic(Pop(), Pop(), (a, b) => a - b, (a, b) => a - b)); break;
                case Code.Mul: stack.Push(Arithmetic(Pop(), Pop(), (a, b) => a * b, (a, b) => a * b)); break;
                case Code.Div or Code.Div_Un: stack.Push(Divide(Pop(), Pop(), instruction.OpCode.Code == Code.Div_Un)); break;
                case Code.And: stack.Push(Arithmetic(Pop(), Pop(), (a, b) => a & b, null)); break;
                case Code.Or: stack.Push(Arithmetic(Pop(), Pop(), (a, b) => a | b, null)); break;
                case Code.Xor: stack.Push(Arithmetic(Pop(), Pop(), (a, b) => a ^ b, null)); break;
                case Code.Shl or Code.Shr or Code.Shr_Un:
                {
                    var amount = (int)Pop().Integer;
                    var value = Pop();
                    var code = instruction.OpCode.Code;
                    stack.Push(value.Kind == StackKind.I4
                        ? StackValue.I4(code == Code.Shl ? value.Int32 << amount : code == Code.Shr ? value.Int32 >> amount : (long)((uint)value.Int32 >> amount))
                        : StackValue.I8(code == Code.Shl ? value.Bits << amount : code == Code.Shr ? (ulong)((long)value.Bits >> amount) : value.Bits >> amount));
                    break;
                }
                case Code.Neg:
                {
                    var value = Pop();
                    stack.Push(value.Kind switch
                    {
                        StackKind.I4 => StackValue.I4(-value.Int32), StackKind.I8 => StackValue.I8(unchecked((ulong)-(long)value.Bits)),
                        StackKind.F => StackValue.F(-value.Double), _ => throw new Unsupported("neg 的操作数"),
                    });
                    break;
                }
                case Code.Not:
                {
                    var value = Pop();
                    stack.Push(value.Kind == StackKind.I4 ? StackValue.I4(~value.Int32) : StackValue.I8(~value.Bits));
                    break;
                }
                case Code.Ceq or Code.Clt or Code.Cgt or Code.Clt_Un or Code.Cgt_Un:
                {
                    var right = Pop();
                    var left = Pop();
                    stack.Push(StackValue.I4(Compare(instruction.OpCode.Code, left, right) ? 1 : 0));
                    break;
                }
                case Code.Conv_I1 or Code.Conv_U1 or Code.Conv_I2 or Code.Conv_U2 or Code.Conv_I4 or Code.Conv_U4 or Code.Conv_I8 or Code.Conv_U8
                    or Code.Conv_I or Code.Conv_U or Code.Conv_R4 or Code.Conv_R8 or Code.Conv_R_Un:
                    stack.Push(Convert(instruction.OpCode.Code, Pop()));
                    break;

                case Code.Br or Code.Br_S: pc = positions[(Instruction)operand]; break;
                // ECMA-335 III.3.66：无符号下标在范围内时跳到对应目标，否则落到下一条指令。
                case Code.Switch:
                {
                    var targets = (Instruction[])operand;
                    var selector = (uint)Pop().Bits;
                    if (selector < targets.Length) pc = positions[targets[selector]];
                    break;
                }
                case Code.Brtrue or Code.Brtrue_S: if (Pop().Bits != 0) pc = positions[(Instruction)operand]; break;
                case Code.Brfalse or Code.Brfalse_S: if (Pop().Bits == 0) pc = positions[(Instruction)operand]; break;
                case Code.Leave or Code.Leave_S:
                    stack.Clear(); pc = positions[(Instruction)operand]; exceptionFlow?.Leave(pc); break;
                case Code.Rethrow:
                    if (exceptionFlow is null) throw new InvalidProgramException("rethrow 没有异常处理表");
                    throw exceptionFlow.Rethrow(at);
                case Code.Endfinally:
                    stack.Clear();
                    if (exceptionFlow is null) throw new InvalidProgramException("endfinally 没有异常处理表");
                    if (exceptionFlow.EndFault(at, out var pending) is { } resumed)
                    {
                        pc = resumed.Pc;
                        if (resumed.Object is { } caught) stack.Push(StackValue.O(caught));
                    }
                    else { escaping = true; throw pending; }
                    break;
                case Code.Ret:
                {
                    StackValue? returned = ManagedTypes.IsVoid(returnType) ? null : Pop();
                    // 透明访问器（F9）不产生返回事件；返回值按结构体叶子观察（F3）
                    if (!transparent) side.Return(returned is { } value ? string.Join(", ", index.StructAbi.Observable(returnType, ToBytes(returnType, value)).Select(v => $"0x{v:x}")) : "void");
                    return returned;
                }
                case Code.Throw:
                    var thrown = NotNull(Pop());
                    throw new CilThrow(side.TypeOf(thrown), thrown);
                default:
                    throw new Unsupported($"指令 {instruction.OpCode}");
            }
            }
            catch (Exception raised) when (!escaping && raised is CilThrow or PlannedThrow)
            {
                var exception = raised is CilThrow cil ? cil : new CilThrow(side.TypeOf(((PlannedThrow)raised).Object), ((PlannedThrow)raised).Object);
                if (exception.Object == 0) exception.Object = side.ExceptionObject(exception.Type);
                stack.Clear();
                if (exceptionFlow?.Throw(at, exception, h => Types.IsAssignable(exception.Type, model.Type(h.CatchType))) is not { } transfer) throw exception;
                pc = transfer.Pc;
                if (transfer.Object is { } caught) stack.Push(StackValue.O(caught));
            }
            finally
            {
                if (exceptionFlow?.Protected(at) == true)
                    for (var call = callsBefore; call < side.CallEvents; call++) side.ProtectedCallEvents.Add(call);
            }
        }
    }

    // ECMA-335 III.3.31/3.32：整数除零及有符号溢出抛出；与 ARM64 原生除法的语义不同。
    private StackValue Divide(StackValue right, StackValue left, bool unsigned)
    {
        if (left.Kind == StackKind.F && right.Kind == StackKind.F && !unsigned)
            return Arithmetic(right, left, (_, _) => throw new InvalidOperationException(), (a, b) => a / b);
        if (left.Kind != right.Kind || left.Kind is not (StackKind.I4 or StackKind.I8)) throw new Unsupported("div 操作数类型");
        var result = CilIntegerDivision.Evaluate(left, right, unsigned);
        return result.Value ?? throw new CilThrow(Types.Corlib(result.Exception!));
    }

    private static StackValue? MathIntrinsic(string name, StackValue value, TypeRef parameter)
    {
        var single = ManagedTypes.PrimitiveName(parameter) == "Single";
        if (!single && ManagedTypes.PrimitiveName(parameter) != "Double") return null;
        var x = value.Double;
        double? result = name switch
        {
            "Abs" => single ? BitConverter.Int32BitsToSingle(BitConverter.SingleToInt32Bits((float)x) & 0x7FFFFFFF) : BitConverter.Int64BitsToDouble(BitConverter.DoubleToInt64Bits(x) & 0x7FFFFFFFFFFFFFFF),
            "Sqrt" when !single => Math.Sqrt(x),
            "Floor" when !single => Math.Floor(x),
            "Ceiling" when !single => Math.Ceiling(x),
            "Truncate" when !single => Math.Truncate(x),
            "Round" when !single => Math.Round(x, MidpointRounding.ToEven),
            _ => null,
        };
        // 负数开平方产生的 NaN 按 ARM64 的默认 NaN（ArmNaN），不用宿主 x86 的负号 NaN。
        return result is { } r ? StackValue.F(single ? (float)ArmNaN(r, x, x) : ArmNaN(r, x, x)) : null;
    }

    private static bool BeforeFieldInitValue(TypeRef type) => type is DefinitionRef { Definition: { IsValueType: true } d }
        && (d.Attributes & System.Reflection.TypeAttributes.BeforeFieldInit) != 0;

    private ulong NotNull(StackValue value) =>
        value.Bits != 0 ? value.Bits : throw new CilThrow(Types.Corlib("System.NullReferenceException"));

    /// <summary>字段地址：引用类型的字段相对对象（含对象头）；值类型的字段经指向数据的托管指针访问，减去对象头。</summary>
    private ulong FieldAddress(World world, FieldRef field, StackValue receiver)
    {
        var offset = world.FieldOffset(field);
        if (field.DeclaringType is DefinitionRef { Definition.IsValueType: true })
            return receiver.Bits + (ulong)(offset - RuntimeLayout.ObjectHeaderSize);
        return NotNull(receiver) + (ulong)offset;
    }

    private ulong Element(CilSide side, TypeRef type, StackValue indexValue, StackValue arrayValue)
    {
        var array = NotNull(arrayValue);
        var position = unchecked((ulong)indexValue.Integer);
        if (position >= side.Read64(array + RuntimeLayout.ArrayMaxLength)) throw new CilThrow(Types.Corlib("System.IndexOutOfRangeException"));
        return array + RuntimeLayout.ArrayData + position * (ulong)side.World.StorageSize(type);
    }

    /// <summary>callvirt 按接收者的运行时类型选择实现（接口方法经 interface offsets）。</summary>
    private MethodRef Dispatch(CilSide side, ulong receiver, MethodRef target)
    {
        if (side.TypeOf(receiver) is not DefinitionRef type) throw new Unsupported("数组上的虚调用");
        var slot = target.Method.Slot;
        if (target.Method.Owner.IsInterface)
        {
            var pair = type.Definition.InterfaceOffsets.FirstOrDefault(p => p.Interface.Substitute(type.Arguments, []).Equals(target.DeclaringType));
            if (pair.Interface is null) throw new Unsupported($"{type} 未实现 {target.DeclaringType}");
            slot += pair.Offset;
        }
        var implementation = WorldIndex.VTableEntry(type, slot) ?? throw new Unsupported($"{type} 的虚表槽位 {slot} 为空");
        if (implementation.Method.GenericParameters.Count != target.MethodArguments.Count)
            throw new Unsupported($"{implementation} 的泛型实参数量不匹配");
        return implementation with { MethodArguments = target.MethodArguments };
    }

    /// <summary>
    /// 记录调用并给出返回值（被调方法不执行）。RuntimeHelpers.RunClassConstructor 按运行时语义处理（不是调用，不占调用序号）：
    /// 类尚未初始化时运行静态构造，与原生侧的类初始化守卫调用 helper 相对应。
    /// 其余触发点（都对任何有静态构造的类型）：静态字段访问；call 静态方法、构造函数（派生类构造中的 base(...)）与值类型的方法；
    /// newobj 与 box 在分配之后（IL2CPP 的 Object::New 在返回新对象之前调用 Runtime::ClassInit）。引用类型的实例方法不触发。
    /// ECMA-335 II.10.5.3.1 对精确初始化的类型要求的触发点都包含在内；对 beforefieldinit 的类型只要求在首次访问静态字段之前的某个时刻，
    /// 提前也是允许的行为。IL2CPP 初始化触发点由 classinit 命令核对；分配函数与显式守卫分别承担对应类型的初始化。
    /// 例外：box 精确初始化的值类型时 IL2CPP 也会运行静态构造，CLR 不会（ECMA 规定精确初始化"只在"所列触发点）；这里随 IL2CPP。
    /// </summary>
    private StackValue? Invoke(CilSide side, MethodRef callee, StackValue[] values)
    {
        var world = side.World;
        if (callee.Method is { Name: "RunClassConstructor", Owner.FullName: "System.Runtime.CompilerServices.RuntimeHelpers" })
        {
            side.RunClassConstructor(world.TypeOfHandle(values[0].Bits));
            return null;
        }
        if (DelegateModel.IsInvoke(callee)) return InvokeDelegate(side, callee, values);
        // BitConverter 的四个按位转换由 BCL 契约定义；不产生原生调用事件，不做数值转换。
        if (callee.Method is { IsStatic: true, Owner.FullName: "System.BitConverter", Parameters.Count: 1 } conversion)
        {
            var converted = conversion.Name switch
            {
                "SingleToInt32Bits" => StackValue.I4(BitConverter.SingleToInt32Bits((float)values[0].Double)),
                "DoubleToInt64Bits" => StackValue.I8(values[0].Bits),
                "Int32BitsToSingle" => StackValue.F(BitConverter.Int32BitsToSingle(values[0].Int32)),
                "Int64BitsToDouble" => StackValue.F(BitConverter.UInt64BitsToDouble(values[0].Bits)),
                _ => (StackValue?)null,
            };
            if (converted is { } bitPattern) return bitPattern;
        }
        // System.Math 的绝对值、平方根与取整：按 IEEE 754 计算（与 ARM64 的 FABS 清符号位、FSQRT/FRINT* 相同），不是调用事件。
        if (callee.Method is { IsStatic: true, Owner.FullName: "System.Math", Parameters.Count: 1 } math && MathIntrinsic(math.Name, values[0], math.Parameters[0].Type) is { } computed)
            return computed;
        // 完全栅栏：对照在单线程中执行，栅栏不改变顺序语义（ECMA-335 I.12.6.5），原生侧的 dmb 也不产生事件。
        if (callee.Method is { Name: "MemoryBarrier", IsStatic: true, Owner.FullName: "System.Threading.Thread" }) return null;
        // 已有的无参异常构造抽象不产生调用事件；被 catch 后继续执行时也不能消耗调用序号。
        if (callee.Method is { Name: ".ctor", Parameters.Count: 0 } && Side.InExceptionRegion(values[0].Bits)) return null;
        var ordinal = side.NextCall();
        side.Callees.Add(callee);
        index.StructAbi.Signature(callee);
        var arguments = StructAbi.ArgumentTypes(callee);
        if (arguments.Length != values.Length) throw new Unsupported($"被调方法 {callee} 的实参个数");
        var rawArguments = arguments.Select((type, i) => ToBytes(type, values[i])).ToArray();
        var bits = index.StructAbi.ObservableArguments(side, arguments, rawArguments);
        if (!(callee.Method is { Name: ".ctor", Parameters.Count: 0 } && Side.InExceptionRegion(values[0].Bits)))
        {
            try { side.CallEvent(index.CodeAddress(callee), index.StructAbi.CallInputs(callee, bits), Side.IsGenericInstance(callee) ? callee : null); }
            catch (PlannedThrow e) { throw new CilThrow(side.TypeOf(e.Object), e.Object); }
        }
        index.StructAbi.WriteBack(side, callee, ordinal, rawArguments);
        var returnType = callee.Method.ReturnType.Substitute(callee.TypeArguments, callee.MethodArguments);
        return ManagedTypes.IsVoid(returnType) ? null : FromBytes(returnType, world.ReturnBytes(ordinal, returnType));
    }

    // —— 值的表示 ——

    private bool IsHandle(TypeRef type) => type.Equals(Types.RuntimeTypeHandle);

    /// <summary>内存中的位型（零扩展到 64 位）→ 栈上的值。</summary>
    public StackValue Load(TypeRef type, ulong bits)
    {
        if (IsHandle(type)) return StackValue.I8(bits);
        switch (Types.Kind(type))
        {
            case TypeKind.Bool or TypeKind.Int:
            {
                var width = Types.Bits(type);
                if (width == 64) return StackValue.I8(bits);
                var signed = ManagedTypes.IsSigned(type);
                var shift = 64 - width;
                var value = signed ? (long)(bits << shift) >> shift : (long)(bits << shift >>> shift);
                return StackValue.I4(value);
            }
            case TypeKind.Float: return StackValue.F(BitConverter.UInt32BitsToSingle((uint)bits));
            case TypeKind.Double: return StackValue.F(BitConverter.UInt64BitsToDouble(bits));
            case TypeKind.Reference: return StackValue.O(bits);
            case TypeKind.Pointer: return StackValue.I8(bits);
            default: throw new Unsupported($"类型 {type} 的值");
        }
    }

    /// <summary>栈上的值 → 按 type 存入内存的位型。</summary>
    private ulong Raw(TypeRef type, StackValue value)
    {
        if (IsHandle(type)) return value.Bits;
        return Types.Kind(type) switch
        {
            TypeKind.Bool or TypeKind.Int => Side.Mask(value.Kind == StackKind.I4 ? (ulong)(uint)value.Int32 : value.Bits, Types.Bits(type)),
            TypeKind.Float => BitConverter.SingleToUInt32Bits((float)value.Double),
            TypeKind.Double => value.Bits,
            TypeKind.Reference or TypeKind.Pointer => value.Bits,
            _ => throw new Unsupported($"类型 {type} 的值"),
        };
    }

    private StackValue Coerce(TypeRef type, StackValue value) => FromBytes(type, ToBytes(type, value));

    private static StackValue Arithmetic(StackValue right, StackValue left, Func<ulong, ulong, ulong> integer, Func<double, double, double>? floating)
    {
        if (left.Kind != right.Kind) throw new Unsupported($"运算数类别不同：{left.Kind} 与 {right.Kind}");
        return left.Kind switch
        {
            StackKind.I4 => StackValue.I4((uint)integer(left.Bits, right.Bits)),
            StackKind.I8 => StackValue.I8(integer(left.Bits, right.Bits)),
            StackKind.F when floating is not null => StackValue.F(ArmNaN(floating(left.Double, right.Double), left.Double, right.Double)),
            _ => throw new Unsupported($"{left.Kind} 上的运算"),
        };
    }

    /// <summary>
    /// 被测 CIL 的语义按目标机器 ARM64 解释，不能带入宿主 x86 的浮点细节。ARM ARM 的 FPProcessNaNs 与 FPDefaultNaN（FPCR.DN = 0，
    /// Unicorn 与 Android 的默认值）：输入有 NaN 时传播该 NaN，静默 NaN 的选择与 x86 SSE 相同（先左操作数）；由非 NaN 输入产生的 NaN
    /// （0/0、∞−∞、0×∞）是默认 NaN，即正号、只有静默位，float 为 0x7fc00000。x86 产生的是负号的 "real indefinite"（0xffc00000）。
    /// 合入 F2、F3 后的全量对照中，有两个方法把这样产生的 NaN 作为实参传出，暴露了这处宿主依赖。
    /// </summary>
    private static double ArmNaN(double result, double left, double right) =>
        double.IsNaN(result) && !double.IsNaN(left) && !double.IsNaN(right) ? BitConverter.UInt64BitsToDouble(0x7ff8000000000000) : result;

    private static bool Compare(Code code, StackValue left, StackValue right)
    {
        if (left.Kind == StackKind.F || right.Kind == StackKind.F)
        {
            double a = left.Double, b = right.Double;
            var unordered = double.IsNaN(a) || double.IsNaN(b);
            return code switch
            {
                Code.Ceq => a == b, Code.Clt => a < b, Code.Cgt => a > b,
                Code.Clt_Un => unordered || a < b, Code.Cgt_Un => unordered || a > b,
                _ => throw new Unsupported(code.ToString()),
            };
        }
        if (left.Kind == StackKind.I4 && right.Kind == StackKind.I4)
            return code switch
            {
                Code.Ceq => left.Int32 == right.Int32, Code.Clt => left.Int32 < right.Int32, Code.Cgt => left.Int32 > right.Int32,
                Code.Clt_Un => (uint)left.Int32 < (uint)right.Int32, Code.Cgt_Un => (uint)left.Int32 > (uint)right.Int32,
                _ => throw new Unsupported(code.ToString()),
            };
        if (left.Kind == StackKind.I4 || right.Kind == StackKind.I4) throw new Unsupported("int32 与 64 位值比较");
        return code switch
        {
            Code.Ceq => left.Bits == right.Bits, Code.Clt => (long)left.Bits < (long)right.Bits, Code.Cgt => (long)left.Bits > (long)right.Bits,
            Code.Clt_Un => left.Bits < right.Bits, Code.Cgt_Un => left.Bits > right.Bits,
            _ => throw new Unsupported(code.ToString()),
        };
    }

    private static StackValue Convert(Code code, StackValue value)
    {
        if (value.Kind == StackKind.F)
            return code switch
            {
                Code.Conv_R4 => StackValue.F((float)value.Double),
                Code.Conv_R8 => value,
                _ => throw new Unsupported("浮点到整数的转换"),
            };
        var integer = value.Integer;
        var unsigned = value.Kind == StackKind.I4 ? (uint)value.Int32 : value.Bits;
        return code switch
        {
            Code.Conv_I1 => StackValue.I4((sbyte)integer), Code.Conv_U1 => StackValue.I4((byte)integer),
            Code.Conv_I2 => StackValue.I4((short)integer), Code.Conv_U2 => StackValue.I4((ushort)integer),
            Code.Conv_I4 or Code.Conv_U4 => StackValue.I4((int)integer),
            Code.Conv_I8 or Code.Conv_I => StackValue.I8(unchecked((ulong)integer)),
            Code.Conv_U8 or Code.Conv_U => StackValue.I8(unsigned),
            Code.Conv_R4 => StackValue.F((float)integer),
            Code.Conv_R8 => StackValue.F(integer),
            Code.Conv_R_Un => StackValue.F(unsigned),
            _ => throw new Unsupported(code.ToString()),
        };
    }
}
