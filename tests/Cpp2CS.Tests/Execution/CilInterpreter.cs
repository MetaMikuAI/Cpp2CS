using Cpp2CS.Model;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

internal sealed class ExecutionBudget(int steps)
{
    public int Remaining { get; set; } = steps;
}

internal enum StackKind { I4, I8, F, O, Struct }

/// <summary>求值栈上的值：I4 保存 32 位位型，I8 为 64 位（含 native int），F 为 double，O 为对象或托管指针地址，Struct 保存不可变的值类型字节。</summary>
/// <summary>Single：F 上的 float32。双方都是 float32 的运算结果仍是 float32：IL2CPP 和 CLR 都这样编译，ECMA-335 只是允许更高精度。</summary>
internal readonly record struct StackValue(StackKind Kind, ulong Bits, byte[]? Data = null, bool Single = false)
{
    // 仅供显式判空溯源；数值运算与转换不传播这些标记。
    public bool NullLiteral { get; init; }
    public bool TestedNull { get; init; }
    public static StackValue I4(long value) => new(StackKind.I4, (uint)value);
    public static StackValue I8(ulong value) => new(StackKind.I8, value);
    public static StackValue F(double value) => new(StackKind.F, BitConverter.DoubleToUInt64Bits(value));
    public static StackValue F32(float value) => new(StackKind.F, BitConverter.DoubleToUInt64Bits(value), null, true);
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
    public bool Recorded { get; set; }
    public TypeRef Type { get; } = type;
    public ulong Object { get; set; } = value;
    public ConversionFailure? Conversion { get; init; }
    public NullCheckSource NullCheck { get; init; }
    public TraceEvent? Event { get; set; }
    public bool Caught { get; set; }
}

/// <summary>CIL 解释器：托管字段存储、事件、异常流及有预算的调用执行。</summary>
[ShapeModel("CIL 基本语义", Basis = "ECMA-335 第 III 部分的指令语义；未知指令和未建模行为返回无法判定")]
internal sealed partial class CilInterpreter(CecilModel model, WorldIndex index)
{
    public int StepLimit { get; init; } = 1_000_000;
    public ExecutionCoverage? Coverage { get; set; }
    public ExecutionBudget? CaseBudget { get; set; }
    private ExecutionBudget budget = new(0);
    private ManagedTypes Types => index.Types;

    public CilSide Run(World world, MethodDefinition method, MethodRef tested, IReadOnlyList<StackValue> arguments)
    {
        budget = CaseBudget ?? new ExecutionBudget(StepLimit);
        var side = new CilSide(world);
        world.Active = side;
        try
        {
            Execute(side, method, tested, arguments);
        }
        catch (CilThrow e)
        {
            side.ThrowObject(e.Object == 0 ? side.ExceptionObject(e.Type) : e.Object, !e.Recorded, e.Caught ? null : e.Event);
        }
        finally
        {
            world.Active = null;
        }
        return side;
    }

    private StackValue? Execute(CilSide side, MethodDefinition method, MethodRef tested, IReadOnlyList<StackValue> arguments, bool transparent = false, MethodBody? ownBody = null)
    {
        var context = model.InContext(tested);
        var world = side.World;
        var executed = ownBody ?? method.Body;
        var instructions = executed.Instructions;
        var positions = new Dictionary<Instruction, int>();
        for (var i = 0; i < instructions.Count; i++) positions.Add(instructions[i], i);
        var localTypes = executed.Variables.Select(v => context.Type(v.VariableType)).ToArray();
        var locals = localTypes.Select(t => FromBytes(t, new byte[world.StorageSize(t)])).ToArray();
        var localAddresses = new Dictionary<int, ulong>();
        var argumentTypes = ManagedValues.ArgumentTypes(tested);
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
        var exceptionFlow = executed.HasExceptionHandlers ? new CilExceptionFlow(executed) : null;
        var escaping = false;
        TypeRef? constraint = null;
        var nullGuard = false;
        int? explicitNullThrow = null;
        for (var steps = 0; ; steps++)
        {
            if (--budget.Remaining < 0)
            {
                throw new Unsupported("CIL 步数预算耗尽", ComparisonReason.StepBudget);
            }
            var at = pc;
            var instruction = instructions[pc++];
            if (explicitNullThrow != at) explicitNullThrow = null;
            if (instruction.OpCode.Code is not (Code.Nop or Code.Br or Code.Br_S or Code.Call or Code.Callvirt or Code.Pop or Code.Newobj or Code.Throw))
                nullGuard = false;
            Coverage?.Visit(method, instruction);
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
                case Code.Starg or Code.Starg_S:
                {
                    var position = ArgIndex(operand);
                    WriteValue(side, argumentTypes[position], ArgumentAddress(position), Pop());
                    break;
                }
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
                    stack.Push(ReadValue(side, context.Type((TypeReference)operand), NotNull(Pop()))); break;
                case Code.Stobj:
                {
                    var value = Pop();
                    WriteValue(side, context.Type((TypeReference)operand), NotNull(Pop()), value);
                    break;
                }
                case Code.Ldind_I1 or Code.Ldind_U1 or Code.Ldind_I2 or Code.Ldind_U2 or Code.Ldind_I4 or Code.Ldind_U4 or Code.Ldind_I8
                    or Code.Ldind_I or Code.Ldind_R4 or Code.Ldind_R8 or Code.Ldind_Ref:
                    stack.Push(ReadValue(side, Primitive(instruction.OpCode.Code), NotNull(Pop()))); break;
                case Code.Stind_I1 or Code.Stind_I2 or Code.Stind_I4 or Code.Stind_I8 or Code.Stind_I or Code.Stind_R4 or Code.Stind_R8 or Code.Stind_Ref:
                {
                    var value = Pop();
                    WriteValue(side, Primitive(instruction.OpCode.Code), NotNull(Pop()), value);
                    break;
                }
                case Code.Readonly or Code.Volatile: break;
                case Code.Conv_Ovf_I when stack.Peek().Kind is StackKind.I4 or StackKind.I8:
                    // ECMA-335 III.3.30：有符号整数转成 64 位 native int 不会溢出。
                    stack.Push(StackValue.I8(unchecked((ulong)Pop().Integer))); break;
                case Code.Sizeof:
                {
                    var type = context.Type((TypeReference)operand);
                    if (Types.Kind(type) == TypeKind.Struct) throw new Unsupported("sizeof 聚合类型需要实际布局");
                    stack.Push(StackValue.I4(world.StorageSize(type)));
                    break;
                }
                case Code.Initobj:
                {
                    var type = context.Type((TypeReference)operand);
                    side.Write(NotNull(Pop()), new byte[world.StorageSize(type)]);
                    break;
                }
                case Code.Ldc_I4_M1: stack.Push(StackValue.I4(-1)); break;
                case >= Code.Ldc_I4_0 and <= Code.Ldc_I4_8: stack.Push(StackValue.I4(instruction.OpCode.Code - Code.Ldc_I4_0)); break;
                case Code.Ldc_I4_S: stack.Push(StackValue.I4((sbyte)operand)); break;
                case Code.Ldc_I4: stack.Push(StackValue.I4((int)operand)); break;
                case Code.Ldc_I8: stack.Push(StackValue.I8(unchecked((ulong)(long)operand))); break;
                case Code.Ldc_R4: stack.Push(StackValue.F32((float)operand)); break;
                case Code.Ldc_R8: stack.Push(StackValue.F((double)operand)); break;
                case Code.Ldnull: stack.Push(StackValue.O(0) with { NullLiteral = true }); break;
                case Code.Ldstr: stack.Push(StackValue.O(world.String((string)operand))); break;
                case Code.Ldtoken:
                    stack.Push(StackValue.I8(operand switch
                    {
                        FieldReference token => world.FieldInfo(context.Field(token)),
                        MethodReference target => world.MethodInfo(context.Method(target)),
                        _ => world.TypePointer(context.Type((TypeReference)operand)),
                    }));
                    break;
                case Code.Pop: Pop(); break;
                case Code.Dup: stack.Push(stack.Peek()); break;

                case Code.Ldfld:
                {
                    var field = context.Field((FieldReference)operand);
                    var receiver = Pop();
                    var type = world.FieldType(field);
                    if (receiver.Kind == StackKind.Struct)
                        stack.Push(FromBytes(type, receiver.Data!.AsSpan(world.FieldOffset(field) - StorageLayout.ObjectHeaderSize, world.StorageSize(type)).ToArray()));
                    else stack.Push(ReadValue(side, type, FieldAddress(world, field, receiver)));
                    // Roslyn 认定捕获的 this 和外层闭包不为空，不再判空（callvirt 换成 call）；这种输入在 C# 的语义里不会出现。
                    break;
                }
                case Code.Ldflda:
                {
                    var field = context.Field((FieldReference)operand);
                    stack.Push(StackValue.O(FieldAddress(world, field, Pop())));
                    break;
                }
                case Code.Stfld:
                {
                    var value = Pop();
                    var field = context.Field((FieldReference)operand);
                    WriteValue(side, world.FieldType(field), FieldAddress(world, field, Pop()), value);
                    break;
                }
                case Code.Ldsfld:
                {
                    var field = context.Field((FieldReference)operand);
                    world.PrepareStatic(field);
                    side.RunClassConstructor(field.DeclaringType);
                    var type = world.FieldType(field);
                    // ECMA-335 III.4.15：值类型的静态字段整体读出（与 ldfld 相同的结构体表示）。
                    stack.Push(ReadValue(side, type, world.StaticAddress(field)));
                    break;
                }
                // ECMA-335 III.4.14：静态字段的地址；与 ldsfld 一样先保证类型初始化。
                case Code.Ldsflda:
                {
                    var field = context.Field((FieldReference)operand);
                    world.PrepareStatic(field);
                    side.RunClassConstructor(field.DeclaringType);
                    stack.Push(StackValue.O(world.StaticAddress(field)));
                    break;
                }
                case Code.Stsfld:
                {
                    var field = context.Field((FieldReference)operand);
                    world.PrepareStatic(field);
                    side.RunClassConstructor(field.DeclaringType);
                    var type = world.FieldType(field);
                    WriteValue(side, type, world.StaticAddress(field), Pop());
                    break;
                }

                case Code.Newarr:
                {
                    var length = Pop().Integer;
                    stack.Push(StackValue.O(side.NewArray(new ArrayRef(context.Type((TypeReference)operand), 1), length)));
                    break;
                }
                case Code.Ldlen:
                {
                    var array = NotNull(Pop());
                    stack.Push(StackValue.I8(side.Read64(array + StorageLayout.ArrayMaxLength)));
                    break;
                }
                // ECMA-335 III.4.9：ldelema 返回元素存储地址，仍检查 null、下标及精确元素类型。
                case Code.Ldelema:
                {
                    var type = context.Type((TypeReference)operand);
                    var position = Pop();
                    var array = Pop();
                    var address = Element(side, type, position, array);
                    if (side.TypeOf(array.Bits) is not ArrayRef actual || !actual.Element.Equals(type))
                        throw new CilThrow(Types.Corlib("System.ArrayTypeMismatchException"));
                    stack.Push(StackValue.O(address));
                    side.ArrayAccesses?.Add(instruction);
                    break;
                }
                case Code.Ldelem_Any:
                {
                    var type = context.Type((TypeReference)operand);
                    var address = Element(side, type, Pop(), Pop());
                    stack.Push(ReadValue(side, type, address));
                    side.ArrayAccesses?.Add(instruction);
                    break;
                }
                case Code.Ldelem_I1 or Code.Ldelem_U1 or Code.Ldelem_I2 or Code.Ldelem_U2 or Code.Ldelem_I4 or Code.Ldelem_U4 or Code.Ldelem_I8
                    or Code.Ldelem_I or Code.Ldelem_R4 or Code.Ldelem_R8 or Code.Ldelem_Ref:
                {
                    var type = Primitive(instruction.OpCode.Code);
                    stack.Push(ReadValue(side, type, Element(side, type, Pop(), Pop())));
                    break;
                }
                case Code.Stelem_I1 or Code.Stelem_I2 or Code.Stelem_I4 or Code.Stelem_I8 or Code.Stelem_I or Code.Stelem_R4 or Code.Stelem_R8:
                {
                    var type = Primitive(instruction.OpCode.Code);
                    var value = Pop();
                    WriteValue(side, type, Element(side, type, Pop(), Pop()), value);
                    break;
                }
                case Code.Stelem_Ref:
                {
                    // ECMA-335 III.4.27：按数组实际的元素类型检查。
                    var type = Primitive(Code.Stelem_Ref);
                    var value = Pop();
                    var position = Pop();
                    var array = Pop();
                    var address = Element(side, type, position, array);
                    if (value.Bits != 0 && side.TypeOf(array.Bits) is ArrayRef { Element: var element } && !Types.IsAssignable(side.TypeOf(value.Bits), element))
                        throw new CilThrow(Types.Corlib("System.ArrayTypeMismatchException"));
                    WriteValue(side, type, address, value);
                    break;
                }
                case Code.Stelem_Any:
                {
                    var type = context.Type((TypeReference)operand);
                    var value = Pop();
                    var address = Element(side, type, Pop(), Pop());
                    if (ManagedTypes.IsReferenceType(type) && value.Bits != 0 && !Types.IsAssignable(side.TypeOf(value.Bits), type))
                        throw new CilThrow(Types.Corlib("System.ArrayTypeMismatchException"));
                    WriteValue(side, type, address, value);
                    side.ArrayAccesses?.Add(instruction);
                    break;
                }
                case Code.Box:
                {
                    var type = context.Type((TypeReference)operand);
                    if (type is DefinitionRef { Definition.FullName: "System.Nullable" }) throw new Unsupported("Nullable 装箱");
                    // ECMA-335 III.4.1：box 是否分配取决于 T 的确切类型，不透明的 T 只有运行时才知道，这里无从选择。
                    if (type.ContainsGenericParameter()) throw new Unsupported("完全共享泛型的不透明值");
                    var value = Pop();
                    // box !T 在 T 为引用类型时保留原引用，不创建装箱对象。
                    if (ManagedTypes.IsReferenceType(type)) { stack.Push(StackValue.O(value.Bits)); break; }
                    var size = world.StorageSize(type);
                    var box = side.New(type, StorageLayout.ObjectHeaderSize + size);
                    side.RunClassConstructor(type);
                    // ECMA-335 III.4.1：box 将完整值复制到新对象，结构体不能缩成一个整数。
                    WriteValue(side, type, box + StorageLayout.ObjectHeaderSize, value);
                    stack.Push(StackValue.O(box));
                    break;
                }
                case Code.Castclass:
                case Code.Isinst:
                case Code.Unbox_Any when ManagedTypes.IsReferenceType(context.Type((TypeReference)operand)):
                {
                    var value = Pop();
                    var type = context.Type((TypeReference)operand);
                    var compatible = value.Bits == 0 || Types.IsAssignable(side.TypeOf(value.Bits), type);
                    if (!compatible && instruction.OpCode.Code != Code.Isinst)
                        throw new CilThrow(Types.Corlib("System.InvalidCastException")) { Conversion = new(value.Bits, type) };
                    stack.Push(StackValue.O(compatible ? value.Bits : 0));
                    break;
                }
                case Code.Unbox:
                case Code.Unbox_Any:
                {
                    var instance = NotNull(Pop());
                    var target = context.Type((TypeReference)operand);
                    var actual = side.TypeOf(instance);
                    if (!ManagedTypes.Underlying(actual).Equals(ManagedTypes.Underlying(target)))
                        throw new CilThrow(Types.Corlib("System.InvalidCastException")) { Conversion = new(instance, target) };
                    if (target is DefinitionRef { Definition.FullName: "System.Nullable" }) throw new Unsupported("Nullable 拆箱");
                    stack.Push(instruction.OpCode.Code == Code.Unbox ? StackValue.I8(instance + StorageLayout.ObjectHeaderSize)
                        : ReadValue(side, target, instance + StorageLayout.ObjectHeaderSize));
                    break;
                }
                case Code.Ldftn:
                    stack.Push(StackValue.I8(world.MethodInfo(context.Method((MethodReference)operand))));
                    break;
                case Code.Ldvirtftn:
                {
                    // ECMA-335 III.4.18：先判空，再按接收者的运行时类型解析虚方法。
                    var receiver = NotNull(Pop());
                    var target = context.Method((MethodReference)operand);
                    var implementation = target.Method.IsVirtual ? Dispatch(side, receiver, target) : target;
                    stack.Push(StackValue.I8(world.MethodInfo(implementation)));
                    break;
                }
                case Code.Newobj:
                {
                    var constructor = context.Method((MethodReference)operand);
                    if (constructor.DeclaringType is not DefinitionRef type) throw new Unsupported("newobj 的声明类型");
                    var values = PopMany(constructor.Method.Parameters.Count);
                    if (type.Definition.IsValueType)
                    {
                        // newobj 为值类型创建零初始化的临时存储，以其地址调用构造，再把值压栈。
                        var temporary = side.Temporary(world.StorageSize(type));
                        side.RunClassConstructor(type);
                        InvokeAt(side, instruction, constructor, [StackValue.O(temporary), .. values]);
                        stack.Push(ReadValue(side, type, temporary));
                        break;
                    }
                    var layout = index.Layouts.Of(type) ?? throw new Unsupported($"对象 {type} 的布局");
                    if (nullGuard && constructor.Method.Parameters.Count == 0
                        && type.Equals(Types.Corlib("System.NullReferenceException"))
                        && pc < instructions.Count && instructions[pc].OpCode.Code == Code.Throw)
                        explicitNullThrow = pc;
                    nullGuard = false;
                    var created = side.New(type, layout.InstanceSize);
                    side.RunClassConstructor(type);
                    InvokeAt(side, instruction, constructor, [StackValue.O(created), .. values]);
                    stack.Push(StackValue.O(created));
                    break;
                }
                case Code.Call or Code.Callvirt:
                {
                    if (((MethodReference)operand).Resolve().IsPInvokeImpl) throw new Unsupported("P/Invoke 不属于托管执行模型");
                    var target = context.Method((MethodReference)operand);
                    var values = PopMany(target.Method.Parameters.Count + (target.Method.IsStatic ? 0 : 1));
                    // 前缀只作用于这一条调用（ECMA-335 III.2.1）。先取走：下面可能抛异常，处理块里的调用不能再受它影响。
                    var constrainedTo = constraint;
                    constraint = null;
                    if (instruction.OpCode.Code == Code.Callvirt) NotNull(values[0], NullCheckSource.CallReceiver);
                    // 约束到引用类型时，指针先解引用，再按 callvirt 调用，空引用要抛异常（ECMA-335 III.2.1、III.4.2）。
                    if (constrainedTo is { } dereferenced && ManagedTypes.IsReferenceType(dereferenced))
                    {
                        values[0] = ReadValue(side, dereferenced, values[0].Bits);
                        NotNull(values[0], NullCheckSource.CallReceiver);
                    }
                    if (side.RuntimeTypeReturn(target, values.Select(v => v.Bits).ToArray()) is { } reflected)
                    {
                        stack.Push(Load(target.Method.ReturnType, reflected));
                        break;
                    }
                    // beforefieldinit 值类型的实例方法与构造函数不是初始化触发点（ECMA-335 II.10.5.3：只保证在首次访问静态字段之前）。
                    // System.Math 的浮点内建函数对应单条 FABS/FSQRT/FRINT 指令，不访问 Math 的静态字段，不是初始化触发点。
                    if (target.Method.IsStatic && (target.Method.Owner.Attributes & System.Reflection.TypeAttributes.BeforeFieldInit) == 0 && !(target.Method is { Owner.FullName: "System.Math", Name: "Abs" or "Sqrt" or "Floor" or "Ceiling" or "Truncate" or "Round", Parameters.Count: 1 }
                        or { Owner.FullName: "System.BitConverter", Name: "SingleToInt32Bits" or "Int32BitsToSingle" or "DoubleToInt64Bits" or "Int64BitsToDouble", Parameters.Count: 1 })
                        || target.Method.Name == ".ctor" && !BeforeFieldInitValue(target.DeclaringType)
                        || target.DeclaringType is DefinitionRef { Definition.IsValueType: true } && !BeforeFieldInitValue(target.DeclaringType))
                        side.RunClassConstructor(target.DeclaringType);
                    MethodRef callee;
                    if (constrainedTo is { } thisType) callee = Constrained(side, thisType, target, values);
                    else callee = instruction.OpCode.Code == Code.Callvirt && target.Method.IsVirtual ? Dispatch(side, values[0].Bits, target) : target;
                    if (InvokeAt(side, instruction, callee, values) is { } result) stack.Push(result);
                    break;
                }
                case Code.Constrained: constraint = context.Type((TypeReference)operand); break;

                case Code.Add_Ovf or Code.Add_Ovf_Un or Code.Sub_Ovf or Code.Sub_Ovf_Un or Code.Mul_Ovf or Code.Mul_Ovf_Un:
                {
                    var right = Pop(); var left = Pop();
                    if (left.Kind != right.Kind || left.Kind is not (StackKind.I4 or StackKind.I8)) throw new Unsupported("溢出算术的操作数类别");
                    var width = left.Kind == StackKind.I4 ? 32 : 64;
                    var unsigned = instruction.OpCode.Code is Code.Add_Ovf_Un or Code.Sub_Ovf_Un or Code.Mul_Ovf_Un;
                    System.Numerics.BigInteger Number(StackValue v) => unsigned ? new(v.Bits) : new(v.Integer);
                    var x = Number(left); var y = Number(right);
                    var result = instruction.OpCode.Code switch { Code.Add_Ovf or Code.Add_Ovf_Un => x + y, Code.Sub_Ovf or Code.Sub_Ovf_Un => x - y, _ => x * y };
                    var min = unsigned ? System.Numerics.BigInteger.Zero : -(System.Numerics.BigInteger.One << (width - 1));
                    var max = (System.Numerics.BigInteger.One << (unsigned ? width : width - 1)) - 1;
                    if (result < min || result > max) throw new CilThrow(Types.Corlib("System.OverflowException"));
                    var bits = (ulong)(result & ((System.Numerics.BigInteger.One << width) - 1));
                    stack.Push(width == 32 ? StackValue.I4((int)bits) : StackValue.I8(bits));
                    break;
                }
                case Code.Add: stack.Push(Arithmetic(Pop(), Pop(), (a, b) => a + b, (a, b) => a + b)); break;
                case Code.Sub: stack.Push(Arithmetic(Pop(), Pop(), (a, b) => a - b, (a, b) => a - b)); break;
                case Code.Mul: stack.Push(Arithmetic(Pop(), Pop(), (a, b) => a * b, (a, b) => a * b)); break;
                case Code.Div or Code.Div_Un: stack.Push(Divide(Pop(), Pop(), instruction.OpCode.Code == Code.Div_Un)); break;
                case Code.Rem or Code.Rem_Un: stack.Push(Divide(Pop(), Pop(), instruction.OpCode.Code == Code.Rem_Un, remainder: true)); break;
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
                        StackKind.F => value.Single ? StackValue.F32(-(float)value.Double) : StackValue.F(-value.Double), _ => throw new Unsupported("neg 的操作数"),
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
                    var compared = Compare(instruction.OpCode.Code, left, right);
                    stack.Push(StackValue.I4(compared ? 1 : 0) with
                    { TestedNull = instruction.OpCode.Code == Code.Ceq && left.Kind == StackKind.O && right.Kind == StackKind.O
                        && (left.NullLiteral || right.NullLiteral) && compared });
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
                    Coverage?.Branch(method, instruction, selector < targets.Length ? (int)selector : targets.Length);
                    if (selector < targets.Length) pc = positions[targets[selector]];
                    break;
                }
                case Code.Beq or Code.Beq_S or Code.Bne_Un or Code.Bne_Un_S or Code.Bge or Code.Bge_S or Code.Bgt or Code.Bgt_S or Code.Ble or Code.Ble_S or Code.Blt or Code.Blt_S
                    or Code.Bge_Un or Code.Bge_Un_S or Code.Bgt_Un or Code.Bgt_Un_S or Code.Ble_Un or Code.Ble_Un_S or Code.Blt_Un or Code.Blt_Un_S:
                {
                    var right = Pop();
                    var left = Pop();
                    var taken = Branches(instruction.OpCode.Code, left, right);
                    Coverage?.Branch(method, instruction, taken ? 1 : 0);
                    if (taken) pc = positions[(Instruction)operand];
                    break;
                }
                case Code.Brtrue or Code.Brtrue_S or Code.Brfalse or Code.Brfalse_S:
                {
                    var value = Pop();
                    var taken = (value.Bits != 0) == (instruction.OpCode.Code is Code.Brtrue or Code.Brtrue_S);
                    Coverage?.Branch(method, instruction, taken ? 1 : 0);
                    if (taken) pc = positions[(Instruction)operand];
                    // 仅跟踪当前方法实际走过的空引用分支；之后只容许跳板与调用。
                    nullGuard = depth == 0 && (value is { Kind: StackKind.O, Bits: 0 } || value.TestedNull == true);
                    break;
                }
                case Code.Leave or Code.Leave_S:
                    stack.Clear();
                    pc = positions[(Instruction)operand];
                    if (exceptionFlow is not null) pc = exceptionFlow.Leave(at, pc);
                    break;
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
                    else { escaping = true; throw pending!; }
                    break;
                case Code.Ret:
                {
                    StackValue? returned = ManagedTypes.IsVoid(returnType) ? null : Pop();
                    if (!transparent) side.Return(returned is { } value ? string.Join(", ", index.ManagedValues.Observable(returnType, ToBytes(returnType, value)).Select(v => $"0x{v:x}")) : "void");
                    return returned;
                }
                case Code.Throw:
                    var thrown = NotNull(Pop());
                    throw new CilThrow(side.TypeOf(thrown), thrown) { NullCheck = explicitNullThrow == at ? NullCheckSource.ExplicitBranch : NullCheckSource.None };
                default:
                    throw new Unsupported($"指令 {instruction.OpCode}");
            }
            }
            catch (Exception raised) when (!escaping && raised is CilThrow or PlannedThrow)
            {
                explicitNullThrow = null;
                nullGuard = false;
                var exception = raised is CilThrow cil ? cil : new CilThrow(side.TypeOf(((PlannedThrow)raised).Object), ((PlannedThrow)raised).Object);
                if (exception.Object == 0) exception.Object = side.ExceptionObject(exception.Type);
                if (!exception.Recorded)
                {
                    exception.Event = side.Event($"throw {exception.Type} @0x{exception.Object:x}", TraceEventKind.Throw, exception.Conversion, exception.NullCheck);
                    exception.Recorded = true;
                }
                stack.Clear();
                if (exceptionFlow?.Throw(at, exception, h => Types.IsAssignable(exception.Type, context.Type(h.CatchType))) is not { } transfer) throw exception;
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

    private StackValue Divide(StackValue right, StackValue left, bool unsigned, bool remainder = false)
    {
        if (left.Kind == StackKind.F && right.Kind == StackKind.F && !unsigned && !remainder)
            return Arithmetic(right, left, (_, _) => throw new InvalidOperationException(), (a, b) => a / b);
        if (left.Kind != right.Kind || left.Kind is not (StackKind.I4 or StackKind.I8)) throw new Unsupported("div 操作数类型");
        var result = CilIntegerDivision.Evaluate(left, right, unsigned, remainder);
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
        return result is { } r ? single ? StackValue.F32((float)FloatingResult(r)) : StackValue.F(FloatingResult(r)) : null;
    }

    private static bool BeforeFieldInitValue(TypeRef type) => type is DefinitionRef { Definition: { IsValueType: true } d }
        && (d.Attributes & System.Reflection.TypeAttributes.BeforeFieldInit) != 0;

    private ulong NotNull(StackValue value, NullCheckSource source = NullCheckSource.None) =>
        value.Bits != 0 ? value.Bits : throw new CilThrow(Types.Corlib("System.NullReferenceException"))
        { NullCheck = depth == 0 ? source : NullCheckSource.None };

    /// <summary>字段地址：引用类型的字段相对对象（含对象头）；值类型的字段经指向数据的托管指针访问，减去对象头。</summary>
    private ulong FieldAddress(World world, FieldRef field, StackValue receiver)
    {
        var offset = world.FieldOffset(field);
        if (field.DeclaringType is DefinitionRef { Definition.IsValueType: true })
            return receiver.Bits + (ulong)(offset - StorageLayout.ObjectHeaderSize);
        return NotNull(receiver, NullCheckSource.FieldReceiver) + (ulong)offset;
    }

    private ulong Element(CilSide side, TypeRef type, StackValue indexValue, StackValue arrayValue)
    {
        var array = NotNull(arrayValue);
        var position = unchecked((ulong)indexValue.Integer);
        if (position >= side.Read64(array + StorageLayout.ArrayMaxLength)) throw new CilThrow(Types.Corlib("System.IndexOutOfRangeException"));
        return array + StorageLayout.ArrayData + position * (ulong)side.World.StorageSize(type);
    }

    /// <summary>callvirt 按接收者的运行时类型选择实现（接口方法经 interface offsets）。</summary>
    /// <summary>
    /// ECMA-335 III.2.1 constrained. 前缀：引用类型解引用后按 callvirt 分派；值类型自己实现了方法时，this 仍是地址，直接调用该实现。
    /// 值类型没有实现（要先装箱）的情形不支持。
    /// </summary>
    private MethodRef Constrained(CilSide side, TypeRef thisType, MethodRef target, IList<StackValue> values)
    {
        if (ManagedTypes.IsReferenceType(thisType))
        {
            return target.Method.IsVirtual ? Dispatch(side, values[0].Bits, target) : target;
        }
        if (thisType is not DefinitionRef { Definition.IsValueType: true } value) throw new Unsupported($"constrained {thisType}");
        var implementation = target.Method.IsVirtual ? Slot(value, target) : target;
        if (implementation.Method.Owner != value.Definition) throw new Unsupported($"constrained {thisType} 要装箱");
        return implementation;
    }

    private MethodRef Dispatch(CilSide side, ulong receiver, MethodRef target)
    {
        var type = side.TypeOf(receiver) switch
        {
            DefinitionRef definition => definition,
            ArrayRef { IsVector: true } when target.Method.Owner.FullName is "System.Array" or "System.Object" => Types.Corlib("System.Array"),
            _ => throw new Unsupported("数组上的虚调用"),
        };
        return Slot(type, target);
    }

    private MethodRef Slot(DefinitionRef type, MethodRef target) => model.Virtual(type, target);

    /// <summary>已建模的库操作直接执行；其余外部调用记录事件并按签名合成输出。</summary>
    private StackValue? Invoke(CilSide side, MethodRef callee, StackValue[] values)
    {
        var world = side.World;
        if (callee.Method is { Name: "RunClassConstructor", Owner.FullName: "System.Runtime.CompilerServices.RuntimeHelpers" })
        {
            side.RunClassConstructor(world.TypeOfHandle(values[0].Bits));
            return null;
        }
        // 核心库 IntPtr/UIntPtr.ToPointer 的参考 IL 只读取指针字段并返回，没有调用事件。
        if (callee.Method is { Name: "ToPointer", IsStatic: false, Parameters.Count: 0,
                Owner.Assembly: "mscorlib.dll", Owner.FullName: "System.IntPtr" or "System.UIntPtr" }
            && callee.Method.ReturnType is PointerRef)
            return StackValue.I8(side.Read64(values[0].Bits));
        if (DelegateModel.IsInvoke(callee)) return InvokeDelegate(side, callee, values);
        if (callee.Method is { Name: "get_Length", IsStatic: false, Owner.FullName: "System.String", Parameters.Count: 0 })
        {
            return ReadValue(side, Types.Int32, NotNull(values[0]) + StorageLayout.StringLength);
        }
        if (callee.Method is { Name: "As", IsStatic: true, Owner.FullName: "System.Runtime.CompilerServices.Unsafe", Parameters.Count: 1 }) return values[0];
        if (callee.Method is { IsStatic: true, Owner.FullName: "System.BitConverter", Parameters.Count: 1 } conversion)
        {
            var converted = conversion.Name switch
            {
                "SingleToInt32Bits" => StackValue.I4(BitConverter.SingleToInt32Bits((float)values[0].Double)),
                "DoubleToInt64Bits" => StackValue.I8(values[0].Bits),
                "Int32BitsToSingle" => StackValue.F32(BitConverter.Int32BitsToSingle(values[0].Int32)),
                "Int64BitsToDouble" => StackValue.F(BitConverter.UInt64BitsToDouble(values[0].Bits)),
                _ => (StackValue?)null,
            };
            if (converted is { } bitPattern) return bitPattern;
        }
        if (callee.Method is { IsStatic: true, Owner.FullName: "System.Math", Parameters.Count: 1 } math && MathIntrinsic(math.Name, values[0], math.Parameters[0].Type) is { } computed)
            return computed;
        if (callee.Method is { Name: "MemoryBarrier", IsStatic: true, Owner.FullName: "System.Threading.Thread" }) return null;
        if (callee.Method is { Name: "CompareExchange" or "Exchange", IsStatic: true, Owner.FullName: "System.Threading.Interlocked", GenericParameters.Count: 1 }
            && values.Length == (callee.Method.Name == "CompareExchange" ? 3 : 2) && callee.MethodArguments is [var exchangedType] && Types.Kind(exchangedType) == TypeKind.Reference)
        {
            var old = side.Read64(values[0].Bits);
            if (callee.Method.Name == "Exchange" || old == values[2].Bits) side.WriteValue(values[0].Bits, values[1].Bits, 8);
            return StackValue.O(old);
        }
        // 已有的无参异常构造抽象不产生调用事件；被 catch 后继续执行时也不能消耗调用序号。
        if (callee.Method is { Name: ".ctor", Parameters.Count: 0 } && Side.InExceptionRegion(values[0].Bits)) return null;
        var ordinal = side.NextCall();
        side.Callees.Add(callee);
        var arguments = ManagedValues.ArgumentTypes(callee);
        if (arguments.Length != values.Length) throw new Unsupported($"被调方法 {callee} 的实参个数");
        var rawArguments = arguments.Select((type, i) => ToBytes(type, values[i])).ToArray();
        var bits = index.ManagedValues.ObservableArguments(side, callee, arguments, rawArguments);
        if (!(callee.Method is { Name: ".ctor", Parameters.Count: 0 } && Side.InExceptionRegion(values[0].Bits)))
        {
            try { side.CallEvent(index.CodeAddress(callee), bits, Side.IsGenericInstance(callee) ? callee : null); }
            catch (PlannedThrow e) { throw new CilThrow(side.TypeOf(e.Object), e.Object); }
        }
        index.ManagedValues.WriteBack(side, callee, ordinal, rawArguments);
        var returnType = callee.Method.ReturnType.Substitute(callee.TypeArguments, callee.MethodArguments);
        return ManagedTypes.IsVoid(returnType) ? null : FromBytes(returnType, side.EnumArrayReturn(callee, bits) ?? world.ReturnBytes(ordinal, returnType));
    }

    // —— 值的表示 ——

    private bool IsHandle(TypeRef type) => type.Equals(Types.RuntimeTypeHandle) || type.Equals(Types.RuntimeFieldHandle) || type.Equals(Types.RuntimeMethodHandle);

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
            case TypeKind.Float: return StackValue.F32(BitConverter.UInt32BitsToSingle((uint)bits));
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
            // float32 的操作数在 double 里运算再舍入一次，加减乘除的结果和直接按 float32 运算相同（double 的精度超过 2p+2）。
            StackKind.F when floating is not null && left.Single && right.Single => StackValue.F32((float)FloatingResult(floating(left.Double, right.Double))),
            StackKind.F when floating is not null => StackValue.F(FloatingResult(floating(left.Double, right.Double))),
            _ => throw new Unsupported($"{left.Kind} 上的运算"),
        };
    }

    /// <summary>NaN 位型未由 CIL 规定；在可能被按位观察前报告无法判定。</summary>
    private static double FloatingResult(double result) => double.IsNaN(result)
        ? throw new Unsupported("浮点 NaN 的符号和载荷未由 CIL 规定", ComparisonReason.NaN) : result;

    /// <summary>ECMA-335 III.3.5–3.15：条件分支等于比较加 brtrue 或 brfalse；浮点的 bge、ble 和无序比较配对，整数的是带符号比较。</summary>
    private static bool Branches(Code code, StackValue left, StackValue right)
    {
        var floating = left.Kind == StackKind.F || right.Kind == StackKind.F;
        return code switch
        {
            Code.Beq or Code.Beq_S => Compare(Code.Ceq, left, right),
            Code.Bne_Un or Code.Bne_Un_S => !Compare(Code.Ceq, left, right),
            Code.Bgt or Code.Bgt_S => Compare(Code.Cgt, left, right),
            Code.Bgt_Un or Code.Bgt_Un_S => Compare(Code.Cgt_Un, left, right),
            Code.Blt or Code.Blt_S => Compare(Code.Clt, left, right),
            Code.Blt_Un or Code.Blt_Un_S => Compare(Code.Clt_Un, left, right),
            Code.Bge or Code.Bge_S => !Compare(floating ? Code.Clt_Un : Code.Clt, left, right),
            Code.Ble or Code.Ble_S => !Compare(floating ? Code.Cgt_Un : Code.Cgt, left, right),
            Code.Bge_Un or Code.Bge_Un_S => !Compare(floating ? Code.Clt : Code.Clt_Un, left, right),
            Code.Ble_Un or Code.Ble_Un_S => !Compare(floating ? Code.Cgt : Code.Cgt_Un, left, right),
            _ => throw new Unsupported(code.ToString()),
        };
    }

    /// <summary>ldind、stind、ldelem、stelem 的简写形式对应的类型。</summary>
    private TypeRef Primitive(Code code) => Types.Corlib(code switch
    {
        Code.Ldind_I1 or Code.Stind_I1 or Code.Ldelem_I1 or Code.Stelem_I1 => "System.SByte",
        Code.Ldind_U1 or Code.Ldelem_U1 => "System.Byte",
        Code.Ldind_I2 or Code.Stind_I2 or Code.Ldelem_I2 or Code.Stelem_I2 => "System.Int16",
        Code.Ldind_U2 or Code.Ldelem_U2 => "System.UInt16",
        Code.Ldind_I4 or Code.Stind_I4 or Code.Ldelem_I4 or Code.Stelem_I4 => "System.Int32",
        Code.Ldind_U4 or Code.Ldelem_U4 => "System.UInt32",
        Code.Ldind_I8 or Code.Stind_I8 or Code.Ldelem_I8 or Code.Stelem_I8 => "System.Int64",
        Code.Ldind_I or Code.Stind_I or Code.Ldelem_I or Code.Stelem_I => "System.IntPtr",
        Code.Ldind_R4 or Code.Stind_R4 or Code.Ldelem_R4 or Code.Stelem_R4 => "System.Single",
        Code.Ldind_R8 or Code.Stind_R8 or Code.Ldelem_R8 or Code.Stelem_R8 => "System.Double",
        Code.Ldind_Ref or Code.Stind_Ref or Code.Ldelem_Ref or Code.Stelem_Ref => "System.Object",
        _ => throw new Unsupported(code.ToString()),
    });

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
                Code.Conv_R4 => StackValue.F32((float)value.Double),
                Code.Conv_R8 => value,
                Code.Conv_I4 when value.Double >= -2147483648d && value.Double < 2147483648d => StackValue.I4((int)value.Double),
                Code.Conv_U4 when value.Double >= 0 && value.Double < 4294967296d => StackValue.I4(unchecked((int)(uint)value.Double)),
                Code.Conv_I8 when value.Double >= -9223372036854775808d && value.Double < 9223372036854775808d
                    => StackValue.I8(unchecked((ulong)(long)value.Double)),
                Code.Conv_U8 when value.Double >= 0 && value.Double < 18446744073709551616d => StackValue.I8((ulong)value.Double),
                _ => throw new Unsupported("浮点到整数的未定义越界转换"),
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
            Code.Conv_R4 => StackValue.F32((float)integer),
            Code.Conv_R8 => StackValue.F(integer),
            Code.Conv_R_Un => StackValue.F(unsigned),
            _ => throw new Unsupported(code.ToString()),
        };
    }
}
