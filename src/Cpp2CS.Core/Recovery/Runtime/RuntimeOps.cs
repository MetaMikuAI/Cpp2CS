using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Effects;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Runtime;

/// <summary>运行时操作经指针实参的内存效果：Argument 为指针在 Arguments 中的位置，Value 为写出或读取的值的编号。</summary>
public sealed record PointerEffect(int Argument, int Value, int Size, MemoryAccess Access);

public enum RuntimeInputKind { Value, Location, Pointee }
/// <summary>运行时操作实际使用的值与期望类型；Pointee 指名提升单元中的逻辑值编号。</summary>
public sealed record RuntimeInput(Sym Value, TypeRef? Type, RuntimeInputKind Kind = RuntimeInputKind.Value, int Pointee = 0);

/// <summary>运行时操作的类型查询。</summary>
public interface IRuntimeTyping
{
    ManagedTypes Types { get; }
    TypeRef? TypeOf(Sym value);
    Sym? ClassOwner(Sym value);
    DefinitionRef? ExceptionType(string fullName);
    /// <summary>操作的类操作数：L2 写入的 Operand，否则为实参中的类实体。</summary>
    TypeRef? ClassOperand(Call call);
    /// <summary>原始指针实参指向位置的类型。</summary>
    TypeRef? LocationType(Call call, int argument, int width);
    FieldRef? FieldOperand(Call call, int argument);
}

/// <summary>下降一个运行时操作所需的上下文，由下降实现提供。</summary>
public interface IRuntimeLowering
{
    ManagedTypes Types { get; }
    Call Call { get; }
    RuntimeOp Op { get; }
    /// <summary>操作的类操作数：L2 写入的 Operand，否则为实参中的类实体。</summary>
    TypeRef? ClassOperand { get; }
    /// <summary>原始实参；内存提升追加的单元由 Inputs 的 Pointee 契约读取，不参与原始实参数量和位置。</summary>
    IReadOnlyList<Sym> Arguments { get; }
    /// <summary>操作的结果（<see cref="ResultSym"/>，序号 0）。</summary>
    Sym Result { get; }
    /// <summary>具有显式结果位宽契约的多结果操作，按机器结果序号取值。</summary>
    Sym ResultAt(int index);
    /// <summary>按本操作 Inputs 契约取得已定型的输入。</summary>
    ManagedValue Input(int index);
    /// <summary>把值写入第 index 个输入指向的位置。</summary>
    void Assign(int index, ManagedValue value);
    /// <summary>值的自然类型；不受约束时为 null。</summary>
    TypeRef? TypeOf(Sym sym);
    LocalValue Local(Sym sym, TypeRef type);
    /// <summary>运行时操作展开为多个托管调用时使用的独立局部。</summary>
    LocalValue Temporary(TypeRef type);
    void Emit(ManagedStatement statement);
    /// <summary>元数据指名的字段位置，仍遵守字段访问约束。</summary>
    ManagedValue Field(ManagedValue receiver, FieldRef field);
    /// <summary>分配的对象等待随后的构造函数调用合为 newobj。</summary>
    void AwaitConstruction();
    /// <summary>判空被随后对同一对象的访问吸收。</summary>
    bool Absorb(Sym target);
    /// <summary>对象在判空处已知非空（此前已判空、已经它访问、为分配结果或在分支的非空一侧）。</summary>
    bool KnownNonNull(Sym target);
    /// <summary>越界检查被随后对同一数组、同一下标的元素访问吸收；length 是数组长度的读取。</summary>
    bool AbsorbBounds(Sym index, Sym length);
    /// <summary>当前语句位于捕获了 exception 的 catch 处理块中。</summary>
    bool InCatchOf(Sym exception);
    /// <summary>当前语句位于 fault 处理块中。</summary>
    bool InFault { get; }
    MethodRef? ExceptionConstructor(string fullName);
    ManagedValue Hole(string reason, TypeRef? type);
    /// <summary>类指针所属的对象：对象偏移 0 处的读取（运行时布局中对象头的 klass）。</summary>
    Sym? ClassOwner(Sym klass);
    /// <summary>直线路径上随后第一个有副作用的语句本身按 IL 语义触发 owner 的类初始化。</summary>
    bool InitializesNext(TypeRef owner);
}

/// <summary>下降：返回 false 表示不支持（记为洞）；terminal 不为 null 时它结束所在的块。</summary>
public delegate bool RuntimeLowering(IRuntimeLowering context, out ManagedStatement? terminal);

/// <summary>一种运行时操作的语义：输入用途、结果类型、可观察效果、指针访问和下降。</summary>
public sealed record RuntimeOpRule(OpKind Kind)
{
    public Func<Call, IReadOnlyList<int>>? ResultWidths { get; init; }
    public Func<Call, IRuntimeTyping, TypeRef?>? ResultType { get; init; }
    public Func<Call, ManagedAbi, IEnumerable<PointerEffect>>? PointerEffects { get; init; }
    public EffectSummary Behavior { get; init; } = EffectSummary.Unknown;
    public Func<Call, IReadOnlyList<Sym>, IRuntimeTyping, IReadOnlyList<RuntimeInput>>? Inputs { get; init; }
    public RuntimeLowering? Lower { get; init; }
}

/// <summary>
/// 运行时操作的注册表：L2 把 codegen 的运行时惯用法归一为 <see cref="RuntimeOp"/>，这里给出每种操作在 IL 中的意义。
/// 新增一种运行时操作只需在此登记一项；内存提升、类型与下降都只经这张表读取它的语义。
/// </summary>
public static class RuntimeOps
{
    private static readonly Dictionary<OpKind, RuntimeOpRule> rules = Build().ToDictionary(r => r.Kind);

    public static RuntimeOpRule? Of(OpKind kind) => rules.GetValueOrDefault(kind);

    /// <summary>机器层上的类操作数：L2 写入的 Operand，否则为实参中的类元数据符号。</summary>
    public static TypeRef? ClassOperand(Call call) => call.Op?.Operand as TypeRef
        ?? call.Arguments.OfType<Symbol>().FirstOrDefault(s => s.Kind == SymbolKind.Class)?.Value as TypeRef;

    private static bool None(IRuntimeLowering context, out ManagedStatement? terminal)
    {
        terminal = null;
        return true;
    }

    /// <summary>越界条件的下标与长度：index >=u length、length <=u index，或 length == 0（下标 0）。</summary>
    private static (Sym Index, Sym Length)? BoundsCondition(Sym condition) => SymTable.Resolve(condition) switch
    {
        OpSym { Op: { Kind: OperatorKind.Compare } c, Args: [var a, var b] } when c.Cond == Cond.Uge => (a, b),
        OpSym { Op: { Kind: OperatorKind.Compare } c, Args: [var a, var b] } when c.Cond == Cond.Ule => (b, a),
        OpSym { Op: { Kind: OperatorKind.Compare } c, Args: [var a, ConstSym { Value: 0 } zero] } when c.Cond == Cond.Eq => (zero, a),
        _ => null,
    };

    private static IEnumerable<RuntimeOpRule> Build()
    {
        // 不透明值只按位置操作：对值类型是整体复制，对引用类型是引用赋值。
        yield return new(OpKind.CopyGenericValue)
        {
            Inputs = (call, a, t) => a.Count == 2 ? [new(a[0], t.ClassOperand(call), RuntimeInputKind.Location), new(a[1], t.ClassOperand(call), RuntimeInputKind.Location)] : [],
            Behavior = new(EffectKind.Read | EffectKind.Write),
            PointerEffects = (_, _) => [new PointerEffect(0, 0, -1, MemoryAccess.Write), new PointerEffect(1, 1, -1, MemoryAccess.Read)],
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.ClassOperand is null || c.Arguments.Count != 2) return false;
                c.Assign(0, c.Input(1));
                return true;
            },
        };
        yield return new(OpKind.ClearGenericValue)
        {
            Inputs = (call, a, t) => a.Count == 1 ? [new(a[0], t.ClassOperand(call), RuntimeInputKind.Location)] : [],
            Behavior = new(EffectKind.Write),
            PointerEffects = (_, _) => [new PointerEffect(0, 0, -1, MemoryAccess.Write)],
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.ClassOperand is not { } type || c.Arguments.Count != 1) return false;
                c.Assign(0, new ComposedValue(type, []));
                return true;
            },
        };
        yield return new(OpKind.ReadByteArray)
        {
            Inputs = (_, a, t) => a.Count == 2 ? [new(a[0], t.TypeOf(a[0])), new(a[1], t.Types.Int32)] : [],
            ResultWidths = _ => [8],
            ResultType = (_, t) => t.Types.Byte,
            Behavior = new(EffectKind.Read, ExceptionEffect.NullReference | ExceptionEffect.Bounds),
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Arguments.Count != 2 || c.TypeOf(c.Arguments[0]) is not ArrayRef { IsVector: true } array
                    || !array.Element.Equals(c.Types.Byte)) return false;
                c.Emit(new ManagedAssignment(c.Call.Address, c.Local(c.Result, c.Types.Byte),
                    new ArrayElementValue(c.Input(0), c.Input(1), c.Types.Byte, 8)));
                return true;
            },
        };
        yield return new(OpKind.FieldAddress)
        {
            Inputs = (call, a, t) => a.Count == 2 ? [new(a[0], t.TypeOf(a[0]) ?? t.FieldOperand(call, 1)?.DeclaringType)] : [],
            ResultType = (call, typing) => typing.FieldOperand(call, 1) is { DeclaringType: DefinitionRef owner } field
                ? new ByRefRef(field.Field.Type.Substitute(owner.Arguments, [])) : null,
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Arguments is not [var receiver, EntitySym { Symbol: { Kind: SymbolKind.Field, Value: FieldRef field } }]) return false;
                var address = new AddressValue(c.Field(c.Input(0), field));
                c.Emit(new ManagedAssignment(c.Call.Address, c.Local(c.Result, address.Type), address));
                return true;
            },
        };
        yield return new(OpKind.CompareExchangeReference)
        {
            Inputs = (call, a, t) => a.Count == 3 ? [new(a[0], t.LocationType(call, 0, 64) ?? t.Types.Object, RuntimeInputKind.Location), new(a[1], t.LocationType(call, 0, 64) ?? t.Types.Object), new(a[2], t.LocationType(call, 0, 64) ?? t.Types.Object)] : [],
            Behavior = new(EffectKind.Read | EffectKind.Write | EffectKind.Capture | EffectKind.Order, ExceptionEffect.Any),
            ResultType = (call, typing) => typing.LocationType(call, 0, 64),
            PointerEffects = (_, _) => [new PointerEffect(0, 0, 8, MemoryAccess.ReadWrite)],
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Arguments.Count != 3 || c.Input(0) is not { } location || !ManagedTypes.IsReferenceType(location.Type)) return false;
                var definition = c.Types.CorlibDefinition("System.Threading.Interlocked")?.Methods.FirstOrDefault(m => m.IsStatic
                    && m.Name == "CompareExchange" && m.GenericParameters.Count == 1 && m.Parameters.Count == 3
                    && m.Parameters[0].Type is ByRefRef { Element: GenericParameterRef } && m.Parameters[1].Type is GenericParameterRef
                    && m.Parameters[2].Type.Equals(m.Parameters[1].Type) && m.ReturnType.Equals(m.Parameters[1].Type));
                if (definition is null) return false;
                var method = new MethodRef(definition, [], [location.Type]);
                var arguments = new ManagedValue[] { new AddressValue(location), c.Input(1), c.Input(2) };
                c.Emit(new ManagedCall(c.Call.Address, new ManagedInvocation(method, null, arguments, false), c.Local(c.Result, location.Type), false));
                return true;
            },
        };
        // GC 写屏障由托管写入承担；元数据与 RGCTX 初始化不单独写出。
        foreach (var kind in new[] { OpKind.WriteBarrier, OpKind.InitClass, OpKind.InitMethodRgctx })
            yield return new(kind) { Behavior = EffectSummary.None, Lower = None };
        yield return new(OpKind.MemoryBarrier)
        {
            Behavior = new(EffectKind.Order),
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Types.CorlibMethod("System.Threading.Thread", "MemoryBarrier") is not { Method.IsStatic: true } barrier) return false;
                c.Emit(new ManagedCall(c.Call.Address, new ManagedInvocation(barrier, null, [], false), null, false));
                return true;
            },
        };
        // 隐式类构造：IL2CPP 在静态访问和构造前插入的 il2cpp_runtime_class_init 是代码生成产物，
        // 托管 IL 没有对应指令；下一次静态访问或 newobj 由 CLR 按 ECMA-335 II.10.5.3 触发同一初始化。
        yield return new(OpKind.RunClassConstructor) { Lower = None };
        // 只服务于分派：结果流向调用目标与 MethodInfo，不是 IL 值。
        foreach (var kind in new[] { OpKind.InterfaceInvokeData, OpKind.ResolveGenericVirtual })
            yield return new(kind) { Behavior = EffectSummary.None, Lower = None };

        // 判空：机器值为 0 时抛出 NullReferenceException。操作数通常是对象引用；clang 也会直接检验内联类型判断的结果
        // （对象已知非空时 isinst 的结果为空即判断失败），这时与 0 比较的是该判断的 bool 值。
        yield return new(OpKind.NullCheck)
        {
            Inputs = (_, a, t) => a.Count == 1 ? [new(a[0], t.TypeOf(a[0]) is { } natural && t.Types.Kind(natural) is TypeKind.Int or TypeKind.Bool ? natural : t.Types.Object)] : [],
            Behavior = new(EffectKind.None, ExceptionEffect.NullReference),
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Arguments.Count != 1) return false;
                var target = SymTable.Resolve(c.Arguments[0]);
                if (c.KnownNonNull(target) || c.Absorb(target)) return true;
                if (c.ExceptionConstructor("System.NullReferenceException") is not { } nre) return false;
                var value = c.Input(0);
                var type = value.Type;
                c.Emit(new ManagedCheck(c.Call.Address, new ComparisonValue(Cond.Eq, value, new ConstantValue(0, type, c.Types.Kind(type) == TypeKind.Reference ? 64 : c.Types.Bits(type)), c.Types.Boolean), nre));
                return true;
            },
        };
        yield return new(OpKind.NewObject)
        {
            Behavior = new(EffectKind.Allocate, ExceptionEffect.Any),
            ResultType = (call, t) => t.ClassOperand(call),
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.ClassOperand is null) return false;
                c.AwaitConstruction();
                return true;
            },
        };
        yield return new(OpKind.NewArray)
        {
            Inputs = (_, a, t) => a.Count == 2 ? [new(a[1], t.Types.Int32)] : [],
            Behavior = new(EffectKind.Allocate, ExceptionEffect.Any),
            ResultType = (call, t) => t.ClassOperand(call),
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.ClassOperand is not ArrayRef array || c.Arguments.Count != 2) return false;
                c.Emit(new ManagedAssignment(c.Call.Address, c.Local(c.Result, array), new NewArrayValue(array, c.Input(0))));
                return true;
            },
        };
        yield return new(OpKind.Box)
        {
            Inputs = (call, a, t) => a.Count == 2 ? [new(a[1], t.ClassOperand(call), RuntimeInputKind.Pointee, 1)] : [],
            Behavior = new(EffectKind.Read | EffectKind.Allocate, ExceptionEffect.Any),
            ResultType = (_, t) => t.Types.Object,
            PointerEffects = (call, abi) => ClassOperand(call) is { } boxed && call.Arguments.Length == 2 ? [new PointerEffect(1, 1, abi.Size(boxed), MemoryAccess.Read)] : [],
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.ClassOperand is not { } boxed || c.Arguments.Count != 2) return false;
                var operand = c.Input(0);
                c.Emit(new ManagedAssignment(c.Call.Address, c.Local(c.Result, c.Types.Object), new BoxValue(operand, boxed, c.Types.Object)));
                return true;
            },
        };
        yield return new(OpKind.GenericHasValue)
        {
            Inputs = (call, a, t) => a.Count == 2 ? [new(a[1], t.ClassOperand(call), RuntimeInputKind.Pointee, 1)] : [],
            ResultWidths = _ => [1],
            ResultType = (_, t) => t.Types.Boolean,
            Behavior = new(EffectKind.Read, ExceptionEffect.None),
            PointerEffects = (call, abi) => ClassOperand(call) is { } type && call.Arguments.Length == 2
                ? [new PointerEffect(1, 1, abi.Kind(type) is null ? -1 : abi.Size(type), MemoryAccess.Read)] : [],
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.ClassOperand is not { } type || c.Arguments.Count != 2) return false;
                var boxed = new BoxValue(c.Input(0), type, c.Types.Object);
                c.Emit(new ManagedAssignment(c.Call.Address, c.Local(c.Result, c.Types.Boolean),
                    new ComparisonValue(Cond.Ne, boxed, new ConstantValue(0, c.Types.Object, 64), c.Types.Boolean)));
                return true;
            },
        };
        yield return new(OpKind.Unbox)
        {
            Inputs = (_, a, t) => a.Count == 2 ? [new(a[0], t.Types.Object)] : [],
            Behavior = new(EffectKind.None, ExceptionEffect.Any),
            ResultType = (call, t) => t.ClassOperand(call) is { } unboxed ? new ByRefRef(unboxed) : null,
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.ClassOperand is not { } unboxed || c.Arguments.Count != 2) return false;
                c.Emit(new ManagedAssignment(c.Call.Address, c.Local(c.Result, new ByRefRef(unboxed)), new UnboxAddressValue(c.Input(0), unboxed)));
                return true;
            },
        };
        yield return new(OpKind.IsInst)
        {
            Inputs = (_, a, t) => a.Count >= 1 ? [new(a[0], t.Types.Object)] : [],
            Behavior = EffectSummary.None,
            ResultType = (call, t) => t.ClassOperand(call) is { } target && ManagedTypes.IsReferenceType(target) ? target : t.Types.Object,
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.ClassOperand is not { } target || c.Arguments.Count < 1) return false;
                // isinst 总是返回对象引用或 null；值类型及开放泛型保留装箱状态，之后由显式拆箱读取值。
                var boxed = ManagedTypes.IsReferenceType(target) ? null : c.Types.Object;
                c.Emit(new ManagedAssignment(c.Call.Address, c.Local(c.Result, boxed ?? target), new IsInstValue(c.Input(0), target, boxed)));
                return true;
            },
        };
        yield return new(OpKind.IsInstArrayElement)
        {
            Inputs = (_, a, t) => a.Count == 2 ? [new(a[0], t.Types.Object), new(a[1], t.TypeOf(a[1]))] : [],
            Behavior = new(EffectKind.Read, ExceptionEffect.Any),
            ResultType = (_, t) => t.Types.Object,
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Arguments is not [var value, var array]
                    || c.TypeOf(array) is not ArrayRef arrayType || !ManagedTypes.IsReferenceType(arrayType.Element)
                    || c.Types.CorlibMethod("System.Object", "GetType") is not { } getType
                    || c.Types.CorlibMethod("System.Type", "GetElementType") is not { } getElementType
                    || c.Types.CorlibMethod("System.Type", "IsInstanceOfType", c.Types.Object) is not { } isInstance) return false;
                var operand = c.Temporary(c.Types.Object);
                var runtimeType = c.Temporary(getType.Method.ReturnType);
                var elementType = c.Temporary(getElementType.Method.ReturnType);
                var accepts = c.Temporary(c.Types.Boolean);
                c.Emit(new ManagedAssignment(c.Call.Address, operand, c.Input(0)));
                c.Emit(new ManagedCall(c.Call.Address, new(getType, c.Input(1), [], false), runtimeType, false));
                c.Emit(new ManagedCall(c.Call.Address, new(getElementType, runtimeType, [], true), elementType, false));
                c.Emit(new ManagedCall(c.Call.Address, new(isInstance, elementType, [operand], true), accepts, false));
                c.Emit(new ManagedAssignment(c.Call.Address, c.Local(c.Result, c.Types.Object),
                    new ChoiceValue(accepts, operand, new ConstantValue(0, c.Types.Object, 64), c.Types.Object, 64)));
                return true;
            },
        };
        // il2cpp_class_is_assignable_from(klass, oklass)：oklass 为对象的类指针时即对象是否为 klass 类型。
        yield return new(OpKind.IsAssignableFrom)
        {
            Inputs = (_, a, t) => a.Count == 2 && t.ClassOwner(a[1]) is { } owner ? [new(owner, t.Types.Object)] : [],
            ResultType = (_, t) => t.Types.Boolean,
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Arguments.Count != 2 || SymTable.Resolve(c.Arguments[0]) is not EntitySym { Symbol: { Kind: SymbolKind.Class, Value: TypeRef target } }
                    || c.ClassOwner(c.Arguments[1]) is not { } owner) return false;
                var test = new ComparisonValue(Cond.Ne, new IsInstValue(c.Input(0), target), new ConstantValue(0, c.Types.Object, 64), c.Types.Boolean);
                c.Emit(new ManagedAssignment(c.Call.Address, c.Local(c.Result, c.Types.Boolean), test));
                return true;
            },
        };
        // 内联的继承检查：实参是对象的类指针，结果为对象是否为 Operand 类型（或其子类、实现）。
        yield return new(OpKind.TypeCheck)
        {
            Inputs = (_, a, t) => a.Count == 1 && t.ClassOwner(a[0]) is { } owner ? [new(owner, t.Types.Object)] : [],
            Behavior = EffectSummary.None,
            ResultType = (_, t) => t.Types.Boolean,
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Op.Operand is not TypeRef target || c.Arguments.Count != 1 || c.ClassOwner(c.Arguments[0]) is not { } owner) return false;
                var test = new ComparisonValue(Cond.Ne, new IsInstValue(c.Input(0), target), new ConstantValue(0, c.Types.Object, 64), c.Types.Boolean);
                c.Emit(new ManagedAssignment(c.Call.Address, c.Local(c.Result, c.Types.Boolean), test));
                return true;
            },
        };
        yield return new(OpKind.Throw)
        {
            Inputs = (_, a, t) => a.Count > 0 ? [new(a[0], t.Types.Object)] : [],
            Behavior = new(EffectKind.None, ExceptionEffect.Any),
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = c.Arguments.Count >= 1 ? new ManagedThrow(c.Call.Address, c.Input(0)) : null;
                return terminal is not null;
            },
        };
        // 逐点证明的 allocate/wrapper/__cxa_throw：抛出唯一实参中的托管异常。
        yield return new(OpKind.ThrowManaged)
        {
            Inputs = (_, a, t) => a.Count > 0 ? [new(a[0], t.Types.Object)] : [],
            Behavior = new(EffectKind.None, ExceptionEffect.Any),
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = c.Arguments.Count >= 1 ? new ManagedThrow(c.Call.Address, c.Input(0)) : null;
                return terminal is not null;
            },
        };
        yield return new(OpKind.ThrowNew)
        {
            Behavior = new(EffectKind.Allocate, ExceptionEffect.Any),
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = c.Op.Operand is string name && c.ExceptionConstructor(name) is { } ctor ? new ManagedThrow(c.Call.Address, new NewObjectValue(ctor, [])) : null;
                return terminal is not null;
            },
        };
        yield return new(OpKind.NewException)
        {
            Behavior = new(EffectKind.Allocate, ExceptionEffect.Any),
            ResultType = (call, t) => call.Op!.Operand is string name ? t.ExceptionType(name) : null,
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Op.Operand is not string name || c.ExceptionConstructor(name) is not { } ctor) return false;
                c.Emit(new ManagedAssignment(c.Call.Address, c.Local(c.Result, ctor.DeclaringType), new NewObjectValue(ctor, [])));
                return true;
            },
        };
        yield return new(OpKind.ThrowIf)
        {
            Inputs = (_, a, t) => a.Count == 1 ? [new(a[0], t.Types.Boolean)] : [],
            Behavior = new(EffectKind.None, ExceptionEffect.Any),
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Op.Operand is not string name || c.Arguments.Count != 1 || c.ExceptionConstructor(name) is not { } ctor) return false;
                // 下标越界的条件：index >=u length；下标为常量 0 时 clang 化简为 length == 0。
                if (name == "System.IndexOutOfRangeException" && BoundsCondition(c.Arguments[0]) is var (index, length) && c.AbsorbBounds(index, length)) return true;
                c.Emit(new ManagedCheck(c.Call.Address, c.Input(0), ctor));
                return true;
            },
        };
        yield return new(OpKind.BoundsCheck)
        {
            Inputs = (_, a, t) => a.Count == 2 ? [new(a[0], t.Types.Int32), new(a[1], t.Types.Int32)] : [],
            Behavior = new(EffectKind.None, ExceptionEffect.Bounds),
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Arguments.Count != 2) return false;
                if (c.AbsorbBounds(c.Arguments[0], c.Arguments[1])) return true;
                if (c.ExceptionConstructor("System.IndexOutOfRangeException") is not { } ctor) return false;
                c.Emit(new ManagedCheck(c.Call.Address, new ComparisonValue(Cond.Uge, c.Input(0), c.Input(1), c.Types.Boolean), ctor));
                return true;
            },
        };
        // C++ 异常机制：取得与结束捕获不是 IL 操作；托管异常由区域的异常局部表示。
        foreach (var kind in new[] { OpKind.BeginCatch, OpKind.EndCatch })
            yield return new(kind) { Behavior = EffectSummary.None, Lower = None };
        // 继续展开：在 fault 处理块中即 endfault。
        yield return new(OpKind.ResumeUnwind)
        {
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = c.InFault ? new ManagedEndFault(c.Call.Address) : null;
                return terminal is not null;
            },
        };
        // 重新抛出：在捕获了同一异常的 catch 中为 rethrow，否则抛出该异常对象（IL 的 rethrow 只能出现在 catch 中）。
        yield return new(OpKind.Rethrow)
        {
            Inputs = (_, a, t) => a.Count > 0 ? [new(a[0], t.Types.Object)] : [],
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = c.Arguments.Count == 0 || c.InCatchOf(c.Arguments[0]) ? new ManagedRethrow(c.Call.Address)
                    : new ManagedThrow(c.Call.Address, c.Input(0));
                return true;
            },
        };
        yield return new(OpKind.ImportOutPair)
        {
            ResultWidths = _ => [32, 32],
            Inputs = (_, a, t) => a.Count == 1 ? [new(a[0], t.Types.Single)] : [],
            ResultType = (call, t) => call.Op?.Operand is "sincosf" ? t.Types.Single : null,
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Op.Operand is not "sincosf" || c.Arguments.Count != 1 || c.Call.Results.Length != 2
                    || c.Types.SinCosImport() is not { } method) return false;
                var sine = c.Local(c.ResultAt(0), c.Types.Single);
                var cosine = c.Local(c.ResultAt(1), c.Types.Single);
                c.Emit(new ManagedCall(c.Call.Address, new(method, null,
                    [c.Input(0), new AddressValue(sine), new AddressValue(cosine)], false), null, false));
                return true;
            },
        };
        yield return new(OpKind.Import)
        {
            ResultWidths = call => MathImportSignature.Find(call.Op?.Operand as string) is { } signature ? [signature.Single ? 32 : 64] : [],
            Inputs = (call, a, t) => call.Op?.Operand is string symbol && MathImportSignature.Find(symbol) is { } signature
                && t.Types.MathImport(symbol) is { } method ? signature.Parameters.Select((_, i) => (Index: call.ArgumentIndex(signature.Register(i)), Type: method.Method.Parameters[i].Type))
                    .Where(p => p.Index >= 0 && p.Index < a.Count).Select(p => new RuntimeInput(a[p.Index], p.Type)).ToArray() : [],
            ResultType = (call, typing) => typing.Types.MathImport(call.Op?.Operand as string)?.Method.ReturnType,
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Op.Operand is not string symbol || MathImportSignature.Find(symbol) is not { } signature
                    || c.Types.MathImport(symbol) is not { } method) return false;
                var arguments = new List<ManagedValue>();
                for (var i = 0; i < signature.Parameters.Length; i++)
                {
                    var position = c.Call.ArgumentIndex(signature.Register(i));
                    if (position < 0 || position >= c.Arguments.Count) return false;
                    arguments.Add(c.Input(i));
                }
                c.Emit(new ManagedCall(c.Call.Address, new(method, null, arguments, false), c.Local(c.Result, method.Method.ReturnType), false));
                return true;
            },
            PointerEffects = (call, _) => call switch
            {
                { Op.Operand: "memcpy" or "memmove", Arguments: [_, _, Ir.Const { Value: > 0 and <= 4096 } count] } =>
                    [new PointerEffect(0, 0, (int)count.Value, MemoryAccess.Write), new PointerEffect(1, 1, (int)count.Value, MemoryAccess.Read)],
                { Op.Operand: "memset", Arguments: [_, _, Ir.Const { Value: > 0 and <= 4096 } length] } =>
                    [new PointerEffect(0, 0, (int)length.Value, MemoryAccess.Write)],
                // 长度未知的库函数只访问实参指向的内存，返回后不保留地址。
                { Op.Operand: "memcpy" or "memmove", Arguments.Length: 3 } =>
                    [new PointerEffect(0, 0, -1, MemoryAccess.Write), new PointerEffect(1, 1, -1, MemoryAccess.Read)],
                { Op.Operand: "memset", Arguments.Length: 3 } => [new PointerEffect(0, 0, -1, MemoryAccess.Write)],
                _ => [],
            },
        };
    }
}
