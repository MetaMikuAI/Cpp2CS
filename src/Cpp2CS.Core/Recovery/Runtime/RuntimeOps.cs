using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Runtime;

/// <summary>运行时操作经指针实参的内存效果：Argument 为指针在 Arguments 中的位置，Value 为写出或读取的值的编号。</summary>
public sealed record PointerEffect(int Argument, int Value, int Size, MemoryAccess Access);

/// <summary>运行时操作的类型查询。</summary>
public interface IRuntimeTyping
{
    ManagedTypes Types { get; }
    DefinitionRef? ExceptionType(string fullName);
}

/// <summary>下降一个运行时操作所需的上下文，由下降实现提供。</summary>
public interface IRuntimeLowering
{
    ManagedTypes Types { get; }
    Call Call { get; }
    RuntimeOp Op { get; }
    IReadOnlyList<Sym> Arguments { get; }
    /// <summary>操作的结果（<see cref="ResultSym"/>，序号 0）。</summary>
    Sym Result { get; }
    ManagedValue View(Sym sym, TypeRef? expected);
    LocalValue Local(Sym sym, TypeRef type);
    void Emit(ManagedStatement statement);
    /// <summary>经指针读取的值 value：已提升单元在调用前的内容；没有时为 null。</summary>
    Sym? Pointee(int value);
    /// <summary>指针实参 argument 指向的非局部位置在 type 下的值；不能定位时为 null。</summary>
    ManagedValue? Location(int argument, TypeRef type);
    /// <summary>分配的对象等待随后的构造函数调用合为 newobj。</summary>
    void AwaitConstruction();
    /// <summary>判空被随后对同一对象的访问吸收。</summary>
    bool Absorb(Sym target);
    /// <summary>当前语句位于捕获了 exception 的 catch 处理块中。</summary>
    bool InCatchOf(Sym exception);
    /// <summary>当前语句位于 fault 处理块中。</summary>
    bool InFault { get; }
    MethodRef? ExceptionConstructor(string fullName);
    ManagedValue Hole(string reason, TypeRef? type);
}

/// <summary>下降：返回 false 表示不支持（记为洞）；terminal 不为 null 时它结束所在的块。</summary>
public delegate bool RuntimeLowering(IRuntimeLowering context, out ManagedStatement? terminal);

/// <summary>一种运行时操作的语义：结果类型、经指针的内存效果、下降。</summary>
public sealed record RuntimeOpRule(OpKind Kind)
{
    public Func<RuntimeOp, IRuntimeTyping, TypeRef?>? ResultType { get; init; }
    public Func<Call, ManagedAbi, IEnumerable<PointerEffect>>? Effects { get; init; }
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

    private static bool None(IRuntimeLowering context, out ManagedStatement? terminal)
    {
        terminal = null;
        return true;
    }

    private static IEnumerable<RuntimeOpRule> Build()
    {
        // 没有托管可见效果：写屏障、内存屏障、类元数据初始化、类构造（ECMA-335 II.10.5.3：访问静态成员时由运行时触发）、RGCTX 初始化。
        foreach (var kind in new[] { OpKind.WriteBarrier, OpKind.MemoryBarrier, OpKind.InitClass, OpKind.RunClassConstructor, OpKind.InitMethodRgctx })
            yield return new(kind) { Lower = None };
        // 只服务于分派：结果流向调用目标与 MethodInfo，不是 IL 值。
        foreach (var kind in new[] { OpKind.InterfaceInvokeData, OpKind.ResolveGenericVirtual })
            yield return new(kind) { Lower = None };

        yield return new(OpKind.NullCheck)
        {
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Arguments.Count != 1) return false;
                var target = SymTable.Resolve(c.Arguments[0]);
                if (c.Absorb(target)) return true;
                if (c.ExceptionConstructor("System.NullReferenceException") is not { } nre) return false;
                c.Emit(new ManagedCheck(c.Call.Address, new ComparisonValue(Cond.Eq, c.View(target, c.Types.Object), new ConstantValue(0, c.Types.Object, 64), c.Types.Boolean), nre));
                return true;
            },
        };
        yield return new(OpKind.NewObject)
        {
            ResultType = (op, _) => op.Operand as TypeRef,
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Op.Operand is not TypeRef) return false;
                c.AwaitConstruction();
                return true;
            },
        };
        yield return new(OpKind.NewArray)
        {
            ResultType = (op, _) => op.Operand as TypeRef,
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Op.Operand is not ArrayRef array || c.Arguments.Count != 2) return false;
                c.Emit(new ManagedAssignment(c.Call.Address, c.Local(c.Result, array), new NewArrayValue(array, c.View(c.Arguments[1], c.Types.Int32))));
                return true;
            },
        };
        yield return new(OpKind.Box)
        {
            ResultType = (_, t) => t.Types.Object,
            Effects = (call, abi) => call.Op!.Operand is TypeRef boxed && call.Arguments.Length == 2 ? [new PointerEffect(1, 1, abi.Size(boxed), MemoryAccess.Read)] : [],
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Op.Operand is not TypeRef boxed || c.Arguments.Count != 2) return false;
                var operand = c.Pointee(1) is { } content ? c.View(content, boxed) : c.Location(1, boxed) ?? c.Hole("装箱 值的位置未知", boxed);
                c.Emit(new ManagedAssignment(c.Call.Address, c.Local(c.Result, c.Types.Object), new BoxValue(operand, boxed, c.Types.Object)));
                return true;
            },
        };
        yield return new(OpKind.Unbox)
        {
            ResultType = (op, _) => op.Operand is TypeRef t ? new ByRefRef(t) : null,
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Op.Operand is not TypeRef unboxed || c.Arguments.Count != 2) return false;
                c.Emit(new ManagedAssignment(c.Call.Address, c.Local(c.Result, new ByRefRef(unboxed)), new UnboxAddressValue(c.View(c.Arguments[1], c.Types.Object), unboxed)));
                return true;
            },
        };
        yield return new(OpKind.IsInst)
        {
            ResultType = (op, _) => op.Operand as TypeRef,
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Op.Operand is not TypeRef target || c.Arguments.Count < 1) return false;
                c.Emit(new ManagedAssignment(c.Call.Address, c.Local(c.Result, target), new IsInstValue(c.View(c.Arguments[0], c.Types.Object), target)));
                return true;
            },
        };
        yield return new(OpKind.IsAssignableFrom) { ResultType = (_, t) => t.Types.Boolean };
        yield return new(OpKind.Throw)
        {
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = c.Arguments.Count >= 1 ? new ManagedThrow(c.Call.Address, c.View(c.Arguments[0], c.Types.Object)) : null;
                return terminal is not null;
            },
        };
        yield return new(OpKind.ThrowNew)
        {
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = c.Op.Operand is string name && c.ExceptionConstructor(name) is { } ctor ? new ManagedThrow(c.Call.Address, new NewObjectValue(ctor, [])) : null;
                return terminal is not null;
            },
        };
        yield return new(OpKind.NewException)
        {
            ResultType = (op, t) => op.Operand is string name ? t.ExceptionType(name) : null,
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
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Op.Operand is not string name || c.Arguments.Count != 1 || c.ExceptionConstructor(name) is not { } ctor) return false;
                c.Emit(new ManagedCheck(c.Call.Address, c.View(c.Arguments[0], c.Types.Boolean), ctor));
                return true;
            },
        };
        yield return new(OpKind.BoundsCheck)
        {
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = null;
                if (c.Arguments.Count != 2 || c.ExceptionConstructor("System.IndexOutOfRangeException") is not { } ctor) return false;
                c.Emit(new ManagedCheck(c.Call.Address, new ComparisonValue(Cond.Uge, c.View(c.Arguments[0], c.Types.Int32), c.View(c.Arguments[1], c.Types.Int32), c.Types.Boolean), ctor));
                return true;
            },
        };
        // C++ 异常机制：取得与结束捕获不是 IL 操作；托管异常由区域的异常局部表示。
        foreach (var kind in new[] { OpKind.BeginCatch, OpKind.EndCatch })
            yield return new(kind) { Lower = None };
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
            Lower = (IRuntimeLowering c, out ManagedStatement? terminal) =>
            {
                terminal = c.Arguments.Count == 0 || c.InCatchOf(c.Arguments[0]) ? new ManagedRethrow(c.Call.Address)
                    : new ManagedThrow(c.Call.Address, c.View(c.Arguments[0], c.Types.Object));
                return true;
            },
        };
        yield return new(OpKind.Import)
        {
            Effects = (call, _) => call switch
            {
                { Op.Operand: "memcpy" or "memmove", Arguments: [_, _, Ir.Const { Value: > 0 and <= 4096 } count] } =>
                    [new PointerEffect(0, 0, (int)count.Value, MemoryAccess.Write), new PointerEffect(1, 1, (int)count.Value, MemoryAccess.Read)],
                { Op.Operand: "memset", Arguments: [_, _, Ir.Const { Value: > 0 and <= 4096 } length] } =>
                    [new PointerEffect(0, 0, (int)length.Value, MemoryAccess.Write)],
                _ => [],
            },
        };
    }
}
