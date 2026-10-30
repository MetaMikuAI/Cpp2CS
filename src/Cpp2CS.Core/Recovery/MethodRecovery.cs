using Cpp2CS.Facts;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Lifting;

namespace Cpp2CS.Recovery;

/// <summary>
/// L3 最小版本：把 L2 归一之后的寄存器 SSA 翻译成带类型的托管方法体（<see cref="ManagedBody"/>）。
/// 只处理能逐条说明语义的形态；其余之处记为洞（<see cref="RecoveryHole"/>），有洞的方法不输出方法体。
/// 规则：
/// 1. 参数与返回值按 <see cref="ManagedAbi"/> 对应到寄存器；提升时把返回值寄存器作为返回语句的读取，避免返回值的计算被当作死定义删去。
/// 2. 每个 SSA 定义成为一个局部变量（ILSpy 再内联）；局部变量的位宽等于定义值的位宽，寄存器中更高的位为 0（W 写入清零高位）。
/// 3. 访存按运行时布局解释为字段、静态字段、数组长度或元素；解释不了即为洞。
/// 4. 判空在同一直线路径上被随后对同一对象的字段访问或实例调用（改用 callvirt）吸收；越界被随后对同一数组同一下标的元素访问吸收；
///    之间只允许无副作用的定义与其他判空（它们抛出同一种异常）。没被吸收的检查显式输出为 if (条件) throw new 异常()。
/// 5. 写屏障只通知 GC、不写入（Il2CppCodeGenWriteBarrier），直接删去；InitClass（类元数据初始化）没有托管可见的效果，删去。
/// 6. 被调用者保存寄存器在序言中存入栈帧、尾声读回（读回已作为死定义删去）：只被这样使用的栈槽删去。
/// 7. 显式的类构造（RunClassConstructor&lt;T&gt;）之后，直线路径上第一个有副作用的操作是访问 T 的静态字段、调用 T 的构造函数或静态方法时，删去显式调用。
///    依据 ECMA-335 II.10.5.3：T 没有 beforefieldinit 时，这些操作本身就在该处触发类型初始化；T 有 beforefieldinit 时，
///    初始化只保证在首次访问静态字段之前（"at, or sometime before"）完成，IL2CPP 的提前运行与 CLR 的延后运行是同一程序的两种合规执行。
/// 8. 不含访存、只在同一块内被（非 φ）使用一次的定义内联到使用处：SSA 值不可变、块内没有对 φ 局部变量的重新赋值，内联不改变结果。
///    例如构造函数里被编译器提到基类构造调用之前的参数运算（C# 中 base(...) 之前不能有语句）。
/// 实例不是线程安全的。
/// </summary>
public sealed partial class MethodRecovery
{
    internal static readonly HashSet<Storage> CalleeSaved =
        [.. Enumerable.Range(19, 12).Select(Storage.Gpr), .. Enumerable.Range(8, 8).Select(Storage.Vec)];

    internal readonly ProgramFacts facts;
    internal readonly ManagedTypes types;
    internal readonly FunctionLifter lifter;
    internal readonly IdiomRewriter rewriter;
    internal readonly ManagedAbi abi;
    internal readonly NativeMethodFacts NativeMethods;
    internal readonly MethodRef? runClassConstructor;
    internal readonly MethodRef? memoryBarrier;
    internal readonly Dictionary<string, MethodRef?> exceptionConstructors = new();

    public MethodRecovery(ProgramFacts facts, ManagedTypes types)
    {
        this.facts = facts;
        this.types = types;
        lifter = new FunctionLifter(facts);
        rewriter = new IdiomRewriter(facts) { RecordFilter = _ => false, RecoverUnusedInputs = true };
        abi = new ManagedAbi(facts.Layouts);
        NativeMethods = new(facts, lifter, rewriter);
        runClassConstructor = types.CorlibMethod("System.Runtime.CompilerServices.RuntimeHelpers", "RunClassConstructor", types.RuntimeTypeHandle);
        memoryBarrier = types.CorlibMethod("System.Threading.Thread", "MemoryBarrier");
    }

    public ManagedTypes Types => types;

    internal MethodRecoveryResult? RuntimeDeclaration(MethodRef method, ulong entry) => DelegateFacts.IsRuntimeMethod(method.Method)
        ? new(method, entry, null, []) { Declaration = RuntimeDeclarationKind.Delegate } : PlatformDeclaration(method, entry);

    public MethodRecoveryResult Recover(MethodRef method, ulong entry) => RuntimeDeclaration(method, entry) ?? new RecoveryScope(this, method, entry).Run();

    /// <summary>
    /// 恢复泛型类型或泛型方法的封闭实例，用于认出访问器等形态；
    /// 方法体以封闭类型表达，不写成泛型定义的 CIL。
    /// </summary>
    public MethodRecoveryResult RecoverInstance(MethodRef method, ulong entry) => RuntimeDeclaration(method, entry) ?? new RecoveryScope(this, method, entry) { ClosedInstance = true }.Run();

    /// <summary>从已知原生实例恢复开放泛型体；标量实例只提供传参布局，输出保留类型参数。</summary>
    public MethodRecoveryResult RecoverShared(MethodRef instance, ulong entry)
    {
        var open = MethodRef.Open(instance.Method);
        if (RuntimeDeclaration(open, entry) is { } declaration) return declaration;
        if (instance.TypeArguments.Count != open.TypeArguments.Count || instance.MethodArguments.Count != open.MethodArguments.Count
            || instance.TypeArguments.Concat(instance.MethodArguments).Any(t => !ManagedTypes.IsReferenceType(t)
                && types.Kind(t) is not (TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double)
                && !(types.Kind(t) == TypeKind.Struct && types.Size(t) > 0) && !FieldLayouts.IsFullyShared(t)))
            return new(open, entry, null, [new(entry, "泛型 实例缺少可用的共享或标量布局")]);
        open = open with
        {
            TypeArguments = open.TypeArguments.Zip(instance.TypeArguments, Bind).ToArray(),
            MethodArguments = open.MethodArguments.Zip(instance.MethodArguments, Bind).ToArray(),
        };
        return new RecoveryScope(this, open, entry) { SharedDefinition = true }.Run();
        TypeRef Bind(TypeRef parameter, TypeRef instance) => parameter is GenericParameterRef g
            ? g with
            {
                Binding = new(FieldLayouts.IsFullyShared(instance) ? NativeBindingKind.Shared
                : ManagedTypes.IsReferenceType(instance) ? NativeBindingKind.Reference
                : types.Kind(instance) == TypeKind.Struct ? NativeBindingKind.Aggregate : NativeBindingKind.Scalar, instance, entry)
            } : parameter;
    }

    /// <summary>异常类型的无参实例构造函数（全名，含 mscorlib 之外的类型）。</summary>
    internal MethodRef? ExceptionConstructor(string fullName)
    {
        if (exceptionConstructors.TryGetValue(fullName, out var known)) return known;
        var type = types.CorlibDefinition(fullName) ?? facts.Model.Types.FirstOrDefault(t => t.FullName == fullName && t.GenericParameters.Count == 0);
        var constructor = type?.Methods.FirstOrDefault(m => m.Name == ".ctor" && !m.IsStatic && m.Parameters.Count == 0);
        return exceptionConstructors[fullName] = constructor is null ? null : new MethodRef(constructor, [], []);
    }

    internal sealed record Argument(int Index, TypeRef Type, int Width);
}
