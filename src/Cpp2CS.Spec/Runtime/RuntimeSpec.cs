using System.Collections.Frozen;
using System.Collections.Immutable;
using Cpp2CS.Spec.Catalog;

namespace Cpp2CS.Spec.Runtime;

/// <summary>运行时操作在托管语义下的含义。</summary>
public enum RuntimeEffect : byte
{
    /// <summary>抛出一个由运行时构造的异常，不返回。</summary>
    Throw,
    /// <summary>不可观察：只动运行时私有的状态（元数据惰性初始化）。</summary>
    Unobservable,
    /// <summary>确保第 0 个实参给出的类已初始化。</summary>
    ClassInitialize,
    /// <summary>纯函数：结果只取决于实参与运行时不可变数据，没有内存效果。结果是登记的具名函数作用在前几个整数实参上。</summary>
    Pure,
    /// <summary>构造一个由运行时决定种类的异常对象并返回它。对象在被抛出之前不可见。</summary>
    MakeException,
    /// <summary>抛出第 0 个实参给出的异常对象，不返回。</summary>
    ThrowArgument,
    /// <summary>分配指定类的新实例，含类初始化分量；结果是新引用。</summary>
    NewObject,
    /// <summary>按数组类与长度分配一维零基数组，超出最大下标时抛出。</summary>
    NewArray,
    /// <summary>正常返回时只查询运行时不可变数据；失败时抛出登记的异常。</summary>
    ReadOrThrow,
    /// <summary>继续传播当前正在展开或处理的异常，不返回。</summary>
    Resume,
}

/// <summary>
/// 运行时操作的登记项。Symbols 是它在带符号的构建里的名字；去符号的构建由命名的依据（设计第 8 节）把地址认到登记项上。
/// Inputs、Result、Memory 用文字写明输入、结果与内存效果；Returns、Observable、Idempotent 供内核读取。
/// Source 是出处：运行时源码里的文件与符号（相对 libil2cpp 目录）。
/// </summary>
public sealed record RuntimeOperation(string Id, ImmutableArray<string> Symbols, RuntimeEffect Effect, bool Returns, bool Observable, bool Idempotent,
    ExceptionKind Exception, string Inputs, string Result, string Memory, string Source)
{
    /// <summary>纯函数：结果是哪个具名函数，作用在前几个整数实参上。</summary>
    public RuntimeFunction Function { get; init; }
    /// <summary>核对包装须原样转交的前几个整数实参槽。同一操作的多个原型取并集，均无栈、浮点或间接结果实参。</summary>
    public int Arguments { get; init; } = -1;
    /// <summary>结果是第 0 个实参所指的元数据槽在初始化之后的内容（类指针、方法、字符串等运行时对象的指针）。</summary>
    public bool ReturnsSlot { get; init; }
    /// <summary>结果就是第 0 个整数实参。</summary>
    public bool ReturnsArgument { get; init; }
}

/// <summary>具名函数的等式（设计 7.8）。每条写明出处。</summary>
public static partial class RuntimeEquations
{
    /// <summary>
    /// 登记的操作数为零时结果为零。IsInst(空, 类) 是空：vm/Object.cpp 的 Object::IsInst 第一行；
    /// codegen/il2cpp-codegen-il2cpp.h 的 IsInstClass、IsInstSealed 同样先判空。
    /// </summary>
    public static ImmutableArray<(RuntimeFunction Function, int Operand)> ZeroPreserving { get; } = [(RuntimeFunction.IsInstance, 0)];
}

/// <summary>运行时操作登记。首批只收语料用到的。</summary>
public static class RuntimeOperations
{
    private static RuntimeOperation Raise(string id, ExceptionKind kind, string source, params string[] symbols) =>
        new(id, [.. symbols], RuntimeEffect.Throw, Returns: false, Observable: true, Idempotent: false, kind,
            "无", "不返回", "构造异常对象并抛出", source) { Arguments = 0 };

    private static readonly ImmutableArray<RuntimeOperation> entries =
    [
        Raise("raise.null-reference", ExceptionKind.NullReference,
            "vm/Exception.cpp: Exception::RaiseNullReferenceException；codegen/il2cpp-codegen-il2cpp.h: NullCheck 经 il2cpp_codegen_raise_null_reference_exception 到达",
            "_Z45il2cpp_codegen_raise_null_reference_exceptionv", "_ZN6il2cpp2vm9Exception27RaiseNullReferenceExceptionEv"),
        Raise("raise.index-out-of-range", ExceptionKind.IndexOutOfRange,
            "vm/Exception.cpp: Exception::RaiseIndexOutOfRangeException；codegen/il2cpp-codegen-il2cpp.h: IL2CPP_ARRAY_BOUNDS_CHECK 经 il2cpp_codegen_raise_index_out_of_range_exception 到达",
            "_Z49il2cpp_codegen_raise_index_out_of_range_exceptionv", "_ZN6il2cpp2vm9Exception29RaiseIndexOutOfRangeExceptionEv"),
        Raise("raise.divide-by-zero", ExceptionKind.DivideByZero,
            "vm/Exception.cpp: Exception::RaiseDivideByZeroException；codegen/il2cpp-codegen-il2cpp.h: DivideByZeroCheck 经 il2cpp_codegen_raise_divide_by_zero_exception 到达",
            "_Z45il2cpp_codegen_raise_divide_by_zero_exceptionv", "_ZN6il2cpp2vm9Exception26RaiseDivideByZeroExceptionEv"),
        new("metadata.initialize", ["_Z42il2cpp_codegen_initialize_runtime_metadataPm"], RuntimeEffect.Unobservable, Returns: true, Observable: false,
            Idempotent: true, ExceptionKind.None, "元数据槽的地址", "无", "把槽里的编码换成运行时对象的指针；只写映像里的元数据槽",
            "codegen/il2cpp-codegen-il2cpp.cpp: il2cpp_codegen_initialize_runtime_metadata；vm/MetadataCache.cpp: InitializeRuntimeMetadata") { Arguments = 1 },
        new("metadata.initialize-inline", ["_Z49il2cpp_codegen_initialize_runtime_metadata_inlinePm", "_ZN6il2cpp2vm13MetadataCache25InitializeRuntimeMetadataEPm"], RuntimeEffect.Unobservable, Returns: true, Observable: false,
            Idempotent: true, ExceptionKind.None, "元数据槽的地址", "槽初始化之后的内容", "把槽里的编码换成运行时对象的指针；只写映像里的元数据槽",
            "codegen/il2cpp-codegen-il2cpp.cpp: il2cpp_codegen_initialize_runtime_metadata_inline 返回 MetadataCache::InitializeRuntimeMetadata 的结果；vm/MetadataCache.cpp: InitializeRuntimeMetadata 返回 *metadataPointer")
            { ReturnsSlot = true, Arguments = 1 },
        new("class.initialize-metadata", ["_ZN6il2cpp2vm12ClassInlines19InitFromCodegenSlowEP11Il2CppClass"], RuntimeEffect.Unobservable,
            Returns: true, Observable: false, Idempotent: true, ExceptionKind.None, "类", "输入的类", "初始化类元数据",
            "vm/ClassInlines.cpp: InitFromCodegenSlow 调用 Class::Init，正常返回原类；设计 16.2 排除类型加载错误")
            { Arguments = 1, ReturnsArgument = true },
        new("method.initialize-rgctx", ["_ZN6il2cpp2vm12ClassInlines24InitRgctxFromCodegenSlowEPK10MethodInfo"], RuntimeEffect.Unobservable,
            Returns: true, Observable: false, Idempotent: true, ExceptionKind.None, "方法结构", "输入的方法结构", "填充方法上下文表",
            "vm/ClassInlines.cpp: InitRgctxFromCodegenSlow 调用 GenericMethod::InflateRGCTX 后返回原方法")
            { Arguments = 1, ReturnsArgument = true },
        new("gc.write-barrier", ["_Z25Il2CppCodeGenWriteBarrierPPvS_", "_ZN6il2cpp2gc16GarbageCollector15SetWriteBarrierEPPv",
            "_ZN6il2cpp2gc16GarbageCollector15SetWriteBarrierEPPvm"], RuntimeEffect.Unobservable, Returns: true, Observable: false,
            Idempotent: true, ExceptionKind.None, "被写位置的地址；生成代码入口另取写入的引用，范围重载另取字节数", "无",
            "通知回收器相应位置已写入，只改回收器私有状态。托管存入由调用者完成",
            "codegen/il2cpp-codegen-common.cpp: Il2CppCodeGenWriteBarrier；gc/BoehmGC.cpp、gc/GarbageCollector.cpp: SetWriteBarrier。语料 DWARF 的两个重载分别取 void** 和 (void**, size_t)") { Arguments = 2 },
        new("type.is-instance", ["_Z6IsInstP12Il2CppObjectP11Il2CppClass", "_ZN6il2cpp2vm6Object6IsInstEP12Il2CppObjectP11Il2CppClass"], RuntimeEffect.Pure, Returns: true,
            Observable: false, Idempotent: true, ExceptionKind.None, "对象、类", "对象可以当作该类使用时是对象自己，否则为空", "无；只读对象的类与类的继承、接口数据（运行时不可变）",
            "codegen/il2cpp-codegen-il2cpp.cpp: IsInst；vm/Object.cpp: Object::IsInst（导入类型与 Windows 运行时的分支在本平台不出现）")
            { Function = RuntimeFunction.IsInstance, Arguments = 2 },
        new("type.class-is-assignable-from", ["_Z39il2cpp_codegen_class_is_assignable_fromP11Il2CppClassS0_", "il2cpp_class_is_assignable_from",
            "_ZN6il2cpp2vm5Class16IsAssignableFromEP11Il2CppClassS3_"], RuntimeEffect.Pure, Returns: true, Observable: false,
            Idempotent: true, ExceptionKind.None, "目标类、来源类", "C++ bool：来源类的实例能否赋给目标类", "只查询类的赋值关系",
            "codegen/il2cpp-codegen-il2cpp.cpp：il2cpp_codegen_class_is_assignable_from 与 il2cpp-api.cpp：il2cpp_class_is_assignable_from 均转交 vm/Class.cpp：Class::IsAssignableFrom")
            { Function = RuntimeFunction.ClassIsAssignableFrom, Arguments = 2 },
        new("exception.array-type-mismatch", ["_Z48il2cpp_codegen_get_array_type_mismatch_exceptionv", "_ZN6il2cpp2vm9Exception29GetArrayTypeMismatchExceptionEv"], RuntimeEffect.MakeException, Returns: true,
            Observable: false, Idempotent: false, ExceptionKind.ArrayTypeMismatch, "无", "新的 ArrayTypeMismatchException 对象", "分配一个异常对象；它在被抛出之前不可见",
            "codegen/il2cpp-codegen-il2cpp.cpp: il2cpp_codegen_get_array_type_mismatch_exception；vm/Exception.cpp: Exception::GetArrayTypeMismatchException") { Arguments = 0 },
        new("raise.exception", ["_Z30il2cpp_codegen_raise_exceptionP11Exception_tP10MethodInfo"], RuntimeEffect.ThrowArgument, Returns: false,
            Observable: true, Idempotent: false, ExceptionKind.None, "异常对象、最近的托管帧", "不返回", "抛出实参给出的异常对象（先清空它的栈迹字段）",
            "codegen/il2cpp-codegen-il2cpp.cpp: il2cpp_codegen_raise_exception；vm/Exception.cpp: Exception::Raise") { Arguments = 2 },
        new("exception.begin-catch", ["__cxa_begin_catch"], RuntimeEffect.Pure, Returns: true, Observable: false,
            Idempotent: true, ExceptionKind.None, "展开异常指针", "捕获的包装对象地址", "更新 C++ 运行时私有的捕获状态",
            "Itanium C++ ABI 异常处理：__cxa_begin_catch 返回调整后的捕获对象指针") { Function = RuntimeFunction.BeginCatch, Arguments = 1 },
        new("exception.end-catch", ["__cxa_end_catch"], RuntimeEffect.Unobservable, Returns: true, Observable: false,
            Idempotent: false, ExceptionKind.None, "无", "无", "结束当前处理块，更新 C++ 运行时私有的捕获状态",
            "Itanium C++ ABI 异常处理：__cxa_end_catch；il2cpp-object-internals.h：Il2CppExceptionWrapper 只持有托管异常指针") { Arguments = 0 },
        new("exception.resume", ["_Unwind_Resume"], RuntimeEffect.Resume, Returns: false, Observable: true,
            Idempotent: false, ExceptionKind.None, "展开异常指针", "不返回", "清理结束后继续当前异常的展开",
            "Itanium C++ ABI 异常处理：_Unwind_Resume") { Arguments = 1 },
        new("exception.rethrow", ["__cxa_rethrow"], RuntimeEffect.Resume, Returns: false, Observable: true,
            Idempotent: false, ExceptionKind.None, "无", "不返回", "重新抛出当前捕获的异常",
            "Itanium C++ ABI 异常处理：__cxa_rethrow") { Arguments = 0 },
        new("exception.rethrow-argument", ["_ZN6il2cpp5utils16RethrowExceptionEP15Il2CppException", "_Z32il2cpp_codegen_rethrow_exceptionP11Exception_t"],
            RuntimeEffect.ThrowArgument, Returns: false, Observable: true, Idempotent: false, ExceptionKind.None,
            "托管异常对象", "不返回", "以实参为 ex 构造包装并抛出",
            "vm-utils/Finally.h、Finally.cpp：RethrowException；codegen/il2cpp-codegen-il2cpp.cpp：il2cpp_codegen_rethrow_exception；两者均调用 vm/Exception.cpp 的 Exception::Rethrow") { Arguments = 1 },
        new("class.initialize", ["_Z33il2cpp_codegen_runtime_class_initP11Il2CppClass", "_ZN6il2cpp2vm7Runtime9ClassInitEP11Il2CppClass"], RuntimeEffect.ClassInitialize, Returns: true, Observable: true,
            Idempotent: true, ExceptionKind.None, "类", "无", "执行该类的类型初始化器（至多一次）；返回时该类的初始化已触发",
            "vm/Runtime.cpp: Runtime::ClassInit；codegen/il2cpp-codegen-il2cpp.h: il2cpp_codegen_runtime_class_init_inline") { Arguments = 1 },
        new("object.new", ["_Z25il2cpp_codegen_object_newP11Il2CppClass", "_ZN6il2cpp2vm6Object3NewEP11Il2CppClass"], RuntimeEffect.NewObject, Returns: true, Observable: true,
            Idempotent: false, ExceptionKind.None, "类", "新实例；Nullable<T> 使用底层类 T", "分配零初始化实例，按类登记终结器，再触发实际分配类的类初始化；静态构造失败时传播 TypeInitializationException",
            "codegen/il2cpp-codegen-il2cpp.cpp: il2cpp_codegen_object_new；vm/Object.cpp: Object::New、Object::NewAllocSpecific；vm/Runtime.cpp: Runtime::ClassInit") { Arguments = 1 },
        new("array.new-vector", ["_Z10SZArrayNewP11Il2CppClassj"], RuntimeEffect.NewArray, Returns: true, Observable: true,
            Idempotent: false, ExceptionKind.Overflow, "数组类、uint32_t 长度", "指定长度的新一维零基数组", "准备数组类的运行时数据；长度超过 IL2CPP_ARRAY_MAX_INDEX 则抛出 OverflowException，否则分配默认初始化的元素区，写入长度",
            "codegen/il2cpp-codegen-il2cpp.cpp: SZArrayNew；vm/Array.cpp: Array::NewSpecific、RaiseOverflowException") { Arguments = 2 },
        new("type.cast-sealed", ["_Z15CastclassSealedP12Il2CppObjectP11Il2CppClass"], RuntimeEffect.ReadOrThrow, Returns: true, Observable: true,
            Idempotent: false, ExceptionKind.InvalidCast, "对象、目标密封类", "空对象或类相符时返回原引用", "非空时比较对象的类与目标类，不相等则构造并抛出 InvalidCastException",
            "codegen/il2cpp-codegen-il2cpp.h: CastclassSealed、IsInstSealed；codegen/il2cpp-codegen-il2cpp.cpp: RaiseInvalidCastException") { Arguments = 2 },
        new("raise.invalid-cast", ["_Z25RaiseInvalidCastExceptionP12Il2CppObjectP11Il2CppClass"], RuntimeEffect.Throw, Returns: false, Observable: true,
            Idempotent: false, ExceptionKind.InvalidCast, "非空对象、目标类", "不返回", "按对象类的元素类和目标类构造异常消息，抛出 InvalidCastException",
            "codegen/il2cpp-codegen-il2cpp.cpp: RaiseInvalidCastException、il2cpp_codegen_get_invalid_cast_exception、il2cpp_codegen_raise_exception") { Arguments = 2 },
    ];

    private static readonly FrozenDictionary<string, RuntimeOperation> bySymbol =
        entries.SelectMany(e => e.Symbols.Select(s => (s, e))).ToFrozenDictionary(p => p.s, p => p.e);

    public static ImmutableArray<RuntimeOperation> Entries => entries;

    /// <summary>按符号名找登记项。</summary>
    public static RuntimeOperation? BySymbol(string symbol) => bySymbol.GetValueOrDefault(symbol);
}
