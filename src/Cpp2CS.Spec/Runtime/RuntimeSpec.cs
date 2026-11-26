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
    /// <summary>原型使用的前几个整数实参槽。这份登记中的原型没有栈、浮点或间接结果实参。</summary>
    public int Arguments { get; init; } = -1;
    /// <summary>结果是第 0 个实参所指的元数据槽在初始化之后的内容（类指针、方法、字符串等运行时对象的指针）。</summary>
    public bool ReturnsSlot { get; init; }
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
        new("gc.write-barrier", ["_Z25Il2CppCodeGenWriteBarrierPPvS_"], RuntimeEffect.Unobservable, Returns: true, Observable: false,
            Idempotent: true, ExceptionKind.None, "被写位置的地址、写入的引用", "无", "通知垃圾回收器这个位置被写过；只改回收器的私有状态，不写托管位置（存入本身由生成代码完成）",
            "codegen/il2cpp-codegen-common.cpp: Il2CppCodeGenWriteBarrier；gc/BoehmGC.cpp: GarbageCollector::SetWriteBarrier") { Arguments = 2 },
        new("type.is-instance", ["_Z6IsInstP12Il2CppObjectP11Il2CppClass", "_ZN6il2cpp2vm6Object6IsInstEP12Il2CppObjectP11Il2CppClass"], RuntimeEffect.Pure, Returns: true,
            Observable: false, Idempotent: true, ExceptionKind.None, "对象、类", "对象可以当作该类使用时是对象自己，否则为空", "无；只读对象的类与类的继承、接口数据（运行时不可变）",
            "codegen/il2cpp-codegen-il2cpp.cpp: IsInst；vm/Object.cpp: Object::IsInst（导入类型与 Windows 运行时的分支在本平台不出现）")
            { Function = RuntimeFunction.IsInstance, Arguments = 2 },
        new("exception.array-type-mismatch", ["_Z48il2cpp_codegen_get_array_type_mismatch_exceptionv", "_ZN6il2cpp2vm9Exception29GetArrayTypeMismatchExceptionEv"], RuntimeEffect.MakeException, Returns: true,
            Observable: false, Idempotent: false, ExceptionKind.ArrayTypeMismatch, "无", "新的 ArrayTypeMismatchException 对象", "分配一个异常对象；它在被抛出之前不可见",
            "codegen/il2cpp-codegen-il2cpp.cpp: il2cpp_codegen_get_array_type_mismatch_exception；vm/Exception.cpp: Exception::GetArrayTypeMismatchException") { Arguments = 0 },
        new("raise.exception", ["_Z30il2cpp_codegen_raise_exceptionP11Exception_tP10MethodInfo"], RuntimeEffect.ThrowArgument, Returns: false,
            Observable: true, Idempotent: false, ExceptionKind.None, "异常对象、最近的托管帧", "不返回", "抛出实参给出的异常对象（先清空它的栈迹字段）",
            "codegen/il2cpp-codegen-il2cpp.cpp: il2cpp_codegen_raise_exception；vm/Exception.cpp: Exception::Raise") { Arguments = 2 },
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
