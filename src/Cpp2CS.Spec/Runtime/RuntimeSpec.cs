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
    public int Arguments { get; init; }
}

/// <summary>具名函数的等式（设计 7.8）。每条写明出处。</summary>
public static class RuntimeEquations
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
            "无", "不返回", "构造异常对象并抛出", source);

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
        new("metadata.initialize", ["_Z42il2cpp_codegen_initialize_runtime_metadataPm", "_Z49il2cpp_codegen_initialize_runtime_metadata_inlinePm"], RuntimeEffect.Unobservable, Returns: true, Observable: false,
            Idempotent: true, ExceptionKind.None, "元数据槽的地址", "无", "把槽里的编码换成运行时对象的指针；只写映像里的元数据槽",
            "codegen/il2cpp-codegen-il2cpp.cpp: il2cpp_codegen_initialize_runtime_metadata、il2cpp_codegen_initialize_runtime_metadata_inline；vm/MetadataCache.cpp: InitializeRuntimeMetadata"),
        new("gc.write-barrier", ["_Z25Il2CppCodeGenWriteBarrierPPvS_"], RuntimeEffect.Unobservable, Returns: true, Observable: false,
            Idempotent: true, ExceptionKind.None, "被写位置的地址、写入的引用", "无", "通知垃圾回收器这个位置被写过；只改回收器的私有状态，不写托管位置（存入本身由生成代码完成）",
            "codegen/il2cpp-codegen-common.cpp: Il2CppCodeGenWriteBarrier；gc/BoehmGC.cpp: GarbageCollector::SetWriteBarrier"),
        new("type.is-instance", ["_Z6IsInstP12Il2CppObjectP11Il2CppClass", "_ZN6il2cpp2vm6Object6IsInstEP12Il2CppObjectP11Il2CppClass"], RuntimeEffect.Pure, Returns: true,
            Observable: false, Idempotent: true, ExceptionKind.None, "对象、类", "对象可以当作该类使用时是对象自己，否则为空", "无；只读对象的类与类的继承、接口数据（运行时不可变）",
            "codegen/il2cpp-codegen-il2cpp.cpp: IsInst；vm/Object.cpp: Object::IsInst（导入类型与 Windows 运行时的分支在本平台不出现）")
            { Function = RuntimeFunction.IsInstance, Arguments = 2 },
        new("exception.array-type-mismatch", ["_Z48il2cpp_codegen_get_array_type_mismatch_exceptionv"], RuntimeEffect.MakeException, Returns: true,
            Observable: false, Idempotent: false, ExceptionKind.ArrayTypeMismatch, "无", "新的 ArrayTypeMismatchException 对象", "分配一个异常对象；它在被抛出之前不可见",
            "codegen/il2cpp-codegen-il2cpp.cpp: il2cpp_codegen_get_array_type_mismatch_exception；vm/Exception.cpp: Exception::GetArrayTypeMismatchException"),
        new("raise.exception", ["_Z30il2cpp_codegen_raise_exceptionP11Exception_tP10MethodInfo"], RuntimeEffect.ThrowArgument, Returns: false,
            Observable: true, Idempotent: false, ExceptionKind.None, "异常对象、最近的托管帧", "不返回", "抛出实参给出的异常对象（先清空它的栈迹字段）",
            "codegen/il2cpp-codegen-il2cpp.cpp: il2cpp_codegen_raise_exception；vm/Exception.cpp: Exception::Raise"),
        new("class.initialize", ["_Z33il2cpp_codegen_runtime_class_initP11Il2CppClass", "_ZN6il2cpp2vm7Runtime9ClassInitEP11Il2CppClass"], RuntimeEffect.ClassInitialize, Returns: true, Observable: true,
            Idempotent: true, ExceptionKind.None, "类", "无", "执行该类的类型初始化器（至多一次）；返回时该类的初始化已触发",
            "vm/Runtime.cpp: Runtime::ClassInit；codegen/il2cpp-codegen-il2cpp.h: il2cpp_codegen_runtime_class_init_inline"),
    ];

    private static readonly FrozenDictionary<string, RuntimeOperation> bySymbol =
        entries.SelectMany(e => e.Symbols.Select(s => (s, e))).ToFrozenDictionary(p => p.s, p => p.e);

    public static ImmutableArray<RuntimeOperation> Entries => entries;

    /// <summary>按符号名找登记项。</summary>
    public static RuntimeOperation? BySymbol(string symbol) => bySymbol.GetValueOrDefault(symbol);
}

/// <summary>
/// 运行时结构的布局。每个数字注明出处（相对 libil2cpp 目录的头文件与成员）。
/// 这一份是 Unity 2022.3、指针 64 位（LP64）。
/// </summary>
public sealed record RuntimeLayout(int PointerBits,
    // il2cpp-object-internals.h: Il2CppObject { Il2CppClass* klass; MonitorData* monitor; }
    int ObjectHeaderBytes,
    // il2cpp-object-internals.h: Il2CppArray { Il2CppObject obj; Il2CppArrayBounds* bounds; il2cpp_array_size_t max_length; }
    // 生成代码按 uint32 读长度：IL2CPP_ARRAY_BOUNDS_CHECK(index, (uint32_t)(this)->max_length)。
    int ArrayLengthOffset, int ArrayLengthBits,
    // il2cpp-object-internals.h: IL2CPP_ARRAY_MAX_INDEX（0x7fffffff）；vm/Array.cpp 的 NewSpecific 在长度超过它时抛出。长度不超过这个值。
    long ArrayLengthMaximum,
    // il2cpp-object-internals.h: kIl2CppSizeOfArray；Il2CppArraySize 的 vector 成员紧随 max_length。
    int ArrayDataOffset,
    // il2cpp-class-internals.h: Il2CppClass::static_fields；生成代码经 il2cpp_codegen_static_fields_for 读它。
    int ClassStaticFieldsOffset,
    // il2cpp-class-internals.h: Il2CppClass::cctor_finished_or_no_cctor（uint32_t）；il2cpp_codegen_runtime_class_init_inline 测试它。
    // 它只会从 0 变为非 0：单调状态（设计 7.4）。
    int ClassInitializedOffset, int ClassInitializedBits)
{
    public static RuntimeLayout Unity2022Lp64 { get; } = new(64, ObjectHeaderBytes: 16, ArrayLengthOffset: 24, ArrayLengthBits: 32, ArrayLengthMaximum: 0x7fffffff, ArrayDataOffset: 32,
        ClassStaticFieldsOffset: 0xb8, ClassInitializedOffset: 0xe0, ClassInitializedBits: 32);
}
