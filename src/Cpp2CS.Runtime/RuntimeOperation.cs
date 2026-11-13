using System.Collections.Frozen;
using System.Collections.Immutable;

namespace Cpp2CS.Runtime;

public enum RuntimeInputUse { Value, Location, Pointee }
public enum RuntimeValueKind { Void, ManagedReference, Class, Method, Metadata, Integer, Boolean, NativePointer, ManagedAddress, InvokeData }
public enum RuntimeWidth { None, Bit, Int32, Int64, Pointer }
public enum RuntimeHeapEffect { None, Read, MayWrite, ArbitraryManagedCode }
public enum RuntimeObservation { Observable, Unobservable, IdempotentEvent }
public enum RuntimeMemoryDomain { Frame, ImmutableRuntime, Monotone, ManagedHeap, RuntimePrivate }
public enum RuntimeEventTrigger { Always, NormalOnly, ExceptionalOnly, StateNotEstablished, Never }
public enum RuntimeConditionKind { Always, NormalReturn, ExceptionalExit, StateNotEstablished, Other }
public enum RuntimeExtentKind { FixedBytes, PointerSlot, ClassValueSize, InputLength, Unknown }
/// <summary>InstanceOfInput：结果是 Input 所指的类的实例（精确类型）。</summary>
public enum RuntimeResultRelationKind { None, Identity, InputOrNull, ResolvedPointee, InstanceOfInput }
public sealed record RuntimeCondition(RuntimeConditionKind Kind, string Description);
public sealed record RuntimeExtent(RuntimeExtentKind Kind, string Description, string? Input = null, int Bytes = 0, int ElementBytes = 1);
public sealed record RuntimeResultRelation(RuntimeResultRelationKind Kind, string? Input = null, string? Evidence = null);
public enum RuntimeTermination { None, Throw, ResumeUnwind, ProcessTermination }
public enum RuntimeAccess { Read, Write, ReadWrite }
public enum RuntimeStateTest { Nonzero, Zero, ResolvedMetadata }

public sealed record RuntimeInput(string Name, RuntimeInputUse Use, RuntimeValueKind Kind);
public sealed record RuntimeResult(RuntimeValueKind Kind, RuntimeWidth Width, RuntimeResultRelation Relation)
{
    public string? ReturnInput => Relation.Kind == RuntimeResultRelationKind.Identity ? Relation.Input : null;
    /// <summary>正常返回的引用可赋给此类输入；不声称对象的动态类型精确相等。</summary>
    public string? ReferenceTypeInput { get; init; }
}
public sealed record RuntimePointerEffect(string Input, RuntimeAccess Access, RuntimeMemoryDomain Domain, RuntimeExtent Extent, RuntimeCondition Condition);
// 结构字段按名字引用；匿名元数据槽由外部全局访问凭据确认，不伪装为结构字段。
public sealed record RuntimeStateRepresentation(string Input, string? Record, string? Field, RuntimeStateTest Test, string Evidence);
public sealed record RuntimePostcondition(string Predicate, RuntimeCondition When, string Description, ImmutableArray<RuntimeStateRepresentation> Representations);
/// <summary>有效开放实体的元数据发布由托管上下文承担；不包含类静态构造。</summary>
public sealed record RuntimeMetadataInitialization(string Input, string Evidence);
public sealed record RuntimeExceptions(bool MayThrow, ImmutableArray<string> Types, bool IsUpperBound, string Description);
public sealed record RuntimeIlForm(string Name, string Description);
public sealed record RuntimeOperation(
    string Name, ImmutableArray<RuntimeInput> Inputs, RuntimeResult Result,
    RuntimeHeapEffect HeapEffect, ImmutableArray<RuntimePointerEffect> PointerEffects,
    RuntimeObservation Observation, RuntimePostcondition? Idempotence,
    ImmutableArray<RuntimePostcondition> Normal, ImmutableArray<RuntimePostcondition> Exceptional,
    RuntimeExceptions Exceptions, bool DoesNotReturn, RuntimeIlForm Il,
    string Preconditions, string Evidence, RuntimeEventTrigger EventTrigger, RuntimeTermination Termination,
    string SynchronousManagedCode)
{
    /// <summary>无条件抛出的固定异常；传入异常对象及重新抛出不设置此项。</summary>
    public string? FixedThrownException { get; init; }
    public string? RelaxedClassInput { get; init; }
    public RuntimeMetadataInitialization? MetadataInitialization { get; init; }

    public RuntimeCondition? EventCondition => EventTrigger switch
    {
        RuntimeEventTrigger.Never => null,
        RuntimeEventTrigger.Always => new(RuntimeConditionKind.Always, "调用时"),
        RuntimeEventTrigger.NormalOnly => new(RuntimeConditionKind.NormalReturn, "仅正常返回"),
        RuntimeEventTrigger.ExceptionalOnly => new(RuntimeConditionKind.ExceptionalExit, "仅异常退出"),
        RuntimeEventTrigger.StateNotEstablished => new(RuntimeConditionKind.StateNotEstablished, Idempotence!.Description),
        _ => throw new InvalidOperationException("事件条件缺少定义")
    };
}

/// <summary>语义只在此表定义。后置条件是具名事实及适用条件，不是已实现的证明规则。</summary>
public static class RuntimeOperations
{
    public static FrozenDictionary<string, RuntimeOperation> All { get; } = Build().ToFrozenDictionary(o => o.Name, StringComparer.Ordinal);
    public static RuntimeOperation Get(string name) => All.TryGetValue(name, out var op) ? op :
        throw new KeyNotFoundException($"运行时操作未登记：{name}");

    private static RuntimeInput V(string name, RuntimeValueKind kind) => new(name, RuntimeInputUse.Value, kind);
    private static RuntimeInput P(string name, RuntimeValueKind kind) => new(name, RuntimeInputUse.Pointee, kind);
    private static RuntimePostcondition Fact(string name, string description, string when = "正常返回", params RuntimeStateRepresentation[] fields) => new(name, new(when == "正常返回" ? RuntimeConditionKind.NormalReturn : when == "异常退出" ? RuntimeConditionKind.ExceptionalExit : RuntimeConditionKind.Other, when), description, [.. fields]);
    private static RuntimeStateRepresentation Field(string input, string record, string field, RuntimeStateTest test = RuntimeStateTest.Nonzero) =>
        new(input, record, field, test, "对应版本布局与运行时实现");
    private static RuntimePointerEffect Read(string input, string extent, RuntimeMemoryDomain domain = RuntimeMemoryDomain.ManagedHeap) => new(input, RuntimeAccess.Read, domain, new(RuntimeExtentKind.Unknown, extent), new(RuntimeConditionKind.Always, "调用时"));
    private static RuntimeOperation Op(string name, RuntimeInput[] inputs, RuntimeValueKind result, RuntimeWidth width,
        RuntimeHeapEffect heap, RuntimeObservation observation, string normal, string il, string description,
        string evidence, string[]? exceptions = null, RuntimePointerEffect[]? pointers = null, string? returnInput = null,
        RuntimePostcondition? idempotence = null, RuntimePostcondition[]? post = null, bool noReturn = false,
        string preconditions = "Unity 2022.3 Android LP64 的匹配基础库；生成器保证类型、元数据指针与缓冲区合法；无自定义 profiler 回调；原生耗尽及内存损坏不作为托管结局", bool upperBound = false, RuntimeEventTrigger? trigger = null, RuntimeTermination termination = RuntimeTermination.Throw, RuntimePostcondition[]? exceptional = null, bool inputOrNull = false, string managedCode = "无用户代码；异常构造可能调用基础库构造函数", string? exceptionReason = null, RuntimeResultRelation? resultRelation = null, string? referenceTypeInput = null) =>
        new(name, [.. inputs], new(result, width, resultRelation ?? new(returnInput is null ? RuntimeResultRelationKind.None : inputOrNull ? RuntimeResultRelationKind.InputOrNull : RuntimeResultRelationKind.Identity, returnInput)) { ReferenceTypeInput = referenceTypeInput }, heap, [.. pointers ?? []], observation, idempotence,
            noReturn ? [] : post is null ? [Fact(name + "Result", normal)] : [.. post],
            exceptional is not null ? [.. exceptional] : exceptions is { Length: > 0 } ? [Fact(name + "Exception", "抛出所列异常；不承诺正常后置条件，堆效果仍适用", "异常退出")] : [],
            new(exceptions is { Length: > 0 }, [.. exceptions ?? []], upperBound,
                exceptionReason ?? (upperBound ? "见函数级依据中的未闭合调用" : "列出托管异常；原生分配耗尽与损坏不作为可恢复结局")),
            noReturn, new(il, description), preconditions, evidence,
            trigger ?? (observation == RuntimeObservation.Unobservable ? RuntimeEventTrigger.Never :
                observation == RuntimeObservation.IdempotentEvent ? RuntimeEventTrigger.StateNotEstablished : RuntimeEventTrigger.Always),
            noReturn ? termination : RuntimeTermination.None, managedCode);

    private static IEnumerable<RuntimeOperation> Build()
    {
        const string codegen = "codegen/il2cpp-codegen-il2cpp";
        var klass = P("class", RuntimeValueKind.Class);
        var obj = P("object", RuntimeValueKind.ManagedReference);
        var method = P("method", RuntimeValueKind.Method);
        yield return Op("AllocateObject", [klass], RuntimeValueKind.ManagedReference, RuntimeWidth.Pointer,
            RuntimeHeapEffect.ArbitraryManagedCode, RuntimeObservation.Observable, "分配指定类对象；可能先触发类初始化", "NewObject", "分配对象，与随后的构造函数调用合成 newobj", "vm/Object.cpp: Object::New → NewAllocSpecific → Class::Init / Allocate / AllocateSpec / NewPtrFree → Runtime::ClassInit; vm/Runtime.cpp: ClassInit → Invoke(cctor)；用户静态构造可改写既有对象与静态字段", ["System.TypeInitializationException", "System.TypeLoadException", "System.NotSupportedException"], upperBound: false, exceptionReason: "封闭的异常种类集合；泛型深度失败见 vm/GenericClass.cpp: CreateClass → vm/Exception.cpp: GetMaximumNestedGenericsException；未解析方法桩只被登记，不在此调用", managedCode: "当前线程可能执行输入类静态构造；分配触发的终结器在其他线程执行", resultRelation: new(RuntimeResultRelationKind.InstanceOfInput, "class"));
        yield return Op("AllocateVector", [klass, V("length", RuntimeValueKind.Integer)], RuntimeValueKind.ManagedReference, RuntimeWidth.Pointer,
            RuntimeHeapEffect.MayWrite, RuntimeObservation.Observable, "新向量的长度等于 length，元素为默认值", "NewArray", "写成 newarr", "vm/Array.cpp: Array::NewSpecific → Class::Init / RaiseOverflowException / Object::AllocatePtrFree / AllocateSpec / Allocate; vm/Class.cpp: InitLocked → SetupFieldsLocked; vm/Exception.cpp: FromNameMsg → Runtime::ObjectInit；分配只写新数组，异常构造可能初始化基础库静态字段", ["System.OverflowException", "System.TypeLoadException", "System.TypeInitializationException", "System.NotSupportedException"], upperBound: false, exceptionReason: "封闭的异常种类集合；泛型深度失败见 vm/GenericClass.cpp: CreateClass → vm/Exception.cpp: GetMaximumNestedGenericsException；未解析方法桩只被登记，不在此调用", managedCode: "不调用元素类静态构造；失败路径同步调用基础库异常构造；GC 终结器在其他线程执行", resultRelation: new(RuntimeResultRelationKind.InstanceOfInput, "class"));
        yield return Op("AllocateArray", [klass, P("dimensions", RuntimeValueKind.Integer)], RuntimeValueKind.ManagedReference, RuntimeWidth.Pointer,
            RuntimeHeapEffect.MayWrite, RuntimeObservation.Observable, "新数组的各维长度来自 dimensions，元素为默认值", "NewMultiArray", "写成多维数组构造", "codegen/il2cpp-codegen-il2cpp.cpp: GenArrayNew → vm/Array.cpp: Array::NewFull → Class::Init / RaiseOverflowException / Object::Allocate*；只写新数组；异常工厂见 vm/Exception.cpp: FromNameMsg", ["System.OverflowException", "System.TypeLoadException", "System.TypeInitializationException", "System.NotSupportedException"], [Read("dimensions", "class 的秩乘以目录中 il2cpp_array_size_t 的大小")], upperBound: false, exceptionReason: "封闭的异常种类集合；泛型深度失败见 vm/GenericClass.cpp: CreateClass → vm/Exception.cpp: GetMaximumNestedGenericsException；未解析方法桩只被登记，不在此调用", managedCode: "同 AllocateVector；不调用元素类静态构造，终结器在其他线程执行");
        yield return Op("AllocateStringUtf8", [P("characters", RuntimeValueKind.Integer)], RuntimeValueKind.ManagedReference, RuntimeWidth.Pointer,
            RuntimeHeapEffect.Read, RuntimeObservation.Observable, "返回 characters 的 UTF-8 解码字符串", "NewStringUtf8", "按编码与来源还原字符串构造", "vm/String.cpp: String::NewWrapper → New → NewLen → NewUtf16 → NewSize / Empty → Object::AllocatePtrFree; utils/StringUtils.cpp: Utf8ToUtf16 → utf8::unchecked::utf8to16；合法长度的 LP64 分配只写新字符串，NewSize 的大小溢出分支不可达", [], [Read("characters", "至首个零字节")], upperBound: false, managedCode: "无同步托管代码；gc/BoehmGC.cpp: GC_set_finalize_on_demand；gc/GarbageCollector.cpp: NotifyFinalizers / FinalizerThread 在其他线程运行终结器");
        yield return Op("Box", [klass, P("data", RuntimeValueKind.ManagedAddress)], RuntimeValueKind.ManagedReference, RuntimeWidth.Pointer,
            RuntimeHeapEffect.ArbitraryManagedCode, RuntimeObservation.Observable, "值类型复制为盒；Nullable 无值时返回 null；引用型取 data 中的引用", "Box", "写成 box；Nullable 与引用型按具体类型解释", "vm/Object.cpp: Object::Box → NullableHasValue / New → NewAllocSpecific → Runtime::ClassInit；复制只写新盒，静态构造可改写已有堆", ["System.TypeInitializationException", "System.TypeLoadException", "System.NotSupportedException"], [new("data", RuntimeAccess.Read, RuntimeMemoryDomain.ManagedHeap, new(RuntimeExtentKind.ClassValueSize, "class 指定的值存储大小", "class"), new(RuntimeConditionKind.Always, "调用时"))], upperBound: false, exceptionReason: "封闭的异常种类集合；泛型深度失败见 vm/GenericClass.cpp: CreateClass → vm/Exception.cpp: GetMaximumNestedGenericsException；未解析方法桩只被登记，不在此调用", managedCode: "值类型分配可能同步执行静态构造；引用型只读指针槽；Nullable 无值不分配；终结器不在本线程执行");
        yield return Op("InitializeMetadata", [new("slot", RuntimeInputUse.Location, RuntimeValueKind.Metadata)], RuntimeValueKind.Metadata, RuntimeWidth.Pointer,
            RuntimeHeapEffect.MayWrite, RuntimeObservation.Unobservable, "元数据槽解析完成，结果为解析的实体指针", "EraseMetadataInitialization", "以解析后的实体替代槽读取，消去初始化效果", "vm/MetadataCache.cpp: InitializeRuntimeMetadata → vm/GlobalMetadata.cpp: InitializeRuntimeMetadata → GetTypeInfoFromTypeIndex / GetMethodInfoFromEncodedIndex / GetFieldInfoFromIndex / GetStringLiteralFromIndex；类型分支经 ClassInlines::InitFromCodegenSlow，字符串经 String::NewUtf16；只发布元数据，异常路径可能写缓存异常的堆栈", ["System.TypeLoadException", "System.TypeInitializationException", "System.NotSupportedException"],
            [new("slot", RuntimeAccess.ReadWrite, RuntimeMemoryDomain.Monotone, new(RuntimeExtentKind.PointerSlot, "一个指针宽槽"), new(RuntimeConditionKind.Other, "全局访问凭据成立"))],
            post: [Fact("MetadataResolved", "slot 已解析；结果是槽内容而不是槽地址", fields: [new("slot", null, null, RuntimeStateTest.ResolvedMetadata, "需要整个二进制的访问凭据；不对匿名地址按形状分类")])], upperBound: false, exceptionReason: "封闭的异常种类集合；泛型深度失败见 vm/GenericClass.cpp: CreateClass → vm/Exception.cpp: GetMaximumNestedGenericsException；未解析方法桩只被登记，不在此调用", managedCode: "不执行输入类静态构造；失败时异常工厂执行基础库构造",
            resultRelation: new(RuntimeResultRelationKind.ResolvedPointee, "slot", "codegen/il2cpp-codegen-il2cpp.cpp: il2cpp_codegen_initialize_runtime_metadata_inline → vm/MetadataCache.cpp / vm/GlobalMetadata.cpp: InitializeRuntimeMetadata；有效实体正常返回时结果等于发布后的槽内容"));
        var cctor = Fact("ClassConstructorCompleted", "类静态构造已完成或无静态构造", "入口标志已成立时可消去；普通完成时建立，重入返回不保证", fields: [new("class", "Il2CppClass", "cctor_finished_or_no_cctor", RuntimeStateTest.Nonzero, "codegen/il2cpp-codegen-il2cpp.h: il2cpp_codegen_runtime_class_init_inline；vm/Runtime.cpp: Runtime::ClassInit 成功后置位，重入不置位；vm/GlobalMetadata.cpp: 无静态构造时初始置位")]);
        yield return Op("InitializeClassPrecise", [klass], RuntimeValueKind.Void, RuntimeWidth.None, RuntimeHeapEffect.ArbitraryManagedCode,
            RuntimeObservation.IdempotentEvent, "", "RunClassConstructor", "保持精确初始化时机，必要时写 RunClassConstructor", "vm/Runtime.cpp: Runtime::ClassInit → Class::GetCCtor → Runtime::Invoke → Exception::GetTypeInitializationException → Class::SetClassInitializationError → Exception::Raise；缓存也可来自 vm/Class.cpp: SetupFieldsLocked / InitLocked 的 TypeLoadException", ["System.TypeInitializationException", "System.TypeLoadException", "System.NotSupportedException"],
            pointers: [new("class", RuntimeAccess.ReadWrite, RuntimeMemoryDomain.Monotone, new(RuntimeExtentKind.Unknown, "类构造状态与失败缓存"), new(RuntimeConditionKind.StateNotEstablished, "类构造未完成"))], idempotence: cctor, post: [cctor], upperBound: false, managedCode: "当前线程执行任意静态构造，可改写既有对象与静态字段；异常包装为 TypeInitializationException") with { RelaxedClassInput = "class" };
        yield return Op("InitializeClassBeforeFieldInit", [klass], RuntimeValueKind.Void, RuntimeWidth.None, RuntimeHeapEffect.ArbitraryManagedCode,
            RuntimeObservation.Unobservable, "", "EraseBeforeFieldInit", "在 beforefieldinit 契约下消去显式时机", "vm/Runtime.cpp: Runtime::ClassInit → Invoke(cctor) → Exception::GetTypeInitializationException / Raise；beforefieldinit 不消除静态构造的堆改写", ["System.TypeInitializationException", "System.TypeLoadException", "System.NotSupportedException"], pointers: [new("class", RuntimeAccess.ReadWrite, RuntimeMemoryDomain.Monotone, new(RuntimeExtentKind.Unknown, "类构造状态与失败缓存"), new(RuntimeConditionKind.StateNotEstablished, "类构造未完成"))], post: [cctor],
            preconditions: "必须由类型元数据证明 beforefieldinit；目录不从同一符号推断此事实", upperBound: false, managedCode: "同精确类初始化，beforefieldinit 只影响事件时机") with { RelaxedClassInput = "class" };
        var ready = Fact("ClassReady", "类布局初始化成功", "正常返回", Field("class", "Il2CppClass", "initialized_and_no_error"));
        yield return Op("EnsureClassReady", [klass], RuntimeValueKind.Class, RuntimeWidth.Pointer, RuntimeHeapEffect.MayWrite,
            RuntimeObservation.IdempotentEvent, "", "EnsureClassReady", "布局就绪由托管运行时承担；删除须证明成功状态", "vm/ClassInlines.cpp: InitFromCodegenSlow → vm/Class.cpp: Class::Init / InitLocked → SetupInterfacesLocked / SetupMethodsLocked / SetupVTable / SetupFieldsLocked / SetupEventsLocked / SetupPropertiesLocked / SetupNestedTypesLocked；不调用输入类 cctor；缓存错误经 vm/Exception.cpp: Raise → PrepareExceptionForThrow 修改既有异常堆栈", ["System.TypeLoadException", "System.TypeInitializationException", "System.NotSupportedException"],
            pointers: [new("class", RuntimeAccess.ReadWrite, RuntimeMemoryDomain.Monotone, new(RuntimeExtentKind.Unknown, "类就绪状态及惰性布局"), new(RuntimeConditionKind.StateNotEstablished, "尚未就绪"))], returnInput: "class", idempotence: ready, post: [ready], upperBound: false, exceptionReason: "封闭的异常种类集合；泛型深度失败见 vm/GenericClass.cpp: CreateClass → vm/Exception.cpp: GetMaximumNestedGenericsException；未解析方法桩只被登记，不在此调用", managedCode: "仅错误工厂的基础库构造；Class::Init 不等于 Runtime::ClassInit") with
            { MetadataInitialization = new("class", "codegen/il2cpp-codegen-il2cpp.h: InitializedTypeInfo；vm/ClassInlines.h: InitFromCodegen；有效开放实体的布局元数据由托管上下文建立") };
        var rgctx = Fact("MethodContextReady", "方法的非空泛型上下文已就绪", "正常返回且 RGCTX 集合非空；空集合不建立非零表示", Field("method", "MethodInfo", "rgctx_data"));
        yield return Op("InitializeMethodRgctx", [method], RuntimeValueKind.Method, RuntimeWidth.Pointer, RuntimeHeapEffect.MayWrite,
            RuntimeObservation.IdempotentEvent, "", "EnsureMethodContext", "泛型上下文初始化由托管运行时承担", "vm/ClassInlines.cpp: InitRgctxFromCodegenSlow → metadata/GenericMethod.cpp: InflateRGCTXData / InflateRGCTXDataLocked → metadata/GenericMetadata.cpp: InflateRGCTXDataLocked → InflateIfNeeded / Class::FromIl2CppType / InitSizeAndFieldLayoutLocked / GenericMethod::GetMethod / Class::InitLocked / GetVirtualMethod；只建立元数据；错误工厂可能初始化基础库静态字段", ["System.TypeLoadException", "System.TypeInitializationException", "System.NotSupportedException"],
            pointers: [new("method", RuntimeAccess.ReadWrite, RuntimeMemoryDomain.Monotone, new(RuntimeExtentKind.Unknown, "方法泛型上下文"), new(RuntimeConditionKind.StateNotEstablished, "尚未就绪"))], returnInput: "method", idempotence: rgctx, post: [rgctx], upperBound: false, exceptionReason: "封闭的异常种类集合；泛型深度失败见 vm/GenericClass.cpp: CreateClass → vm/Exception.cpp: GetMaximumNestedGenericsException；未解析方法桩只被登记，不在此调用", managedCode: "没有调用解析得到的方法或用户重载；只可能执行基础库错误构造") with
            { MetadataInitialization = new("method", "codegen/il2cpp-codegen-il2cpp.h: il2cpp_rgctx_method_init；vm/ClassInlines.h: InitRgcxFromCodegen；有效开放方法的 RGCTX 由托管上下文建立") };
        yield return Op("IsInstance", [obj, klass], RuntimeValueKind.ManagedReference, RuntimeWidth.Pointer, RuntimeHeapEffect.Read,
            RuntimeObservation.Unobservable, "object 可赋给 class 时返回原 object，否则 null；不保证恒等返回", "IsInst", "写成 isinst", codegen + ".h: IsInstClass/Sealed; .cpp: IsInst", pointers: [Read("object", "对象类及其类型关系", RuntimeMemoryDomain.ImmutableRuntime), Read("class", "目标类型关系", RuntimeMemoryDomain.ImmutableRuntime)], returnInput: "object", inputOrNull: true, referenceTypeInput: "class");
        yield return Op("IsAssignableFrom", [klass, P("candidate", RuntimeValueKind.Class)], RuntimeValueKind.Boolean, RuntimeWidth.Bit, RuntimeHeapEffect.Read,
            RuntimeObservation.Unobservable, "candidate 可赋给 class 时为真", "TypeAssignable", "作为类型关系查询", codegen + ".cpp: il2cpp_codegen_class_is_assignable_from", pointers: [Read("class", "目标类型关系", RuntimeMemoryDomain.ImmutableRuntime), Read("candidate", "候选类型关系", RuntimeMemoryDomain.ImmutableRuntime)]);
        yield return Op("CastClass", [obj, klass], RuntimeValueKind.ManagedReference, RuntimeWidth.Pointer, RuntimeHeapEffect.Read,
            RuntimeObservation.Observable, "object 为 null 或类型检查成功；结果恒等于 object", "CastClass", "写成 castclass", codegen + ".h: Castclass", ["System.InvalidCastException"], pointers: [Read("object", "对象类及其类型关系", RuntimeMemoryDomain.ImmutableRuntime), Read("class", "目标类型关系", RuntimeMemoryDomain.ImmutableRuntime)], returnInput: "object", trigger: RuntimeEventTrigger.ExceptionalOnly, referenceTypeInput: "class");
        yield return Op("Unbox", [obj, klass], RuntimeValueKind.ManagedAddress, RuntimeWidth.Pointer, RuntimeHeapEffect.Read,
            RuntimeObservation.Observable, "非空且元素类匹配，返回盒内数据地址", "Unbox", "写成 unbox", codegen + ".h: UnBox(obj, expectedBoxedClass)", ["System.NullReferenceException", "System.InvalidCastException"], trigger: RuntimeEventTrigger.ExceptionalOnly);
        yield return Op("UnboxAny", [obj, klass, new("storage", RuntimeInputUse.Location, RuntimeValueKind.ManagedAddress)], RuntimeValueKind.ManagedAddress, RuntimeWidth.Pointer, RuntimeHeapEffect.Read,
            RuntimeObservation.Observable, "普通值类型返回盒内地址；Nullable 或引用类型写 storage 并返回 storage", "UnboxAny", "写成 unbox.any 并保存所需结果位置", codegen + ".cpp: UnBox_Any", ["System.NullReferenceException", "System.InvalidCastException"],
            [Read("object", "盒内值；object 非空且为值类型时"), new("storage", RuntimeAccess.Write, RuntimeMemoryDomain.Frame, new(RuntimeExtentKind.ClassValueSize, "class 的值存储大小", "class"), new(RuntimeConditionKind.Other, "class 为 Nullable 或引用类型"))],
            preconditions: "storage 必须是足够大的帧缓冲区；运行时源码有此断言", trigger: RuntimeEventTrigger.ExceptionalOnly);
        yield return Op("UnboxNullable", [obj, klass, new("storage", RuntimeInputUse.Location, RuntimeValueKind.ManagedAddress)], RuntimeValueKind.Void, RuntimeWidth.None, RuntimeHeapEffect.MayWrite,
            RuntimeObservation.Observable, "storage 获得 Nullable 值；object 为 null 时 hasValue 为假", "UnboxNullable", "写成 Nullable 的 unbox.any", codegen + ".h: UnBoxNullable; .cpp: UnBoxNullable_internal", ["System.InvalidCastException"],
            [Read("object", "非空盒内值"), new("storage", RuntimeAccess.Write, RuntimeMemoryDomain.ManagedHeap, new(RuntimeExtentKind.ClassValueSize, "Nullable 的值存储大小", "class"), new(RuntimeConditionKind.NormalReturn, "正常返回"))], trigger: RuntimeEventTrigger.ExceptionalOnly);
        yield return Op("CheckNull", [V("value", RuntimeValueKind.NativePointer)], RuntimeValueKind.Void, RuntimeWidth.None, RuntimeHeapEffect.None,
            RuntimeObservation.Observable, "value 非零", "NullCheck", "由同一位置的 IL 访问吸收或保留条件抛出", codegen + ".h: NullCheck", ["System.NullReferenceException"], trigger: RuntimeEventTrigger.ExceptionalOnly);
        yield return Op("CheckDivideByZero", [V("denominator", RuntimeValueKind.Integer)], RuntimeValueKind.Void, RuntimeWidth.None, RuntimeHeapEffect.None,
            RuntimeObservation.Observable, "denominator 非零", "DivideCheck", "由整数除法吸收", codegen + ".h: DivideByZeroCheck", ["System.DivideByZeroException"], trigger: RuntimeEventTrigger.ExceptionalOnly);
        yield return Op("CheckArrayElementType", [V("array", RuntimeValueKind.ManagedReference), V("value", RuntimeValueKind.ManagedReference)], RuntimeValueKind.Void, RuntimeWidth.None, RuntimeHeapEffect.Read,
            RuntimeObservation.Observable, "value 为 null 或能赋给数组元素类型", "ArrayStoreCheck", "由 stelem.ref 吸收", codegen + ".h: ArrayElementTypeCheck", ["System.ArrayTypeMismatchException"], preconditions: "array 已判空且为引用元素数组", trigger: RuntimeEventTrigger.ExceptionalOnly);
        foreach (var (name, type, inputs) in new (string, string, RuntimeInput[])[] {
            ("ThrowNullReference", "System.NullReferenceException", []), ("ThrowBounds", "System.IndexOutOfRangeException", []),
            ("ThrowDivideByZero", "System.DivideByZeroException", []), ("ThrowOverflow", "System.OverflowException", [method]),
            ("ThrowInvalidCast", "System.InvalidCastException", [obj, klass]), ("ThrowArrayTypeMismatch", "System.ArrayTypeMismatchException", []),
            ("ThrowOutOfMemory", "System.OutOfMemoryException", []) })
            yield return Op(name, inputs, RuntimeValueKind.Void, RuntimeWidth.None, RuntimeHeapEffect.MayWrite, RuntimeObservation.Observable,
                "", "Throw", "抛出 " + type + "；条件由前驱路径提供", codegen + ".h/.cpp: raise_* / RaiseInvalidCastException / ArrayElementTypeCheck", [type], noReturn: true) with { FixedThrownException = type };
        yield return Op("ThrowManaged", [P("exception", RuntimeValueKind.ManagedReference), method], RuntimeValueKind.Void, RuntimeWidth.None, RuntimeHeapEffect.MayWrite,
            RuntimeObservation.Observable, "", "Throw", "写成 throw，记录新的抛出位置", codegen + ".cpp: il2cpp_codegen_raise_exception 清空 trace_ips 与 stack_trace", ["InputException"], pointers: [new("exception", RuntimeAccess.ReadWrite, RuntimeMemoryDomain.ManagedHeap, new(RuntimeExtentKind.Unknown, "异常的 trace_ips 与 stack_trace"), new(RuntimeConditionKind.Other, "抛出前"))], noReturn: true, exceptional: [Fact("ThrownInput", "抛出 exception，清空旧 trace_ips 与 stack_trace；记录新的抛出位置", "异常退出")]);
        yield return Op("Rethrow", [P("exception", RuntimeValueKind.ManagedReference)], RuntimeValueKind.Void, RuntimeWidth.None, RuntimeHeapEffect.MayWrite,
            RuntimeObservation.Observable, "", "Rethrow", "写成 rethrow，保留原异常身份", codegen + ".cpp: il2cpp_codegen_rethrow_exception", ["InputException"], noReturn: true, preconditions: "处于对应异常的 catch 区域", exceptional: [Fact("RethrownInput", "重新抛出同一 exception，保留原始抛出身份", "异常退出")]);
        yield return Op("LookupVirtualMethod", [obj, V("slot", RuntimeValueKind.Integer)], RuntimeValueKind.Method, RuntimeWidth.Pointer, RuntimeHeapEffect.None,
            RuntimeObservation.Observable, "结果是 object 类的 slot 虚表项的方法信息", "VirtualDispatch", "供 callvirt 的目标查询使用", codegen + ".h: GetVirtualMethodInfo", ["System.NullReferenceException"], trigger: RuntimeEventTrigger.ExceptionalOnly);
        yield return Op("LookupInterfaceMethod", [obj, V("slot", RuntimeValueKind.Integer), V("interface", RuntimeValueKind.Class)], RuntimeValueKind.Method, RuntimeWidth.Pointer, RuntimeHeapEffect.ArbitraryManagedCode,
            RuntimeObservation.Observable, "结果是接收者实现 interface 的 slot 方法", "InterfaceDispatch", "供接口 callvirt 的目标查询使用", "codegen/il2cpp-codegen-il2cpp.h: GetInterfaceMethodInfo → vm/ClassInlines.h: GetInterfaceInvokeDataFromVTable → vm/ClassInlines.cpp: GetInterfaceInvokeDataFromVTableSlowPath → Class::IsGenericClassAssignableFromVariance / RCW::GetComInterfaceInvokeData / RaiseExceptionForNotFoundInterface；vm/RCW.cpp: GetComInterfaceInvokeData → QueryInterfaceNoAddRef 可进入外部 COM 实现", ["AnyManagedException"], upperBound: true, managedCode: "普通类型只有类型关系查询与基础库异常构造；RCW 分支可同步回调托管代码并改写已有对象", exceptionReason: "RCW 的外部 QueryInterface 实现及托管回调不受本运行时控制，异常取上界");
        yield return Op("LookupInterfaceData", [obj, V("interface", RuntimeValueKind.Class), V("slot", RuntimeValueKind.Integer)], RuntimeValueKind.InvokeData, RuntimeWidth.Pointer, RuntimeHeapEffect.ArbitraryManagedCode,
            RuntimeObservation.Observable, "结果指向匹配接口槽的 VirtualInvokeData", "InterfaceDispatch", "供接口分派目标与方法信息查询使用", "vm/ClassInlines.cpp: GetInterfaceInvokeDataFromVTableSlowPath(Il2CppObject*) → RCW::GetComInterfaceInvokeData → vm/RCW.h: QueryInterfaceNoAddRef → QueryInterface；外部实现可回调；失败经 RaiseExceptionForNotFoundInterface → Exception::GetMethodAccessException", ["AnyManagedException"], upperBound: true, managedCode: "RCW 分支可执行未知外部实现与托管回调；不能按普通接口快路径概括", exceptionReason: "RCW 的外部 QueryInterface 实现及托管回调不受本运行时控制，异常取上界");
        yield return Op("ResolveGenericVirtual", [V("definition", RuntimeValueKind.Method), method], RuntimeValueKind.Method, RuntimeWidth.Pointer, RuntimeHeapEffect.MayWrite,
            RuntimeObservation.Observable, "返回 definition 在 method 的泛型实参下的实例", "GenericVirtualDispatch", "供泛型 callvirt 使用", "codegen/il2cpp-codegen-il2cpp.cpp: il2cpp_codegen_get_generic_virtual_method_internal → metadata/GenericMethod.cpp: GetGenericVirtualMethod → GetMethod / CreateMethodLocked → GenericClass::GetClass / GenericMetadata::InflateIfNeeded / Class::InitLocked；创建方法元数据，不调用生成的方法或未解析调用桩", ["System.TypeLoadException", "System.TypeInitializationException", "System.NotSupportedException"], upperBound: false, exceptionReason: "封闭的异常种类集合；泛型深度失败见 vm/GenericClass.cpp: CreateClass → vm/Exception.cpp: GetMaximumNestedGenericsException；未解析方法桩只被登记，不在此调用", managedCode: "无用户泛型方法执行；布局错误路径可能运行基础库异常构造");
        yield return Op("NotifyWriteBarrier", [new("location", RuntimeInputUse.Location, RuntimeValueKind.ManagedAddress), V("value", RuntimeValueKind.ManagedReference)], RuntimeValueKind.Void, RuntimeWidth.None, RuntimeHeapEffect.None,
            RuntimeObservation.Unobservable, "GC 已收到位置通知；本操作不执行托管赋值", "EraseWriteBarrier", "通知由托管写入承担", "codegen/il2cpp-codegen-common.cpp: Il2CppCodeGenWriteBarrier 仅调用 SetWriteBarrier");
        yield return Op("MemoryBarrier", [], RuntimeValueKind.Void, RuntimeWidth.None, RuntimeHeapEffect.None,
            RuntimeObservation.Unobservable, "只约束多线程内存次序，单线程下无可观察效果", "EraseMemoryBarrier", "删除屏障调用",
            "codegen/il2cpp-codegen-il2cpp.h: VolatileRead / VolatileWrite；codegen/il2cpp-codegen-il2cpp.cpp: il2cpp_codegen_memory_barrier → vm/Thread.cpp: Thread::FullMemoryBarrier → os/Atomic.h: Atomic::FullMemoryBarrier → Baselib_atomic_thread_fence_seq_cst",
            preconditions: "单线程语义；屏障不读取或写入托管堆", managedCode: "不执行托管代码");
        foreach (var (name, fill) in new[] { ("MemoryCopy", false), ("MemoryMove", false), ("MemoryFill", true) })
        {
            var extent = new RuntimeExtent(RuntimeExtentKind.InputLength, "length 个字节", "length");
            var condition = new RuntimeCondition(RuntimeConditionKind.Always, "调用时");
            var writes = new RuntimePointerEffect("destination", RuntimeAccess.Write, RuntimeMemoryDomain.ManagedHeap, extent, condition);
            yield return Op(name, [new("destination", RuntimeInputUse.Location, RuntimeValueKind.NativePointer),
                    fill ? V("value", RuntimeValueKind.Integer) : P("source", RuntimeValueKind.NativePointer), V("length", RuntimeValueKind.Integer)],
                RuntimeValueKind.NativePointer, RuntimeWidth.Pointer, RuntimeHeapEffect.None, RuntimeObservation.Unobservable,
                "目标区间被写入；返回 destination", name, "按已定位的缓冲区复制或填充下降",
                "ISO C11 N1570 7.24.2.1 memcpy / 7.24.2.2 memmove / 7.24.6.1 memset",
                pointers: fill ? [writes] : [new("source", RuntimeAccess.Read, RuntimeMemoryDomain.ManagedHeap, extent, condition), writes],
                returnInput: "destination", preconditions: "缓冲区与 length 合法；memcpy 源目标不得重叠；经指针效果须依实际地址区域重定位", managedCode: "无");
        }
        yield return Op("BeginCatch", [P("exception", RuntimeValueKind.NativePointer)], RuntimeValueKind.NativePointer, RuntimeWidth.Pointer,
            RuntimeHeapEffect.None, RuntimeObservation.Unobservable, "返回调整后的异常载荷指针；增加处理计数并维护活跃异常栈", "BeginCatch", "异常区域归一",
            "Itanium C++ ABI 2.5.3 __cxa_begin_catch", preconditions: "有效 catch landing pad；异常头符合 Itanium ABI", pointers: [new("exception", RuntimeAccess.ReadWrite, RuntimeMemoryDomain.RuntimePrivate, new(RuntimeExtentKind.Unknown, "C++ 异常头"), new(RuntimeConditionKind.Always, "调用时"))], managedCode: "无");
        yield return Op("CxxGetExceptionPointer", [P("exception", RuntimeValueKind.NativePointer)], RuntimeValueKind.NativePointer, RuntimeWidth.Pointer,
            RuntimeHeapEffect.None, RuntimeObservation.Unobservable, "返回当前异常的载荷指针", "ExceptionPayload", "异常值命名",
            "Itanium C++ ABI 2.5.3 __cxa_get_exception_ptr", managedCode: "无");
        yield return Op("CxxAllocateException", [V("size", RuntimeValueKind.Integer)], RuntimeValueKind.NativePointer, RuntimeWidth.Pointer,
            RuntimeHeapEffect.None, RuntimeObservation.Unobservable, "分配原生异常载荷", "ExceptionStorage", "只在包装对象已证明时折叠",
            "Itanium C++ ABI 2.4.2 __cxa_allocate_exception", managedCode: "无");
        yield return Op("CxxFreeException", [P("exception", RuntimeValueKind.NativePointer)], RuntimeValueKind.Void, RuntimeWidth.None,
            RuntimeHeapEffect.None, RuntimeObservation.Unobservable, "释放尚未抛出的原生异常载荷", "ExceptionStorage", "只在包装对象已证明时折叠",
            "Itanium C++ ABI 2.4.3 __cxa_free_exception", managedCode: "无");
        yield return Op("CxxThrow", [P("exception", RuntimeValueKind.NativePointer), V("type", RuntimeValueKind.NativePointer), V("destructor", RuntimeValueKind.NativePointer)], RuntimeValueKind.Void, RuntimeWidth.None,
            RuntimeHeapEffect.ArbitraryManagedCode, RuntimeObservation.Observable, "抛出原生异常载荷", "NativeThrow", "先证明托管包装对象再下降",
            "Itanium C++ ABI 2.4.3 __cxa_throw", ["NativeException"], noReturn: true);
        yield return Op("CxxRethrow", [], RuntimeValueKind.Void, RuntimeWidth.None,
            RuntimeHeapEffect.None, RuntimeObservation.Observable, "继续传播当前捕获的原生异常", "Rethrow", "只在对应托管 catch 内下降",
            "Itanium C++ ABI 2.5.4 __cxa_rethrow", ["ActiveException"], noReturn: true);
        yield return Op("EndCatch", [], RuntimeValueKind.Void, RuntimeWidth.None, RuntimeHeapEffect.ArbitraryManagedCode,
            RuntimeObservation.Observable, "减少处理计数，必要时销毁异常", "EndCatch", "异常区域归一",
            "Itanium C++ ABI 2.5.3 __cxa_end_catch；异常析构回调不受本目录约束", preconditions: "与活跃捕获匹配；异常析构函数遵守不抛出约定", managedCode: "异常析构函数可能回调托管代码");
        yield return Op("ExitProcess", [V("status", RuntimeValueKind.Integer)], RuntimeValueKind.Void, RuntimeWidth.None, RuntimeHeapEffect.ArbitraryManagedCode,
            RuntimeObservation.Observable, "", "Exit", "进程正常终止并执行退出处理器", "ISO C11 N1570 7.22.4.4 exit；atexit 处理器可执行用户代码",
            noReturn: true, termination: RuntimeTermination.ProcessTermination, preconditions: "遵守 ISO C exit 契约", managedCode: "退出处理器可能回调托管代码");
        yield return Op("AbortProcess", [], RuntimeValueKind.Void, RuntimeWidth.None, RuntimeHeapEffect.ArbitraryManagedCode,
            RuntimeObservation.Observable, "", "Abort", "进程异常终止", "ISO C11 N1570 7.22.4.1 abort；SIGABRT 处理器可执行用户代码",
            noReturn: true, termination: RuntimeTermination.ProcessTermination, preconditions: "遵守 ISO C abort 契约", managedCode: "信号处理器可能回调");
        yield return Op("StackProtectionFailure", [], RuntimeValueKind.Void, RuntimeWidth.None, RuntimeHeapEffect.None,
            RuntimeObservation.Unobservable, "", "StackProtectionFailure", "失败形成进程终止结局；仅证明失败分支不可达时才能消去", "LSB 5.0 __stack_chk_fail；Android bionic libc/bionic/__stack_chk_fail.cpp → async_safe_fatal", noReturn: true, preconditions: "失败路径终止进程，不可当作普通正常返回删除", termination: RuntimeTermination.ProcessTermination);
        yield return Op("ResumeUnwind", [V("exception", RuntimeValueKind.NativePointer)], RuntimeValueKind.Void, RuntimeWidth.None, RuntimeHeapEffect.ArbitraryManagedCode,
            RuntimeObservation.Observable, "", "ResumeUnwind", "由异常归一连接到继续展开结局", "Itanium C++ ABI 1.3 _Unwind_Resume；继续执行清理 landing pad", ["ActiveException"], noReturn: true, termination: RuntimeTermination.ResumeUnwind, exceptional: [Fact("UnwindContinued", "继续传播当前异常；不建立新的抛出事件身份", "异常展开")], preconditions: "处于有效的异常清理 landing pad", managedCode: "继续执行清理代码，可能进入托管 finally");
        yield return Op("TerminateUnwind", [], RuntimeValueKind.Void, RuntimeWidth.None, RuntimeHeapEffect.ArbitraryManagedCode,
            RuntimeObservation.Observable, "", "Terminate", "异常展开终止；不能降成普通 return", "ISO C++ [except.terminate] std::terminate；用户 terminate_handler 可回调", noReturn: true, termination: RuntimeTermination.ProcessTermination, preconditions: "C++ terminate_handler 遵守不返回约定", managedCode: "用户 terminate_handler 可回调托管代码");
    }
}
