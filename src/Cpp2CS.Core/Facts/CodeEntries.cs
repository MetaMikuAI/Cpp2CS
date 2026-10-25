using Cpp2CS.Model;

namespace Cpp2CS.Facts;

/// <summary>注册表中出现的代码入口种类。</summary>
public enum EntryKind
{
    /// <summary>非泛型方法实现（CodeGenModule.methodPointers）。</summary>
    Method,
    /// <summary>泛型方法实例或泛型类型上的方法实例（genericMethodPointers，经 genericMethodTable 对应 MethodSpec）。</summary>
    GenericMethod,
    /// <summary>值类型实例方法的 this 调整桩（CodeGenModule.adjustorThunks）：装箱对象指针 + 0x10 后转到方法本体。</summary>
    AdjustorThunk,
    /// <summary>泛型值类型方法实例的 this 调整桩（genericAdjustorThunks）。</summary>
    GenericAdjustorThunk,
    /// <summary>反射/委托调用用的调用器（invokerPointers）。</summary>
    Invoker,
    /// <summary>原生到托管的反向 P/Invoke 包装（reversePInvokeWrappers）。</summary>
    ReversePInvoke,
    /// <summary>未生成具体实例时的间接调用桩（unresolvedVirtual/Instance/StaticCallPointers）。</summary>
    UnresolvedVirtualCall, UnresolvedInstanceCall, UnresolvedStaticCall,
    /// <summary>每个程序集的模块初始化函数。</summary>
    ModuleInitializer,
    /// <summary>互操作数据中的函数指针（Il2CppInteropData）。</summary>
    DelegatePInvokeWrapper, MarshalToNative, MarshalFromNative, MarshalCleanup, CreateCcw,
}

/// <summary>
/// 一个代码入口。Method：Method/GenericMethod/AdjustorThunk/GenericAdjustorThunk/ReversePInvoke 的托管方法；
/// Index：所在表中的序号；Detail：模块名、互操作类型等补充信息。
/// </summary>
public sealed record CodeEntry(ulong Address, EntryKind Kind, MethodRef? Method, int Index, string? Detail)
{
    public override string ToString() => $"0x{Address:x} {Kind} {(Method?.ToString() ?? Detail ?? Index.ToString())}";
}

/// <summary>RGCTX 条目种类，与 Il2CppRGCTXDataType 一致。</summary>
public enum RgctxKind { Invalid, Type, Class, Method, Array, Constrained }

/// <summary>一条运行时泛型上下文定义。Value：TypeRef（Type/Class/Array）、MethodRef（Method）或 (TypeRef, MethodRef)（Constrained）。</summary>
public sealed record RgctxEntry(RgctxKind Kind, object? Value)
{
    public override string ToString() => $"{Kind}({Value})";
}

/// <summary>注册表给出的全部代码入口、RGCTX 定义与元数据槽位表。</summary>
public sealed class Registrations
{
    public required ulong CodeRegistration { get; init; }
    public required ulong MetadataRegistration { get; init; }
    public required IReadOnlyList<CodeEntry> Entries { get; init; }
    /// <summary>按地址分组；同一地址的多个入口即 ICF/共享代码的全部所有者。</summary>
    public required IReadOnlyDictionary<ulong, CodeEntry[]> ByAddress { get; init; }
    /// <summary>RGCTX：键为 (程序集映像名, 令牌)，令牌为方法（0x06）或类型（0x02）。</summary>
    public required IReadOnlyDictionary<(string Image, uint Token), RgctxEntry[]> Rgctx { get; init; }
    /// <summary>metadataRegistration.metadataUsages 列出的槽位地址；v27+ 可能为空。</summary>
    public required IReadOnlyList<ulong> MetadataUsageSlots { get; init; }
    /// <summary>metadataRegistration.types 中每个 Il2CppType 的地址 → 运行时类型序号。</summary>
    public required IReadOnlyDictionary<ulong, int> TypePointers { get; init; }
    /// <summary>每个非泛型方法的调用器序号（invokerIndices），-1 表示没有。</summary>
    public required IReadOnlyDictionary<MethodDef, int> InvokerOf { get; init; }

    public CodeEntry[] At(ulong address) => ByAddress.TryGetValue(address, out var list) ? list : [];
}
