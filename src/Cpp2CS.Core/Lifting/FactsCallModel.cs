using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Ssa;

namespace Cpp2CS.Lifting;

/// <summary>一个调用目标读取与写出的寄存器，以及依据。</summary>
public sealed record CallSignature(Storage[] Reads, Storage[] Results, string Source)
{
    /// <summary>托管签名中 MethodInfo* 参数的寄存器（IL2CPP 常不设置它，或原样转传调用方收到的值）。</summary>
    public Storage? MethodInfo { get; init; }
}

/// <summary>
/// 按事实层确定调用读写的寄存器：
/// 托管方法入口按元数据签名（<see cref="ManagedAbi"/>）；调用器按 InvokerMethod 原型；
/// 运行时 helper 按 libil2cpp 2022.3 codegen 接口的原型（见 <see cref="Helper"/>）；
/// 其余（间接调用、未识别目标、无法分类的签名）退回保守约定。
/// 实例按目标缓存，不是线程安全的。
/// </summary>
public sealed class FactsCallModel : ICallModel
{
    private readonly ProgramFacts facts;
    private readonly ManagedAbi abi;
    private readonly ConservativeCallModel conservative;
    private readonly CallingConvention convention;
    private readonly Dictionary<ulong, CallSignature?> cache = new();

    public FactsCallModel(ProgramFacts facts, CallingConvention convention)
    {
        this.facts = facts;
        this.convention = convention;
        abi = new ManagedAbi(facts.Layouts);
        conservative = new ConservativeCallModel(convention);
    }

    private static Storage X(int i) => Storage.Gpr(i);

    /// <summary>
    /// helper 原型（libil2cpp 2022.3 codegen/il2cpp-codegen.h 与 vm 导出）：
    /// InitMetadata(uintptr_t* slot) → 槽位的值；InitializedTypeInfo(klass) → klass；il2cpp_runtime_class_init(klass)；
    /// NullCheck(obj)（未内联的判空）；il2cpp_object_new(klass) → obj；il2cpp_array_new_specific(klass, length) → array；il2cpp_value_box(klass, data) → obj；
    /// IsInst(obj, klass) → obj；il2cpp_class_is_assignable_from(klass, oklass) → bool；il2cpp_gc_wbarrier_set_field 的写屏障(ptr, value)；
    /// 接口慢路径(obj, klass, slot) → VirtualInvokeData*；il2cpp_raise_exception(ex, lastManagedFrame)；Rethrow(ex)；
    /// InitMethodRgctx(method) → method；dmb 屏障无参数。其余 helper 退回保守约定。
    /// </summary>
    private static CallSignature? Helper(RuntimeHelper helper) => helper.Kind switch
    {
        // vm::MetadataCache::InitializeRuntimeMetadata(uintptr_t*) 返回槽位初始化之后的值；两个包装都保留 x0（一个加 dmb 后返回，一个直接尾调用）
        HelperKind.InitMetadata => new([X(0)], [X(0)], "helper"),
        HelperKind.InitializedTypeInfo or HelperKind.ObjectNew or HelperKind.InitMethodRgctx => new([X(0)], [X(0)], "helper"),
        HelperKind.ClassInit or HelperKind.NullCheck => new([X(0)], [], "helper"),
        HelperKind.NewArray or HelperKind.Box or HelperKind.IsInst or HelperKind.IsAssignableFrom => new([X(0), X(1)], [X(0)], "helper"),
        HelperKind.WriteBarrier => new([X(0), X(1)], [], "helper"),
        HelperKind.InterfaceLookup => new([X(0), X(1), X(2)], [X(0)], "helper"),
        HelperKind.Raise => new([X(0), X(1)], [], "helper"),
        HelperKind.Rethrow => new([X(0)], [], "helper"),
        HelperKind.Throw => new([], [], "helper"),
        HelperKind.GetException => new([], [X(0)], "helper"),
        HelperKind.MemoryBarrier => new([], [], "helper"),
        HelperKind.CompareExchangeReference => new([X(0), X(1), X(2)], [X(0)], "helper"),
        HelperKind.Import => helper.Detail switch
        {
            "memcpy" or "memmove" or "memset" => new([X(0), X(1), X(2)], [X(0)], "libc"),
            "modf" => new([X(0), Storage.Vec(0)], [Storage.Vec(0)], "libm"),
            "sinf" => new([Storage.Vec(0)], [Storage.Vec(0)], "libm"),
            "fmodf" => new([Storage.Vec(0), Storage.Vec(1)], [Storage.Vec(0)], "libm"),
            "__cxa_begin_catch" => new([X(0)], [X(0)], "libc++abi"),
            "__cxa_end_catch" => new([], [], "libc++abi"),
            _ => null,
        },
        _ => null,
    };

    /// <summary>目标的签名；没有可靠依据时为 null（调用方使用保守约定）。</summary>
    public CallSignature? Signature(ulong target)
    {
        if (cache.TryGetValue(target, out var cached)) return cached;
        CallSignature? signature = null;
        if (facts.Unregistered.At(target) is { } identity)
            signature = new(identity.Abi.Reads, identity.Abi.Results, "inferred-definition") { MethodInfo = identity.Abi.MethodInfo?.Register };
        else if (facts.Helpers.At(target) is { } helper) signature = Helper(helper);
        else
        {
            foreach (var entry in facts.EntriesAt(target))
            {
                if (entry.Kind == EntryKind.Invoker)
                {
                    // void (*InvokerMethod)(Il2CppMethodPointer, const MethodInfo*, void* obj, void** args, void* returnValue)
                    signature = new([X(0), X(1), X(2), X(3), X(4)], [], "invoker");
                    break;
                }
                if (entry is { Method: { } method, Kind: EntryKind.Method or EntryKind.GenericMethod or EntryKind.AdjustorThunk or EntryKind.GenericAdjustorThunk }
                    && abi.Classify(method, out _) is { } classified)
                {
                    signature = new(classified.Reads, classified.Results, "metadata") { MethodInfo = classified.MethodInfo?.Register };
                    break;
                }
            }
        }
        cache[target] = signature;
        return signature;
    }

    private CallSignature? Of(Call call) =>
        call is { Kind: CallKind.Direct or CallKind.Tail, Target: Const target } ? Signature(target.Value) : null;

    public IReadOnlyList<Storage> Reads(Call call) => Of(call)?.Reads ?? conservative.Reads(call);

    public IReadOnlyList<Storage> Results(Call call) =>
        call.Kind is CallKind.Tail or CallKind.TailIndirect ? [] : Of(call)?.Results ?? conservative.Results(call);

    public IReadOnlyList<Storage> Clobbers(Call call) => convention.Clobbered;
}
