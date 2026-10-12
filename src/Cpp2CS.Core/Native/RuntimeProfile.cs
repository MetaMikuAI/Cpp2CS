namespace Cpp2CS.Native;

public sealed record RuntimeHelper(string Kind, bool NoReturn, string Evidence);
public sealed record RuntimeFieldLayout(string Record, string Field, int Offset, int Size, string Evidence);
public sealed class RuntimeProfile
{
    public Dictionary<ulong, RuntimeHelper> Helpers { get; } = [];
    public List<RuntimeFieldLayout> Fields { get; } = [];
    public ulong? ManagedExceptionRtti { get; }
    public RuntimeProfile(ElfImage image)
    {
        if (image.Sha256 != "6ce1de5c0357e122f153f62d648de1655b7f8a339b2ae1c575595868a361e4bb") return;
        ManagedExceptionRtti = 0xb09f5e8; // 0x4a04f38..0x4a04f48：托管异常载荷使用的 __cxa_throw 类型。
        Fields.Add(new("MethodInfo", "klass", 0x20, 8,
            "Dumper MethodInfo prefix: methodPointer, virtualMethodPointer, invoker_method, name, klass; five ARM64 pointers. Generic runtime sites load declaring class at +0x20."));
        Fields.Add(new("Il2CppClass", "interface_offsets_count", 0x12e, 2,
            "0x499e694 global interface resolver: ldrh at 0x499e6ac and 0x499e6e0; bounds table walk. Dumper header reports 0x12a; native runtime takes precedence."));
        // 全程序集运行时入口。只有完整二进制哈希匹配才启用。
        Helpers[0x49c85a8] = new("InitializeMetadata", false, "wrapper -> 0x49d61ec -> encoded-token resolver 0x4a0fb90; DMB after resolution");
        Helpers[0x49c883c] = new("ThrowNullReference", true, "0x4a04f98 -> 0x4a04fac -> exception factory 0x4a04fbc; System.NullReferenceException name; throw 0x4a04f00");
        Helpers[0x49c870c] = new("RaiseException", true, "clears exception trace at x0+0x38; 0x4a04f00 stores exception x0 in C++ payload -> 0xb0992d0 (__cxa_throw); no normal return");
        Helpers[0x49c8844] = new("ThrowIndexOutOfRange", true, "0x4a04fe4 -> factory 0x4a04ff4 (System at 0x1edfa0d, IndexOutOfRangeException at 0x1f09b62) -> 0x4a04f00 -> __cxa_throw");
        Helpers[0x49c8860] = new("CreateArrayTypeMismatchException", false, "tail branch 0x4a061b8 -> exception factory 0x4a05930; System at 0x1edfa0d, ArrayTypeMismatchException at 0x1eeedd4; returns exception object");
        Helpers[0x49c8720] = new("IsInstance", false, "branch 0x49f798c; null guard; 0x49d1c3c assignability; returns original object or null; COM fallback retained");
        Helpers[0x49c8724] = new("Box", false, "branch 0x49f76b8; class value-type flag; allocator 0x49f7a88; copies payload from x1 to object+0x10; nullable path retained");
        Helpers[0x49c8830] = new("Allocate", false, "branch 0x49f7770; object allocator shared with il2cpp_object_new; class initialization retained");
        Helpers[0x49c8834] = new("RethrowException", true, "0x4a04f28 allocates an 8-byte C++ payload with __cxa_allocate_exception, stores original x0, then calls __cxa_throw at 0x4a04f48; unlike RaiseException it does not clear managed trace");
        Helpers[0x49c868c] = new("AllocateArray", false, "zero extends w1; branch 0x49f7080; initializes array class x0, checks length, allocates element_size*length+0x20, writes class/bounds/length; throws on failure");
        Helpers[0x49c8554] = new("WriteBarrier", false, "0x49c9760 -> 0x4a3e794; x0 slot selects atomic GC dirty-page bitmap; does not store a reference and does not consume x1");
        Helpers[0x49c8bd8] = new("ThrowInvalidCast", true, "object class name -> 0x4a05b14 InvalidCastException factory -> 0x49c870c -> terminal throw 0x4aad07c");
        Helpers[0xb0992d0] = new("CxxThrow", true, "PLT adrp/ldr/br -> GOT 0xb809f28; .rela.plt imports __cxa_throw; no normal return");
        Helpers[0x44102bc] = new("CxxCatchTerminate", true, "bl 0xb0992a0 (__cxa_begin_catch); bl 0xb0992e0 -> GOT 0xb809f30 (_ZSt9terminatev); no epilogue");
        Helpers[0x499e914] = new("ResolveInterface", false, "object.klass -> 0x499e694 class/interface/slot lookup; COM fallback 0x4a081d4; returns VirtualInvokeData pointer or throws");
        Helpers[0x49c871c] = new("InitializeClass", false, "tail branch 0x49c4710 class initialization");
        Helpers[0x499e620] = new("EnsureClassMetadata", false, "0x499e624 preserves input class in x19; 0x49d11f0 initializes metadata; checks error at +0xd8, returns original class at 0x499e634 or throws via 0x4a04f00");
        Helpers[0x49c85bc] = new("ResolveMetadata", false, "tail branch 0x49d61ec encoded-token resolver; returns slot content");
        Helpers[0x49c8c68] = new("IsAssignable", false, "tail branch 0x49d1c3c class assignability, shared by IsInstance");
        Helpers[0xb0992a0] = new("CxxBeginCatch", false, "PLT GOT 0xb809f10 __cxa_begin_catch");
        Helpers[0xb0992b0] = new("CxxEndCatch", false, "PLT GOT 0xb809f18 __cxa_end_catch");
        Helpers[0xb0992c0] = new("CxxAllocateException", false, "PLT GOT 0xb809f20 __cxa_allocate_exception");
        Helpers[0x4aad07c] = new("UnwindResume", true, "libunwind phase-2 dispatch; diagnostics at 0x1f0e104 '_Unwind_Resume' and 0x1f09d80 '_Unwind_Resume() can\u0027t return'; abort if dispatch returns");
    }
    public bool NoReturn(ulong address) => Helpers.TryGetValue(address, out var helper) && helper.NoReturn;
}
