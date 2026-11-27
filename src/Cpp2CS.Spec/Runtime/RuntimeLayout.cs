namespace Cpp2CS.Spec.Runtime;

/// <summary>运行时布局。数组长度的存储位宽、生成代码的比较位宽和运行时允许的最大值分别登记。</summary>
public sealed record RuntimeLayout(int PointerBits, int ObjectHeaderBytes, int ArrayLengthOffset, int ArrayLengthBits,
    long ArrayLengthMaximum, int ArrayDataOffset, int ClassStaticFieldsOffset, int ClassInitializedOffset, int ClassInitializedBits)
{
    public int ObjectClassOffset { get; init; }
    public int ObjectMonitorOffset { get; init; }
    public int ExceptionWrapperExOffset { get; init; }
    public int ExceptionWrapperExBits { get; init; }
    public int ArrayBoundsOffset { get; init; }
    public int ArrayLengthStorageBits { get; init; }
    public int ArrayBoundsBytes { get; init; }
    public int ArrayBoundLengthOffset { get; init; }
    public int ArrayLowerBoundOffset { get; init; }
    public int ClassElementOffset { get; init; }
    public int ClassCastOffset { get; init; }
    public int ClassInterfaceOffsetsOffset { get; init; }
    public int ClassInterfaceCountOffset { get; init; }
    public int ClassInterfaceCountBits { get; init; }
    public int ClassVTableOffset { get; init; }
    public int ClassTypeHierarchyOffset { get; init; }
    public int ClassTypeHierarchyDepthOffset { get; init; }
    public int ClassTypeHierarchyDepthBits { get; init; }
    public int ClassInitializedFlagsOffset { get; init; }
    public int ClassInitializedAndNoErrorBit { get; init; }
    public int MethodClassOffset { get; init; }
    public int MethodRgctxOffset { get; init; }
    public int ClassRgctxOffset { get; init; }
    public int ClassSizeFlagsOffset { get; init; }
    public int VirtualInvokeDataBytes { get; init; }
    public int VirtualMethodPointerOffset { get; init; }
    public int VirtualMethodInfoOffset { get; init; }
    public int InterfaceOffsetPairBytes { get; init; }
    public int InterfaceTypeOffset { get; init; }
    public int InterfaceSlotOffset { get; init; }
    public int InterfaceSlotBits { get; init; }
    public int DelegateMethodPointerOffset { get; init; }
    public int DelegateInvokeImplOffset { get; init; }
    public int DelegateTargetOffset { get; init; }
    public int DelegateMethodOffset { get; init; }
    public int DelegateInvokeImplThisOffset { get; init; }

    // 每行给出头文件依据与调试信息量法。数组起点常量由 offsetof(Il2CppArraySize, vector) 定义。
    // cctor_finished_or_no_cctor 只从零变为非零，非零表示初始化完成或没有静态构造。
    // 数组比较位宽由宏的强制转换决定；最大下标是源码宏，结构 DIE 不含这个上界。
    public static RuntimeLayout Unity2022Lp64 { get; } = new(
        PointerBits: 64,                  // il2cpp-object-internals.h | bits Il2CppObject.klass
        ObjectHeaderBytes: 16,            // il2cpp-object-internals.h | size Il2CppObject
        ArrayLengthOffset: 24,            // il2cpp-object-internals.h | offset Il2CppArray.max_length
        ArrayLengthBits: 32,              // codegen/il2cpp-codegen-il2cpp.h IL2CPP_ARRAY_BOUNDS_CHECK | castbits uint32_t
        ArrayLengthMaximum: 0x7fffffff,   // il2cpp-object-internals.h | macro IL2CPP_ARRAY_MAX_INDEX
        ArrayDataOffset: 32,              // il2cpp-object-internals.h Il2CppArraySize.vector | constant kIl2CppSizeOfArray
        ClassStaticFieldsOffset: 0xb8,    // il2cpp-class-internals.h | offset Il2CppClass.static_fields
        ClassInitializedOffset: 0xe0,     // il2cpp-class-internals.h | offset Il2CppClass.cctor_finished_or_no_cctor
        ClassInitializedBits: 32)         // il2cpp-class-internals.h | bits Il2CppClass.cctor_finished_or_no_cctor
    {
        ObjectClassOffset = 0,            // il2cpp-object-internals.h | offset Il2CppObject.klass
        ObjectMonitorOffset = 8,          // il2cpp-object-internals.h | offset Il2CppObject.monitor
        ExceptionWrapperExOffset = 0,     // il2cpp-object-internals.h | ptroffset Il2CppExceptionWrapper.ex
        ExceptionWrapperExBits = 64,      // il2cpp-object-internals.h | bits Il2CppExceptionWrapper.ex
        ArrayBoundsOffset = 16,           // il2cpp-object-internals.h | offset Il2CppArray.bounds
        ArrayLengthStorageBits = 64,      // il2cpp-object-internals.h | bits Il2CppArray.max_length
        ArrayBoundsBytes = 16,            // il2cpp-object-internals.h | size Il2CppArrayBounds
        ArrayBoundLengthOffset = 0,       // il2cpp-object-internals.h | offset Il2CppArrayBounds.length
        ArrayLowerBoundOffset = 8,        // il2cpp-object-internals.h | offset Il2CppArrayBounds.lower_bound
        ClassElementOffset = 0x40,        // il2cpp-class-internals.h | offset Il2CppClass.element_class
        ClassCastOffset = 0x48,           // il2cpp-class-internals.h | offset Il2CppClass.castClass
        ClassInterfaceOffsetsOffset = 0xb0, // il2cpp-class-internals.h | offset Il2CppClass.interfaceOffsets
        ClassInterfaceCountOffset = 0x12e, // il2cpp-class-internals.h | offset Il2CppClass.interface_offsets_count
        ClassInterfaceCountBits = 16,     // il2cpp-class-internals.h | bits Il2CppClass.interface_offsets_count
        ClassVTableOffset = 0x138,        // il2cpp-class-internals.h | offset Il2CppClass.vtable
        ClassTypeHierarchyOffset = 0xc8,  // il2cpp-class-internals.h | offset Il2CppClass.typeHierarchy
        ClassTypeHierarchyDepthOffset = 0x130, // il2cpp-class-internals.h | offset Il2CppClass.typeHierarchyDepth
        ClassTypeHierarchyDepthBits = 8,  // il2cpp-class-internals.h | bits Il2CppClass.typeHierarchyDepth
        ClassInitializedFlagsOffset = 0x135, // il2cpp-class-internals.h | bitbyte Il2CppClass.initialized_and_no_error,initialized,enumtype,nullabletype,is_generic,has_references,init_pending,size_init_pending
        ClassInitializedAndNoErrorBit = 0, // il2cpp-class-internals.h | bitindex Il2CppClass.initialized_and_no_error
        MethodClassOffset = 0x20,         // il2cpp-class-internals.h | ptroffset MethodInfo.klass
        MethodRgctxOffset = 0x38,         // il2cpp-class-internals.h | ptroffset MethodInfo.rgctx_data
        ClassRgctxOffset = 0xc0,          // il2cpp-class-internals.h | ptroffset Il2CppClass.rgctx_data
        ClassSizeFlagsOffset = 0x136,     // il2cpp-class-internals.h | bitbyte Il2CppClass.size_inited,has_finalize,has_cctor,is_blittable,is_import_or_windows_runtime,is_vtable_initialized,is_byref_like
        VirtualInvokeDataBytes = 16,      // il2cpp-class-internals.h | size VirtualInvokeData
        VirtualMethodPointerOffset = 0,    // il2cpp-class-internals.h | offset VirtualInvokeData.methodPtr
        VirtualMethodInfoOffset = 8,      // il2cpp-class-internals.h | offset VirtualInvokeData.method
        InterfaceOffsetPairBytes = 16,    // il2cpp-class-internals.h | size Il2CppRuntimeInterfaceOffsetPair
        InterfaceTypeOffset = 0,          // il2cpp-class-internals.h | offset Il2CppRuntimeInterfaceOffsetPair.interfaceType
        InterfaceSlotOffset = 8,          // il2cpp-class-internals.h | offset Il2CppRuntimeInterfaceOffsetPair.offset
        InterfaceSlotBits = 32,           // il2cpp-class-internals.h | bits Il2CppRuntimeInterfaceOffsetPair.offset
        DelegateMethodPointerOffset = 16, // il2cpp-object-internals.h | offset Il2CppDelegate.method_ptr
        DelegateInvokeImplOffset = 24,    // il2cpp-object-internals.h | offset Il2CppDelegate.invoke_impl
        DelegateTargetOffset = 32,        // il2cpp-object-internals.h | offset Il2CppDelegate.target
        DelegateMethodOffset = 40,        // il2cpp-object-internals.h | offset Il2CppDelegate.method
        DelegateInvokeImplThisOffset = 64, // il2cpp-object-internals.h | offset Il2CppDelegate.invoke_impl_this
    };
}
