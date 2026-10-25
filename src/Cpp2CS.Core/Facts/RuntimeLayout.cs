namespace Cpp2CS.Facts;

/// <summary>
/// Unity 2022.3.62f2 libil2cpp 运行时结构的字段偏移（LP64）。
/// 来源：nneonneo/Il2CppVersions headers/2022.3.62f2.h，用 gcc offsetof 计算；与 Il2CppDumper 生成的 il2cpp.h 不同
/// （后者缺 stack_slot_size，instance_size 之后的字段整体偏 4 字节）。代码中的使用情况另由普查核验（见 <see cref="LayoutChecks"/>）。
/// </summary>
public static class RuntimeLayout
{
    public const string UnityVersion = "2022.3.62f2";

    // Il2CppObject / Il2CppArray / Il2CppString
    public const int ObjectKlass = 0x00, ObjectMonitor = 0x08, ObjectHeaderSize = 0x10;
    public const int ArrayBounds = 0x10, ArrayMaxLength = 0x18, ArrayData = 0x20;
    public const int StringLength = 0x10, StringChars = 0x14;

    // Il2CppClass
    public const int ClassImage = 0x00, ClassByvalArg = 0x20, ClassElementClass = 0x40, ClassCastClass = 0x48, ClassDeclaringType = 0x50,
        ClassParent = 0x58, ClassGenericClass = 0x60, ClassTypeMetadataHandle = 0x68, ClassKlass = 0x78, ClassFields = 0x80, ClassMethods = 0x98,
        ClassNestedTypes = 0xA0, ClassImplementedInterfaces = 0xA8, ClassInterfaceOffsets = 0xB0, ClassStaticFields = 0xB8, ClassRgctxData = 0xC0,
        ClassTypeHierarchy = 0xC8, ClassUnityUserData = 0xD0, ClassInitializationExceptionGCHandle = 0xD8, ClassCctorStarted = 0xDC,
        ClassCctorFinishedOrNoCctor = 0xE0, ClassCctorThread = 0xE8, ClassGenericContainerHandle = 0xF0, ClassInstanceSize = 0xF8,
        ClassStackSlotSize = 0xFC, ClassActualSize = 0x100, ClassElementSize = 0x104, ClassNativeSize = 0x108, ClassStaticFieldsSize = 0x10C,
        ClassThreadStaticFieldsSize = 0x110, ClassThreadStaticFieldsOffset = 0x114, ClassFlags = 0x118, ClassToken = 0x11C, ClassMethodCount = 0x120,
        ClassVtableCount = 0x12A, ClassInterfacesCount = 0x12C, ClassInterfaceOffsetsCount = 0x12E, ClassTypeHierarchyDepth = 0x130,
        ClassGenericRecursionDepth = 0x131, ClassRank = 0x132, ClassMinimumAlignment = 0x133, ClassPackingSize = 0x134,
        /// <summary>位域首字节：bit0 initialized_and_no_error，bit1 initialized，bit2 enumtype，bit3 nullabletype，bit4 is_generic，bit5 has_references，bit6 init_pending，bit7 size_init_pending。</summary>
        ClassBitflags1 = 0x135,
        /// <summary>位域次字节：bit0 size_inited，bit1 has_finalize，bit2 has_cctor，bit3 is_blittable，bit4 is_import_or_windows_runtime，bit5 is_vtable_initialized，bit6 is_byref_like。</summary>
        ClassBitflags2 = 0x136,
        ClassVtable = 0x138;
    /// <summary>VirtualInvokeData { methodPtr; method }。</summary>
    public const int VirtualInvokeDataSize = 0x10;
    /// <summary>Il2CppRuntimeInterfaceOffsetPair { interfaceType; offset }。</summary>
    public const int InterfaceOffsetPairSize = 0x10;

    // MethodInfo
    public const int MethodPointer = 0x00, MethodVirtualPointer = 0x08, MethodInvoker = 0x10, MethodName = 0x18, MethodKlass = 0x20,
        MethodReturnType = 0x28, MethodParameters = 0x30, MethodRgctxData = 0x38, MethodGenericMethod = 0x40, MethodToken = 0x48,
        MethodFlags = 0x4C, MethodIflags = 0x4E, MethodSlot = 0x50, MethodParametersCount = 0x52, MethodBitflags = 0x53, MethodInfoSize = 0x58;

    // FieldInfo { name; type; parent; offset; token }
    public const int FieldName = 0x00, FieldType = 0x08, FieldParent = 0x10, FieldOffset = 0x18, FieldToken = 0x1C;

    // Il2CppDelegate
    public const int DelegateMethodPtr = 0x10, DelegateInvokeImpl = 0x18, DelegateTarget = 0x20, DelegateMethod = 0x28;

    /// <summary>vtable 槽位 slot 的方法指针在 Il2CppClass 中的偏移。</summary>
    public static int VtableMethodPointer(int slot) => ClassVtable + slot * VirtualInvokeDataSize;
    /// <summary>vtable 槽位 slot 的 MethodInfo* 在 Il2CppClass 中的偏移。</summary>
    public static int VtableMethodInfo(int slot) => ClassVtable + slot * VirtualInvokeDataSize + 8;
}
