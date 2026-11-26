using System.Collections.Immutable;

namespace Cpp2CS.Spec.Catalog;

/// <summary>求值栈上一个值的类别（ECMA-335 III.1.1）。浮点按 il2cpp 的做法区分 32 位与 64 位。</summary>
public enum StackKind : byte { Int32, Int64, NativeInt, Float32, Float64, Object, ByRef, Value }

/// <summary>目录项对一个操作数的要求。</summary>
public enum StackClass : byte
{
    Int32, Int64, NativeInt,
    /// <summary>Int32、Int64 或 NativeInt。</summary>
    Integer,
    Float32, Float64,
    /// <summary>Float32 或 Float64。</summary>
    Float,
    Object, ByRef,
    /// <summary>值类型的值。</summary>
    Value,
    /// <summary>整数、对象引用或地址：可以与零比较、可以按无符号数比较的值。</summary>
    Scalar,
    /// <summary>
    /// 能存入指令涉及的类型（局部变量、形参、字段、返回值的类型）的值，按 ECMA-335 III.1.6 表 III.9：
    /// 不超过 32 位的整数接受 int32 与本机整数；64 位整数只接受 int64；本机整数接受 int32 与本机整数；
    /// 浮点接受浮点；类接受对象引用；值类型接受同样大小的值类型；托管指针接受托管指针与本机整数。
    /// </summary>
    Assignable,
    Any,
}

/// <summary>目录项在操作数类别之外的适用条件，由指令的元数据操作数决定。</summary>
public enum VariantCondition : byte
{
    None,
    /// <summary>静态字段，所属类没有静态构造函数。</summary>
    StaticWithoutInitializer,
    /// <summary>静态字段，所属类有静态构造函数。</summary>
    StaticWithInitializer,
    /// <summary>实例字段。经对象、值或地址访问静态字段时，对象被忽略，也不抛出 NullReference（ECMA-335 III.4.10、III.4.28）。</summary>
    InstanceField,
    /// <summary>没有 this 的方法。</summary>
    StaticMethod,
    /// <summary>目标唯一的实例方法：非虚方法，或者密封类、值类型上的方法，或者 final 的虚方法。</summary>
    UniqueTarget,
    /// <summary>类上的虚方法，目标不唯一。</summary>
    ClassVirtual,
    /// <summary>接口方法。</summary>
    InterfaceMethod,
    /// <summary>返回类型为 void。</summary>
    ReturnsVoid,
    /// <summary>返回类型不是 void。</summary>
    ReturnsValue,
    /// <summary>没有 this 的方法，所属的类有静态构造函数：调用点先确保该类已初始化（ECMA-335 I.8.9.5）。</summary>
    StaticMethodWithInitializer,
    /// <summary>构造函数，所属的类型是引用类型（this 是对象引用）。</summary>
    ReferenceTypeConstructor,
}

/// <summary>模板抛出的异常。</summary>
public enum ExceptionKind : byte { None, NullReference, IndexOutOfRange, DivideByZero, InvalidCast, ArrayTypeMismatch, Overflow }

/// <summary>模板里被读写的位置的种类。位置由种类、基（对象、数组与下标、地址）和字段决定。</summary>
public enum LocationKind : byte
{
    None,
    /// <summary>对象的实例字段：基是对象引用。</summary>
    InstanceField,
    /// <summary>经地址访问的字段：基是所属值的地址。</summary>
    FieldAtAddress,
    /// <summary>静态字段：没有基。</summary>
    StaticField,
    /// <summary>一维零基数组的元素：基是数组引用与下标。</summary>
    ArrayElement,
}

/// <summary>
/// 规格登记的具名函数。前一组是纯函数，在项里写成属性；后一组是运行时操作，在效果图里是一次运行时调用。
/// 每个函数注明出处；它在各目标上的原生写法由规格另行登记。
/// </summary>
public enum RuntimeFunction : byte
{
    None,
    /// <summary>数组的长度，32 位。出处：il2cpp-object-internals.h 的 Il2CppArray::max_length；IL2CPP_ARRAY_BOUNDS_CHECK 按 uint32 比较。</summary>
    ArrayLength,
    /// <summary>对象的类。出处：il2cpp-object-internals.h 的 Il2CppObject::klass。</summary>
    ClassOf,
    /// <summary>
    /// IsInst(对象, 类)：对象可以当作该类使用时是对象自己，否则为空。空对象得空。类由模板写出，或取自指令的类型操作数。
    /// 出处：il2cpp-codegen-il2cpp.h 的 IsInst、IsInstClass、IsInstSealed。
    /// </summary>
    IsInstance,
    /// <summary>
    /// 字段所在的地址：所属值的地址加字段在值里的偏移。所属值经地址给出，它的类型是值类型。出处：生成代码里的 &amp;p-&gt;field；
    /// 二进制里的字段偏移表按装箱之后的对象登记（offsetof(T, f) + sizeof(RuntimeObject)），在值里的偏移要减去对象头。
    /// </summary>
    FieldAddress,
    /// <summary>
    /// double 转 int32。范围内向零舍入；范围外与 NaN 的结果随目标而定：il2cpp-codegen-common.h 的
    /// il2cpp_codegen_cast_double_to_int 在 ARM 上把正无穷改成最小负数，其余交给 C++ 的转换。
    /// </summary>
    CastDoubleToInt32,
    /// <summary>虚表项：类的虚表里某个方法槽位上的调用数据。出处：il2cpp-codegen-il2cpp.h 的 il2cpp_codegen_get_virtual_invoke_data。</summary>
    VirtualInvokeData,
    /// <summary>
    /// 接口查找（运行时操作，强制内联）：参数是接收者对象，接口与槽号由效果所带的方法实体给出。
    /// 在对象的类的接口偏移表里找到接口，取虚表里对应槽位的调用数据；找不到时调用以对象、接口、槽号为参数的慢路径。
    /// 出处：il2cpp-codegen-il2cpp.h 的 il2cpp_codegen_get_interface_invoke_data，vm/ClassInlines.h 的 GetInterfaceInvokeDataFromVTable
    /// 与 GetInterfaceInvokeDataFromVTableSlowPath。
    /// </summary>
    InterfaceInvokeData,
    /// <summary>
    /// 数组的长度，按 il2cpp_array_size_t 读（指针位宽）：ldlen 的生成代码读 ((RuntimeArray*)a)-&gt;max_length。
    /// 与 ArrayLength 是同一个字段；长度不超过 IL2CPP_ARRAY_MAX_INDEX，ArrayLength 是它的低 32 位。出处：il2cpp-object-internals.h 的 Il2CppArray::max_length。
    /// </summary>
    ArrayLengthNative,
    /// <summary>数组类的元素类。出处：il2cpp-class-internals.h 的 Il2CppClass::element_class；il2cpp-codegen-il2cpp.h 的 ArrayElementTypeCheck 读 array-&gt;klass-&gt;element_class。</summary>
    ElementClass,
}

/// <summary>模板里的值的构造方式。</summary>
public enum ValueOp : byte
{
    // 来源
    /// <summary>第 A 个操作数，按入栈的次序从 0 编号。</summary>
    Operand,
    /// <summary>第 A 步的结果。</summary>
    Step,
    /// <summary>指令的立即数，位宽 A。</summary>
    Immediate,
    /// <summary>指令指定的形参、局部变量当前的值。</summary>
    Argument, Local,
    /// <summary>空引用。</summary>
    Null,
    /// <summary>指令的字面量操作数（ldstr 的字符串）：实体，位宽是指针位宽。</summary>
    Literal,
    /// <summary>未定义，位宽同第一个参数。</summary>
    Undefined,
    // 整数运算，两个操作数同宽
    Add, Sub, Mul, SignedDivide, SignedRemainder, And, Xor, Negate,
    /// <summary>移位。移位量按无符号数调整到与被移位的值同宽。</summary>
    ShiftLeft, ShiftRightSigned, ShiftRightUnsigned,
    // 谓词，结果 1 位
    Equal, SignedLess, UnsignedLess, IsZero, IsMinimum, IsAllOnes,
    /// <summary>移位量小于被移位的值的位宽。参数：移位量，被移位的值。</summary>
    ShiftInRange,
    Both, Not,
    /// <summary>1 位的谓词变成 int32 的 0 或 1。</summary>
    Flag,
    /// <summary>取低 A 位，再扩展到 B 位：C 为 1 按符号扩展，为 0 按零扩展。A 不小于 B 时只截断到 B 位。</summary>
    Resize,
    /// <summary>
    /// 从存储位宽扩到栈上的位宽；把栈上的值转成存储的表示。都按指令涉及的类型（字段、元素、形参、局部变量、返回值的类型）。
    /// 存储：不超过 32 位的整数截断；本机整数接受 int32 时按类型的符号扩展（ECMA-335 III.1.6）；
    /// 浮点按存储的格式转换（ECMA-335 I.12.1.3、III.3.63）；其余不变。
    /// </summary>
    FromStorage, ToStorage,
    /// <summary>值类型的值里的一个字段：按字段的偏移与位宽切片。</summary>
    FieldOfValue,
    // 浮点，两个操作数同宽
    FloatAdd, FloatSubtract, FloatMultiply, FloatDivide,
    /// <summary>浮点转 double；有符号、无符号整数转 double。</summary>
    FloatToDouble, SignedToDouble, UnsignedToDouble,
    /// <summary>具名纯函数。参数之后可以跟指令的字段、类型或方法操作数，由函数决定。</summary>
    Named,
    Select,
}

/// <summary>模板里的值。</summary>
public sealed record TemplateValue(ValueOp Op, ImmutableArray<TemplateValue> Arguments, int A = 0, int B = 0, int C = 0,
    RuntimeFunction Function = RuntimeFunction.None);

/// <summary>模板里一步的种类。前八种是效果；其后是数据的搬动与块末的去向，不是效果。</summary>
public enum StepKind : byte
{
    /// <summary>条件成立时抛出。</summary>
    ThrowIf,
    Read, Write,
    /// <summary>调用指令的方法操作数。Indirect 为真时，目标是一个值（调用数据），方法操作数只说明签名。</summary>
    Call,
    /// <summary>调用运行时操作。</summary>
    RuntimeCall,
    /// <summary>确保字段所属的类、被调方法所属的类已初始化。</summary>
    ClassInitialize,
    /// <summary>
    /// 新对象：分配构造函数所属的类的一个对象，结果是新引用。含该类的类初始化分量（时机是否精确取自元数据）。
    /// 它是事件；对象在首次被使用之前不可见（设计 6.1、7.5）。
    /// </summary>
    NewObject,
    /// <summary>抛出第 0 个值给出的异常对象，不返回；块在这一步结束。</summary>
    Throw,
    /// <summary>有定义条件：翻译只在条件成立时有定义（设计 9.1）。它不是效果；共同执行在这一步之后把条件并入路径条件。</summary>
    Require,
    /// <summary>写指令指定的局部变量、形参。</summary>
    StoreLocal, StoreArgument,
    /// <summary>条件成立时去指令的目标，否则去下一条指令。</summary>
    Branch,
    Jump,
    /// <summary>按选择子去跳转表里的目标；超出表的范围去下一条指令。</summary>
    Switch,
    Return,
}

/// <summary>模板里的一步。Values 的含义随种类而定：位置的基在前，被写的值、实参在后。</summary>
public sealed record TemplateStep(StepKind Kind, ImmutableArray<TemplateValue> Values, LocationKind Location = LocationKind.None,
    ExceptionKind Exception = ExceptionKind.None, RuntimeFunction Function = RuntimeFunction.None, bool Indirect = false);

/// <summary>结果压栈时的类别。</summary>
public enum ResultKind : byte
{
    None, Int32, Int64, NativeInt, Float32, Float64, Object, ByRef,
    /// <summary>与第 0 个操作数相同。</summary>
    SameAsOperand,
    /// <summary>指令涉及的类型在栈上的类别。</summary>
    Subject,
}

/// <summary>
/// 目录项上登记的实现偏差：有定义条件不成立的输入上，标准另有规定。ImplementationDefined 为真表示标准把行为留给实现
/// （不算偏差，单独计数）；为假表示标准规定了与翻译不同的行为。
/// </summary>
public sealed record Deviation(string Condition, string Standard, bool ImplementationDefined);

/// <summary>出处：il2cpp 对这条指令的翻译、运行时头文件里的位置、标准里的条目。</summary>
public sealed record Provenance(string Translation, string Runtime, string Standard);

/// <summary>
/// 操作目录的一项：一个托管操作。Id 是它的标识，声明只引用标识。
/// Il 是下降时写出的指令（各形式的规范助记符）；Operands 与 Condition 是适用条件；
/// Steps 是效果模板，直线序列；Result 是压栈的结果。
/// </summary>
public sealed record CatalogEntry(string Id, string Il, string Summary, ImmutableArray<StackClass> Operands, bool SameKind,
    VariantCondition Condition, ImmutableArray<TemplateStep> Steps, TemplateValue? Result, ResultKind ResultKind, Provenance Source)
{
    /// <summary>操作数取自方法签名（调用）而不是 Operands。</summary>
    public bool OperandsFromSignature { get; init; }
    /// <summary>助记符里写明的元素类型的存储位宽（ldelem.i4 的 32）；没有则为 0。</summary>
    public int ImpliedBits { get; init; }
    /// <summary>助记符写明元素是对象引用（ldelem.ref、stelem.ref）：存储位宽是指针位宽。</summary>
    public bool ImpliedReference { get; init; }
    /// <summary>方法操作数是构造函数：this 由模板里“新对象”一步的结果给出，栈上只有其余的实参；结果是新对象。</summary>
    public bool Constructs { get; init; }
    /// <summary>登记的实现偏差，与模板里的有定义条件对应。</summary>
    public ImmutableArray<Deviation> Deviations { get; init; } = [];
}
