using System.Collections.Immutable;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Runtime;

namespace Cpp2CS.Kernel.Engine;

/// <summary>一次对常量地址的调用被认成了什么。</summary>
public enum CalleeKind : byte
{
    /// <summary>没有命名：未命名的效果。</summary>
    Unknown,
    /// <summary>托管方法的入口（代码地图）。</summary>
    Managed,
    /// <summary>登记的运行时操作。</summary>
    Runtime,
}

/// <summary>调用目标的命名。Basis 是命名的依据（设计第 8 节），Name 只用于诊断。</summary>
public sealed record Callee(CalleeKind Kind, RuntimeOperation? Operation, string Name, string Basis)
{
    /// <summary>独占入口的托管方法及其签名。</summary>
    public Forward.MethodShape? Signature { get; init; }
    /// <summary>共享入口登记的全部方法签名。独占入口为 null，共享但签名不全时为空数组。</summary>
    public ImmutableArray<Forward.MethodShape>? SharedSignatures { get; init; }
}

/// <summary>
/// 事实层向等价引擎提供的全局事实：运行时命名、代码地图、布局。实现属于事实层；每个回答都是关于二进制的真命题，
/// 不能回答时返回空，引擎把相应的效果当作未命名或未定位。
/// </summary>
public interface INativeFacts
{
    /// <summary>运行时结构的布局。</summary>
    RuntimeLayout Layout { get; }
    /// <summary>对这个地址的调用是什么。</summary>
    Callee Callee(ulong address);
    /// <summary>托管方法的入口地址（代码地图）。</summary>
    ulong? Entry(EntityRef method);
    /// <summary>实例字段相对对象指针的字节偏移。</summary>
    int? InstanceFieldOffset(EntityRef field);
    /// <summary>静态字段相对所属类的静态区的字节偏移。</summary>
    int? StaticFieldOffset(EntityRef field);
    /// <summary>地址落在映像的数据区（不是任何托管位置）。</summary>
    bool InImageData(ulong address);
    /// <summary>
    /// 这个地址上的指针字是链接期常量时，是它的值：地址位于装入后只读的区域（重定位只读段），
    /// 内容由文件内容与相对重定位决定。
    /// </summary>
    ulong? LinkConstant(ulong address);
    /// <summary>这个地址是一个类型的元数据槽时，是那个类型：槽初始化之后的内容是该类型的类指针。依据是槽里的编码。</summary>
    EntityRef? TypeAtSlot(ulong address);
    /// <summary>这个地址是一个字符串字面量的元数据槽时，是那个字符串：槽初始化之后的内容是该字面量对象的指针。依据是槽里的编码。</summary>
    EntityRef? StringAtSlot(ulong address) => null;
    /// <summary>方法定义或方法引用的元数据槽初始化后指向的方法实体。</summary>
    EntityRef? MethodAtSlot(ulong address) => null;
    /// <summary>
    /// 这个地址是一个元数据槽（任何用途）：槽里是编码，初始化之后换成运行时对象的指针，此后不变。
    /// 槽在被读取时已经初始化（设计 16.2），所以它的读取没有版本。
    /// </summary>
    bool MetadataSlot(ulong address) => EntityAtSlot(address) is not null;
    /// <summary>元数据槽初始化之后的内容代表的实体：类型、字符串字面量或方法。</summary>
    EntityRef? EntityAtSlot(ulong address) => TypeAtSlot(address) ?? StringAtSlot(address) ?? MethodAtSlot(address);
}
