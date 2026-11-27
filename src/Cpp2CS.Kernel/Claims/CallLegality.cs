using Cpp2CS.Spec.Catalog;
using Cpp2CS.Kernel.Engine;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Kernel;

/// <summary>
/// 调用的写法是否合法（设计第 9 节“合法”）。行为等价不够：共同执行分不出 call 与 callvirt，也分不出直接基类的构造函数与更远的祖先的构造函数，
/// 但写出的 IL 必须能通过验证（ECMA-335 III.1.8.1.4、III.3.19、III.4.2）。
/// </summary>
public static class CallLegality
{
    /// <summary>
    /// 不合法时给出原因，合法时为空。operation 是声明的目录项（按它的 IL 助记符判断）；target 是被调方法；host 是宿主方法；receiverIsHostThis：第 0 个操作数就是宿主方法入口处的 this。
    /// 只问实体之间的关系，不需要方法的形状。
    /// 元数据回答不了的事实按不合法处理。
    /// </summary>
    public static string? Check(CatalogEntry entry, EntityRef target, bool receiverIsHostThis, EntityRef host, IEntityMetadata metadata)
    {
        string operation = entry.Il;
        if (operation is not ("call" or "callvirt")) return null;
        if (metadata.DeclaringTypeOf(target) is not { } owner) return $"{target} 所属的类型不可知";
        if (metadata.IsValueType(owner) is not bool valueType) return $"{target} 所属的类型是不是值类型不可知";
        if (metadata.IsInstanceConstructor(target) is not bool constructor) return $"{target} 是不是实例构造函数不可知";
        if (operation == "callvirt")
        {
            if (constructor) return $"{target} 是构造函数：不能用 callvirt 调用";
            // 值类型的方法不经虚表，接收方是托管指针：callvirt 只在带 constrained. 前缀、目标声明在引用类型上时用于值类型。
            return valueType ? $"{target} 声明在值类型上：须用 call" : null;
        }
        // 值类型的构造函数可以对着一个地址直接调用（ldloca; …; call .ctor）。
        if (!constructor || valueType) return null;
        // 引用类型的构造函数经 call 调用，只用于在构造函数里初始化 this；创建对象用 newobj。
        if (metadata.IsInstanceConstructor(host) != true) return $"{target} 是构造函数：只有构造函数里才能用 call 调用它";
        if (!receiverIsHostThis) return $"{target} 是构造函数：call 的接收方须是本方法的 this";
        if (metadata.DeclaringTypeOf(host) is not { } hostType) return "本方法所属的类型不可知";
        if (owner == hostType || metadata.BaseOf(hostType) is { } parent && parent == owner) return null;
        return $"{target} 不是本类或直接基类的构造函数";
    }

    /// <summary>宿主方法入口处的 this：按调用约定取第 0 个形参的入口槽位。没有 this 或槽位未声明时为空。</summary>
    public static Term? HostThis(MethodSnapshot snapshot, MethodShape host)
    {
        if (!host.HasThis || EngineFacts.Convention(host, out _, out _) is not { Length: > 0 } convention) return null;
        return EngineFacts.Gather(snapshot.Terms, convention[0], slot => snapshot.EntryParameters.FirstOrDefault(p => p.Slot == slot));
    }
}
