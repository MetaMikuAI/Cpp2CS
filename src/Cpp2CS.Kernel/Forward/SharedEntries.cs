using Cpp2CS.Kernel.Engine;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Kernel.Forward;

/// <summary>登记的泛型代码入口及其隐含方法指针应指向的实体。多个实体登记同一地址时可证共享。</summary>
public sealed record GenericEntry(ulong Address, EntityRef ExpectedMethod, bool MultipleEntities);

public interface IGenericEntryFacts : INativeFacts
{
    GenericEntry? GenericEntry(EntityRef method);
}

public static class NativeEntryQueries
{
    /// <summary>返回泛型实例的入口与隐含实参要求；事实提供方没有对应登记时为空。</summary>
    public static GenericEntry? GenericEntry(this INativeFacts facts, EntityRef method) =>
        (facts as IGenericEntryFacts)?.GenericEntry(method);
}
