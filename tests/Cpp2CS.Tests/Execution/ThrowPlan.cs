using Cpp2CS.Model;

namespace Cpp2CS.Tests.Execution;

/// <summary>调用事件从零编号；同一个不可变计划交给两侧，异常对象按相同分配次序产生。</summary>
internal sealed record ThrowPlan(int CallEvent, TypeRef Type);
internal sealed class PlannedThrow(ulong value) : Exception
{
    public ulong Object { get; } = value;
}

internal sealed partial class World
{
    public ThrowPlan? ThrowPlan { get; set; }
}
