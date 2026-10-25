using Cpp2CS.Model;

namespace Cpp2CS.Facts;

/// <summary>
/// 程序级基础事实：代码地图、引用普查、元数据模型、注册表入口及各自的不变式检查。
/// 后续层（提升、恢复）只查询这里，不重复做全局推断。
/// </summary>
public sealed class ProgramFacts
{
    public required ProgramModel Model { get; init; }
    public required CodeMap Code { get; init; }
    public required CodeScan Scan { get; init; }
    public required Registrations Registrations { get; init; }
    public required UsageSlots Usages { get; init; }
    public required RuntimeHelpers Helpers { get; init; }
    public required FieldLayouts Layouts { get; init; }
    public required FactChecks Checks { get; init; }
    public required IReadOnlyDictionary<string, double> Timings { get; init; }

    public UnregisteredMethods Unregistered { get; init; } = UnregisteredMethods.Empty;

    /// <summary>函数入口上的全部注册表入口（ICF/共享代码的所有者集合）。</summary>
    public CodeEntry[] EntriesAt(ulong address) => Registrations.At(address);
}
