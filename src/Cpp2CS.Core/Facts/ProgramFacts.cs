using Cpp2CS.Facts.Derived;

namespace Cpp2CS.Facts;

/// <summary>基础事实与派生事实的只读组合；初始化转发保留构造兼容性。</summary>
public sealed class ProgramFacts
{
    public BaseFacts Base { get; private set; } = new();
    public DerivedFacts Derived { get; private set; } = new();
    public ProgramFacts() { }
    public ProgramFacts(BaseFacts basis, DerivedFacts derived) { Base = basis; Derived = derived; }
    public ProgramModel Model { get => Base.Model; init => Base = Base with { Model = value }; }
    public CodeMap Code { get => Base.Code; init => Base = Base with { Code = value }; }
    public CodeScan Scan { get => Base.Scan; init => Base = Base with { Scan = value }; }
    public Registrations Registrations { get => Base.Registrations; init => Base = Base with { Registrations = value }; }
    public UsageSlots Usages { get => Base.Usages; init => Base = Base with { Usages = value }; }
    public RuntimeHelpers Helpers { get => Base.Helpers; init => Base = Base with { Helpers = value }; }
    public FieldLayouts Layouts { get => Base.Layouts; init => Base = Base with { Layouts = value }; }
    public FactChecks Checks { get => Base.Checks; init => Base = Base with { Checks = value }; }
    public IReadOnlyDictionary<string, double> Timings { get => Base.Timings; init => Base = Base with { Timings = value }; }
    public Cpp2CS.Options.RecoveryOptions Options { get => Base.Options; init => Base = Base with { Options = value }; }
    public UnregisteredMethods Unregistered { get => Derived.Unregistered; init => Derived = Derived with { Unregistered = value }; }
    public CodeEntry[] EntriesAt(ulong address) => Base.EntriesAt(address);
}
