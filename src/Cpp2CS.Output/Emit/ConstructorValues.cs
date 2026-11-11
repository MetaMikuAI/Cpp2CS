
namespace Cpp2CS.Output;

/// <summary>构造体的局部定义、参数来源与本类字段位置；初始化检查和源码形式共用。</summary>
internal sealed class ConstructorValues
{
    private readonly TypeDef owner;
    private readonly Dictionary<LocalId, List<ManagedValue>> definitions = [];
    private readonly Dictionary<LocalId, int> uses = [];
    public IReadOnlyDictionary<LocalId, List<ManagedValue>> Definitions => definitions;
    public IReadOnlyDictionary<LocalId, int> Uses => uses;

    public ConstructorValues(ManagedBody body)
    {
        owner = body.Method.Method.Owner;
        void Define(LocalValue local, ManagedValue value)
        {
            if (!definitions.TryGetValue(local.Id, out var values)) definitions.Add(local.Id, values = []);
            values.Add(value);
        }
        void Use(ManagedValue value)
        {
            foreach (var local in ManagedValues.Walk(value).OfType<LocalValue>()) uses[local.Id] = uses.GetValueOrDefault(local.Id) + 1;
        }
        foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
        {
            if (statement is ManagedAssignment assignment) Define(assignment.Target, assignment.Value);
            foreach (var value in ManagedValues.Of(statement).Where(v => statement is not ManagedAssignment a || !ReferenceEquals(v, a.Target))) Use(value);
            foreach (var copy in ManagedValues.Edges(statement).SelectMany(e => e.Copies)) { Define(copy.Target, copy.Value); Use(copy.Value); }
        }
    }

    public bool IsThis(ManagedValue value)
    {
        var pending = new Stack<ManagedValue>(); pending.Push(value);
        var seen = new HashSet<LocalId>();
        var found = false;
        while (pending.TryPop(out var current))
        {
            if (current is ArgumentValue { Index: -1 }) { found = true; continue; }
            if (current is not LocalValue local || !definitions.TryGetValue(local.Id, out var sources)) return false;
            if (seen.Add(local.Id)) foreach (var source in sources) pending.Push(source);
        }
        return found;
    }
    // 值（沿局部变量的定义展开）是否引用了满足 argument 的参数
    public bool UsesArgument(ManagedValue value, Func<ArgumentValue, bool> argument)
    {
        var pending = new Stack<ManagedValue>(); pending.Push(value);
        var seen = new HashSet<LocalId>();
        while (pending.TryPop(out var current))
        {
            if (current is ArgumentValue a && argument(a)) return true;
            if (current is LocalValue local && seen.Add(local.Id) && definitions.TryGetValue(local.Id, out var sources))
                foreach (var source in sources) pending.Push(source);
            foreach (var child in ManagedValues.Children(current)) pending.Push(child);
        }
        return false;
    }
    public bool UsesThis(ManagedValue value) => UsesArgument(value, a => a.Index == -1);
    public bool IsInitialization(ManagedStatement statement) =>
        statement is ManagedCall { Invocation: { Method.Method.Name: ".ctor", Receiver: { } receiver } } && IsThis(receiver);
    public FieldValue? OwnField(ManagedValue value) => value switch
    {
        IndirectValue { Address: AddressValue address } => OwnField(address.Target),
        FieldValue f when IsThis(f.Receiver) && f.Field.Field.Owner == owner => f,
        FieldValue { Receiver: AddressValue address } => OwnField(address.Target),
        _ => null,
    };
    public bool IsOwnFieldStore(ManagedStatement statement) => statement is ManagedStore s && OwnField(s.Target) is not null;
    public string StorePath(ManagedValue value) => value switch
    {
        IndirectValue { Address: AddressValue address } => StorePath(address.Target),
        FieldValue { Receiver: AddressValue address } field => StorePath(address.Target) + $".{field.Field.Field.Index}",
        FieldValue field => $"field#{field.Field.Field.Index}",
        _ => "",
    };
}
