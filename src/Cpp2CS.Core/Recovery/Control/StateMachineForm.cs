using Cpp2CS.Ir;
using Cpp2CS.Managed;

namespace Cpp2CS.Recovery.Control;

/// <summary>
/// 状态机 MoveNext 的共同部分：入口读状态、按状态走分派、把分派写成反编译器能追踪的形态。async 和迭代器都按 Roslyn 的形态写回。
/// </summary>
internal abstract class StateMachineForm
{
    internal const string StateName = "<>1__state";
    internal const string ThisName = "<>4__this";
    protected const int Budget = 64;
    /// <summary>新块的地址不对应原生代码，取高位以免与原生块和 finally 的新块重合。</summary>
    private const ulong SyntheticAddress = 5UL << 60;

    protected ManagedBody body;
    protected readonly Dictionary<ulong, List<ManagedStatement>> code;
    protected readonly ulong entry;
    /// <summary>方法体可能已经过一轮这里的改写，新块不能和已有的同址。</summary>
    private ulong nextBlock;
    /// <summary>新块排在哪个原有块之后，并和它属于同样的内层区域。</summary>
    protected readonly List<(ulong Block, ulong Origin)> added = [];
    /// <summary>入口读状态的局部，即 Roslyn 的 num。</summary>
    protected LocalValue? num;
    public string? Reason { get; private set; }

    protected StateMachineForm(ManagedBody source)
    {
        body = source;
        code = source.Blocks.ToDictionary(b => b.Address, b => b.Statements.ToList());
        entry = source.Blocks[0].Address;
        nextBlock = source.Blocks.Select(b => b.Address).Where(a => a >> 60 == SyntheticAddress >> 60).Select(a => ((a ^ SyntheticAddress) >> 40) + 1).DefaultIfEmpty(0UL).Max();
    }

    protected bool Fail(string reason)
    {
        Reason ??= reason;
        return false;
    }

    internal static bool IsLocal(ManagedValue? value, Variable variable) => value is LocalValue local && local.Variable.Equals(variable);

    protected static bool IsField(ManagedValue? value, string name) => value is FieldValue { Receiver: ArgumentValue { Index: -1 } } field && field.Field.Field.Name == name;
    protected static long? StateStored(ManagedStatement statement) =>
        statement is ManagedStore { Target: var target, Value: ConstantValue constant } && IsField(target, StateName) ? (int)constant.Bits : null;

    protected ulong Fresh() => SyntheticAddress | nextBlock++ << 40;
    protected ulong FreshAfter(ulong origin)
    {
        var block = Fresh();
        added.Add((block, origin));
        return block;
    }
    protected ulong[] Predecessors(ulong target) =>
        code.Where(p => p.Value.SelectMany(ManagedValues.Edges).Any(e => e.Target == target)).Select(p => p.Key).ToArray();

    protected LocalValue? StateLocal()
    {
        var (at, index) = (entry, 0);
        for (var steps = 0; steps < Budget; steps++)
            switch (code[at].ElementAtOrDefault(index))
            {
                case ManagedAssignment { Target: var target, Value: var value } when IsField(value, StateName): return target;
                case ManagedAssignment { Value: var value } when IsField(value, ThisName): index++; break;
                case ManagedJump { Edge: { Copies.Count: 0 } edge }: (at, index) = (edge.Target, 0); break;
                default: return null;
            }
        return null;
    }

    /// <summary>
    /// 读 this 的语句可能夹在两次状态比较之间，反编译器追踪分派时走到别的语句就停下，后面的比较留在输出里。
    /// 读这个字段没有副作用，也没有别的写入时，提到读状态之后。
    /// </summary>
    protected bool HoistThis()
    {
        if (num is not { } cached) return true;
        var (at, index) = (entry, 0);
        var before = new HashSet<ulong>();
        for (var steps = 0; steps < Budget; steps++)
        {
            var statement = code[at].ElementAtOrDefault(index);
            if (statement is ManagedAssignment { Target: var target, Value: var value } && target.Variable.Equals(cached.Variable) && IsField(value, StateName)) break;
            if (statement is ManagedAssignment { Value: var read } && IsField(read, ThisName)) index++;
            else if (statement is ManagedJump { Edge: { Copies.Count: 0 } edge })
            {
                before.Add(at);
                (at, index) = (edge.Target, 0);
            }
            else return true;
        }
        var dispatch = new HashSet<ulong>();
        foreach (var state in code.Values.SelectMany(s => s).Select(StateStored).OfType<long>().Append(-1).Distinct())
            if (state >= -1) Dispatch(state, visited: dispatch);
        var insert = index + 1;
        foreach (var address in dispatch.Where(a => !before.Contains(a)))
            for (var i = address == at ? insert : 0; i < code[address].Count; i++)
            {
                if (code[address][i] is not ManagedAssignment { Target: var target, Value: var value } assignment || !IsField(value, ThisName)) continue;
                if (address == at && i == insert) { insert++; continue; }
                if (!OnlyThis(target.Variable)) return Fail("num:this");
                code[address].RemoveAt(i--);
                code[at].Insert(insert++, assignment);
            }
        return true;
    }

    protected bool OnlyThis(Variable variable) => code.Values.SelectMany(s => s).All(s => s switch
    {
        ManagedAssignment { Target: var target, Value: var value } when target.Variable.Equals(variable) => IsField(value, ThisName),
        ManagedCall { Result: { } result } when result.Variable.Equals(variable) => false,
        _ => !ManagedValues.Edges(s).SelectMany(e => e.Copies).Any(c => c.Target.Variable.Equals(variable)),
    });

    /// <summary>
    /// clang 把 switch (num) 降级成无符号范围检查加跳转表。无符号比较写到 IL 上带转换，反编译器追踪状态局部时不认，也不是 Roslyn 的写法，拆成两个有符号比较。
    /// </summary>
    protected void SignedRangeChecks()
    {
        if (num is not { } cached) return;
        foreach (var at in code.Keys.ToArray())
        {
            if (code[at] is not [.., ManagedBranch { Condition: ComparisonValue { Left: var left, Right: ConstantValue bound } test } branch]) continue;
            // case 不从 0 开始时检查的是 num + 偏移。
            int? offset = left switch
            {
                BinaryValue { Op: BinOp.Add, Left: var added, Right: ConstantValue constant } when IsLocal(added, cached.Variable) => (int)constant.Bits,
                _ when IsLocal(left, cached.Variable) => 0,
                _ => null,
            };
            if (offset is not { } shift) continue;
            var (inside, outside, limit) = test.Condition switch
            {
                Cond.Ule => (branch.Taken, branch.Fallthrough, bound.Bits + 1),
                Cond.Ult => (branch.Taken, branch.Fallthrough, bound.Bits),
                Cond.Ugt => (branch.Fallthrough, branch.Taken, bound.Bits + 1),
                Cond.Uge => (branch.Fallthrough, branch.Taken, bound.Bits),
                _ => (null!, null!, 0UL),
            };
            if (inside is null) continue;
            ComparisonValue Below(long value) => new(Cond.Slt, cached, new ConstantValue((uint)(int)value, cached.Type, cached.Width), test.Type);
            var upper = FreshAfter(at);
            code[upper] = [new ManagedBranch(branch.Address, Below((long)limit - shift), inside, outside)];
            code[at][^1] = new ManagedBranch(branch.Address, Below(-(long)shift), outside, new ManagedEdge(upper, []));
        }
    }

    protected static long? Evaluate(ManagedValue value, HashSet<Variable> state, long known) =>
        ConstantConditions.Evaluate(value, leaf => leaf is LocalValue local && state.Contains(local.Variable) || IsField(leaf, StateName) ? known : null);

    /// <summary>
    /// 按状态值走入口的分派，停在第一条不是分派的语句。selectors 是 try 入口的序号局部：
    /// 走过的边写入序号，分派块按序号选择，选择记到 entered，经过的边记到 used。
    /// </summary>
    protected (ulong Block, int Index)? Dispatch(long known, HashSet<Variable>? selectors = null, List<(ulong Block, int Case)>? entered = null, HashSet<ManagedEdge>? used = null, HashSet<ulong>? visited = null)
    {
        var state = new HashSet<Variable>();
        var selected = new Dictionary<Variable, int>();
        var (at, index) = (entry, 0);
        bool Passes(ManagedEdge edge) => edge.Copies.All(c => selectors is not null && selectors.Contains(c.Target.Variable) && c.Value is ConstantValue);
        void Take(ManagedEdge edge)
        {
            foreach (var copy in edge.Copies) selected[copy.Target.Variable] = (int)((ConstantValue)copy.Value).Bits;
            if (edge.Copies.Count > 0) used?.Add(edge);
            (at, index) = (edge.Target, 0);
        }
        for (var steps = 0; steps < Budget; steps++)
        {
            if (index >= code[at].Count) return null;
            visited?.Add(at);
            switch (code[at][index])
            {
                case ManagedAssignment { Target: var target, Value: var value } when IsField(value, StateName):
                    state.Add(target.Variable);
                    index++;
                    break;
                case ManagedAssignment { Value: var value } when IsField(value, ThisName):
                    index++;
                    break;
                case ManagedJump { Edge: var edge } when Passes(edge):
                    Take(edge);
                    break;
                case ManagedBranch branch when Evaluate(branch.Condition, state, known) is { } taken && Passes(taken != 0 ? branch.Taken : branch.Fallthrough):
                    Take(taken != 0 ? branch.Taken : branch.Fallthrough);
                    break;
                case ManagedSwitch { Index: LocalValue selector } choice when selected.TryGetValue(selector.Variable, out var chosen) && chosen >= 0 && chosen < choice.Cases.Count && Passes(choice.Cases[chosen]):
                    entered?.Add((at, chosen));
                    Take(choice.Cases[chosen]);
                    break;
                case ManagedSwitch choice when Evaluate(choice.Index, state, known) is { } value && value >= 0 && value < choice.Cases.Count && Passes(choice.Cases[(int)value]):
                    Take(choice.Cases[(int)value]);
                    break;
                default:
                    return (at, index);
            }
        }
        return null;
    }

    protected bool ReadElsewhere(Variable variable, ManagedStatement except) =>
        code.Values.SelectMany(s => s).Where(s => !ReferenceEquals(s, except))
            .SelectMany(s => (s is ManagedAssignment assignment ? [assignment.Value] : ManagedValues.Of(s)).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk).Any(v => IsLocal(v, variable));
}
