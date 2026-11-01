using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Recovery.Values;

/// <summary>求值器向外界查询的边界：入口值与调用结果。</summary>
public interface IValueEnvironment
{
    /// <summary>存储单元在函数入口的值；null 表示没有依据。</summary>
    Sym? Entry(SymTable syms, Storage storage);

    /// <summary>调用定义 Results[index] 的值；null 表示没有依据。</summary>
    Sym? CallResult(SymTable syms, Call call, int index, IReadOnlyList<Sym> arguments);
}

/// <summary>
/// 一个机器函数的符号值：每个 SSA 变量、每条语句的每个操作数各对应一个符号值。
/// 按逆后序求值：进入块时填入已求值前驱的 φ 来源，回边来源在全部定义求值后填入；
/// 平凡 φ 转发后重新求值，直到不再出现新的平凡 φ。
/// 求值只读机器函数，不改写它。
/// </summary>
public sealed class ValueModel
{
    private const int MaxPasses = 8;

    private readonly MachineFunction function;
    private readonly IValueEnvironment environment;
    private readonly Block[] order;
    private readonly HashSet<Block> visited = [];
    private readonly Dictionary<Variable, Sym> values = [];
    private readonly Dictionary<Stmt, Sym[]> operands = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<Stmt, Block> blocks = new(ReferenceEqualityComparer.Instance);
    private Stmt? site;
    private int ordinal;

    public SymTable Syms { get; } = new();
    public MachineFunction Function => function;
    public int Passes { get; private set; }

    private ValueModel(MachineFunction function, IValueEnvironment environment)
    {
        this.function = function;
        this.environment = environment;
        order = ReversePostorder(function);
    }

    private static Block[] ReversePostorder(MachineFunction function)
    {
        var result = new List<Block>();
        var seen = new HashSet<Block>();
        var stack = new Stack<(Block Block, int Next)>();
        stack.Push((function.EntryBlock, 0));
        seen.Add(function.EntryBlock);
        while (stack.Count > 0)
        {
            var (block, next) = stack.Pop();
            if (next < block.Successors.Count)
            {
                stack.Push((block, next + 1));
                var successor = block.Successors[next];
                if (seen.Add(successor)) stack.Push((successor, 0));
                continue;
            }
            result.Add(block);
        }
        result.Reverse();
        return result.ToArray();
    }

    public static ValueModel Build(MachineFunction function, IValueEnvironment environment)
    {
        var model = new ValueModel(function, environment);
        model.Run();
        return model;
    }

    public Sym Of(Variable variable) => SymTable.Resolve(values.TryGetValue(variable, out var value) ? value : Missing(variable));

    /// <summary>语句的操作数，顺序同 <see cref="ExprMap.Operands"/>。</summary>
    public IReadOnlyList<Sym> Operands(Stmt statement) => operands.TryGetValue(statement, out var list) ? list.Select(SymTable.Resolve).ToArray() : [];

    public Block BlockOf(Stmt statement) => blocks[statement];

    private void Run()
    {
        for (Passes = 1; Passes <= MaxPasses; Passes++)
        {
            values.Clear();
            operands.Clear();
            visited.Clear();
            foreach (var block in order)
            {
                FillSources(block);
                foreach (var statement in block.Statements)
                {
                    blocks[statement] = block;
                    Evaluate(block, statement);
                }
                visited.Add(block);
            }
            foreach (var block in order) FillSources(block);
            if (!ForwardTrivial()) break;
        }
    }

    /// <summary>来源（除自身外）只有一个值的 φ 等于该值。</summary>
    private bool ForwardTrivial()
    {
        var changed = false;
        foreach (var phi in Syms.Phis.ToArray())
        {
            if (phi.Forward is not null || phi.Sources.Any(s => s is null)) continue;
            var distinct = phi.Sources.Select(s => SymTable.Resolve(s!)).Where(s => !ReferenceEquals(s, phi)).Distinct().ToArray();
            if (distinct.Length > 1) continue;
            phi.Forward = distinct.Length == 1 ? distinct[0] : Syms.Undef(phi.Width);
            changed = true;
        }
        return changed;
    }

    /// <summary>填入已求值前驱的 φ 来源。</summary>
    private void FillSources(Block block)
    {
        foreach (var phi in block.Statements.OfType<Phi>())
        {
            var sym = Syms.Phi(block, phi.Target, phi.Target.Width);
            for (var i = 0; i < phi.Sources.Length; i++)
                if (visited.Contains(block.Predecessors[i]))
                    Syms.SetSource(sym, i, phi.Sources[i] is { } source ? Value(source) : Syms.Unknown("φ 来源缺失", phi.Target.Width));
        }
    }

    private void Evaluate(Block block, Stmt statement)
    {
        site = statement;
        ordinal = 0;
        if (statement is Phi phi)
        {
            values[phi.Target] = Syms.Phi(block, phi.Target, phi.Target.Width);
            return;
        }
        var list = ExprMap.Operands(statement).Select(Eval).ToArray();
        operands[statement] = list;
        switch (statement)
        {
            case Define define:
                values[define.Target] = list[0];
                break;
            case Call call:
                {
                    var arguments = list.AsSpan(1, call.Arguments.Length).ToArray();
                    for (var r = 0; r < call.Defines.Length; r++)
                        if (call.Defines[r] is { } target)
                            values[target] = environment.CallResult(Syms, call, r, arguments) is { } result
                                ? Syms.Widen(result, target.Width) : Syms.Widen(Syms.Result(call, r + 1, target.Width), target.Width);
                    break;
                }
        }
    }

    private Sym Value(Variable variable) => values.TryGetValue(variable, out var value) ? value : Missing(variable);

    private Sym Missing(Variable variable) => variable.Version switch
    {
        0 => environment.Entry(Syms, variable.Storage) is { } entry ? Syms.Widen(entry, variable.Width) : Syms.Unknown($"入口 {variable.Storage}", variable.Width),
        < 0 => Syms.Unknown($"{variable.Storage} 被调用破坏", variable.Width),
        _ => Syms.Unknown($"{variable} 没有定义", variable.Width),
    };

    private Sym Eval(Expr expression)
    {
        switch (expression)
        {
            case Const c:
                return c.Width <= 64 ? Syms.Const(c.Value, c.Width) : Syms.ZeroExtend(Syms.Const(c.Value, 64), c.Width);
            case Use u:
                return Syms.Slice(Value(u.Variable), 0, u.Width);
            case Load load:
                {
                    var address = Eval(load.Address);
                    return Syms.Read(site!, ordinal++, address, load.Width);
                }
            case Binary b:
                return Syms.Binary(b.Op, Eval(b.Left), Eval(b.Right), b.Width);
            case Unary u:
                return Syms.Unary(u.Op, Eval(u.Operand), u.Width);
            case Compare c:
                return Syms.Compare(c.Cond, Eval(c.Left), Eval(c.Right));
            case Ir.Convert c:
                return Syms.Convert(c.Kind, Eval(c.Operand), c.Width);
            case Select s:
                return Syms.Select(Eval(s.Condition), Eval(s.True), Eval(s.False), s.Width);
            case Logical l:
                return Syms.Logical(l.IsAnd, Eval(l.Left), Eval(l.Right));
            case Not n:
                return Syms.Not(Eval(n.Operand));
            case Extract x:
                return Syms.Slice(Eval(x.Operand), x.Low, x.Width);
            case Insert i:
                {
                    var target = Eval(i.Base);
                    var value = Eval(i.Value);
                    var high = i.Low + value.Width;
                    var parts = new List<Sym>();
                    if (i.Low > 0) parts.Add(Syms.Slice(target, 0, i.Low));
                    parts.Add(value);
                    if (high < target.Width) parts.Add(Syms.Slice(target, high, target.Width - high));
                    return Syms.Concat(parts);
                }
            case FrameAddress f:
                return Syms.Frame(f.Offset);
            case Entry e:
                return environment.Entry(Syms, e.Storage) is { } entry ? Syms.Widen(entry, e.Width) : Syms.Unknown($"入口 {e.Storage}", e.Width);
            case Symbol s:
                return Syms.Entity(s);
            case Unknown u:
                return Syms.Unknown(u.Reason, u.Width);
            case Intrinsic i:
                return Syms.Intrinsic(i.Name, i.Arguments.Select(Eval).ToArray(), i.Width);
            case Flags or TestFlags or ConditionalFlags:
                return Syms.Unknown("未归一的标志位", Math.Max(1, expression.Width));
            default:
                return Syms.Unknown($"表达式 {expression.GetType().Name}", Math.Max(1, expression.Width));
        }
    }
}
