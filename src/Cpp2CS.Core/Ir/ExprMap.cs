
namespace Cpp2CS.Ir;

/// <summary>表达式的通用遍历与重写。重写时子表达式不变则复用原对象。</summary>
public static class ExprMap
{
    /// <summary>自顶向下重写：f 返回非 null 时用其结果替换该节点（不再深入）。</summary>
    public static Expr Map(Expr expr, Func<Expr, Expr?> f)
    {
        if (f(expr) is { } replaced) return replaced;
        switch (expr)
        {
            case Binary b:
                {
                    var l = Map(b.Left, f); var r = Map(b.Right, f);
                    return ReferenceEquals(l, b.Left) && ReferenceEquals(r, b.Right) ? b : b with { Left = l, Right = r };
                }
            case Unary u:
                {
                    var o = Map(u.Operand, f);
                    return ReferenceEquals(o, u.Operand) ? u : u with { Operand = o };
                }
            case Convert c:
                {
                    var o = Map(c.Operand, f);
                    return ReferenceEquals(o, c.Operand) ? c : c with { Operand = o };
                }
            case Compare c:
                {
                    var l = Map(c.Left, f); var r = Map(c.Right, f);
                    return ReferenceEquals(l, c.Left) && ReferenceEquals(r, c.Right) ? c : c with { Left = l, Right = r };
                }
            case Select s:
                {
                    var c = Map(s.Condition, f); var t = Map(s.True, f); var e = Map(s.False, f);
                    return ReferenceEquals(c, s.Condition) && ReferenceEquals(t, s.True) && ReferenceEquals(e, s.False) ? s : s with { Condition = c, True = t, False = e };
                }
            case Logical l:
                {
                    var a = Map(l.Left, f); var b = Map(l.Right, f);
                    return ReferenceEquals(a, l.Left) && ReferenceEquals(b, l.Right) ? l : l with { Left = a, Right = b };
                }
            case Not n:
                {
                    var o = Map(n.Operand, f);
                    return ReferenceEquals(o, n.Operand) ? n : n with { Operand = o };
                }
            case Extract e:
                {
                    var o = Map(e.Operand, f);
                    return ReferenceEquals(o, e.Operand) ? e : e with { Operand = o };
                }
            case Insert i:
                {
                    var b = Map(i.Base, f); var v = Map(i.Value, f);
                    return ReferenceEquals(b, i.Base) && ReferenceEquals(v, i.Value) ? i : new Insert(b, v, i.Low);
                }
            case Load l:
                {
                    var a = Map(l.Address, f);
                    return ReferenceEquals(a, l.Address) ? l : l with { Address = a };
                }
            case Flags fl:
                {
                    var l = Map(fl.Left, f); var r = fl.Right is null ? null : Map(fl.Right, f);
                    return ReferenceEquals(l, fl.Left) && ReferenceEquals(r, fl.Right) ? fl : fl with { Left = l, Right = r };
                }
            case TestFlags t:
                {
                    var o = Map(t.FlagsValue, f);
                    return ReferenceEquals(o, t.FlagsValue) ? t : t with { FlagsValue = o };
                }
            case ConditionalFlags c:
                {
                    var a = Map(c.Condition, f); var b = Map(c.Taken, f);
                    return ReferenceEquals(a, c.Condition) && ReferenceEquals(b, c.Taken) ? c : c with { Condition = a, Taken = b };
                }
            case Intrinsic i:
                {
                    Expr[]? args = null;
                    for (var k = 0; k < i.Arguments.Length; k++)
                    {
                        var a = Map(i.Arguments[k], f);
                        if (ReferenceEquals(a, i.Arguments[k])) continue;
                        args ??= (Expr[])i.Arguments.Clone();
                        args[k] = a;
                    }
                    return args is null ? i : i with { Arguments = args };
                }
            default:
                return expr;
        }
    }

    public static IEnumerable<Expr> Children(Expr expr) => expr switch
    {
        Binary b => [b.Left, b.Right],
        Unary u => [u.Operand],
        Convert c => [c.Operand],
        Compare c => [c.Left, c.Right],
        Select s => [s.Condition, s.True, s.False],
        Logical l => [l.Left, l.Right],
        Not n => [n.Operand],
        Extract e => [e.Operand],
        Insert i => [i.Base, i.Value],
        Load l => [l.Address],
        Flags f => f.Right is null ? [f.Left] : [f.Left, f.Right],
        TestFlags t => [t.FlagsValue],
        ConditionalFlags c => [c.Condition, c.Taken],
        Intrinsic i => i.Arguments,
        _ => [],
    };

    /// <summary>先序枚举所有子节点（含自身）。</summary>
    public static IEnumerable<Expr> Walk(Expr expr)
    {
        var stack = new Stack<Expr>();
        stack.Push(expr);
        while (stack.Count > 0)
        {
            var e = stack.Pop();
            yield return e;
            foreach (var child in Children(e)) stack.Push(child);
        }
    }

    /// <summary>语句直接包含的表达式。</summary>
    public static IEnumerable<Expr> Operands(Stmt stmt) => stmt switch
    {
        Assign a => [a.Value],
        Define d => [d.Value],
        Store s => [s.Target, s.Value],
        Call c => [c.Target, .. c.Arguments, .. c.DelegateReceiver is { } receiver ? new[] { receiver } : []],
        Branch b => [b.Condition],
        IndirectJump j => [j.Target],
        Return r => [.. r.Value is { } v ? new[] { v } : [], .. r.Pieces.Select(p => p.Value), .. r.Buffer is { } b ? new[] { b } : []],
        _ => [],
    };

    /// <summary>重写语句中的全部表达式（不改变定义目标）。</summary>
    public static Stmt MapOperands(Stmt stmt, Func<Expr, Expr> f)
    {
        switch (stmt)
        {
            case Assign a: { var v = f(a.Value); return ReferenceEquals(v, a.Value) ? a : a with { Value = v }; }
            case Define d: { var v = f(d.Value); return ReferenceEquals(v, d.Value) ? d : d with { Value = v }; }
            case Store s:
                {
                    var t = f(s.Target); var v = f(s.Value);
                    return ReferenceEquals(t, s.Target) && ReferenceEquals(v, s.Value) ? s : s with { Target = t, Value = v };
                }
            case Call c:
                {
                    var t = f(c.Target);
                    var args = c.Arguments.Select(f).ToArray();
                    var receiver = c.DelegateReceiver is { } r ? f(r) : null;
                    return ReferenceEquals(t, c.Target) && ReferenceEquals(receiver, c.DelegateReceiver) && args.AsSpan().SequenceEqual(c.Arguments)
                        ? c : c with { Target = t, Arguments = args, DelegateReceiver = receiver };
                }
            case Branch b: { var v = f(b.Condition); return ReferenceEquals(v, b.Condition) ? b : b with { Condition = v }; }
            case IndirectJump j: { var v = f(j.Target); return ReferenceEquals(v, j.Target) ? j : j with { Target = v }; }
            case Return r:
                {
                    var v = r.Value is null ? null : f(r.Value);
                    var b = r.Buffer is null ? null : f(r.Buffer);
                    var pieces = r.Pieces.Select(p => p with { Value = f(p.Value) }).ToArray();
                    return ReferenceEquals(v, r.Value) && ReferenceEquals(b, r.Buffer) && pieces.AsSpan().SequenceEqual(r.Pieces)
                        ? r : r with { Value = v, Buffer = b, Pieces = pieces };
                }
            default: return stmt;
        }
    }
}
