using Cpp2CS.Ir;
using System.Collections.Immutable;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>
/// 共享的路径条件与形参绑定。Φ 是原子文字（规范化的 1 位项）的集合；判定只用文字本身、已知值、整数区间与非空事实，
/// 判定不出时为 null，由共同执行分叉。判定能力只影响完备性：分叉总是健全的。
/// θ 把模板形参映射到调用方的项，首次需要时绑定，之后必须一致；一次证明只有一组实参。
/// </summary>
internal sealed class Solver(TermTable terms, ManagedTypes? types = null)
{
    public TermTable Terms => terms;
    private readonly Dictionary<Term, Term> theta = new(ReferenceEqualityComparer.Instance);
    private Dictionary<Term, Term> memo = new(ReferenceEqualityComparer.Instance);
    /// <summary>分配得到的对象（各次分配互不相同，也不同于分配之前已有的值）。</summary>
    public HashSet<Term> Allocations { get; } = new(ReferenceEqualityComparer.Instance);

    public IReadOnlyDictionary<Term, Term> Binding => theta;
    public int Version { get; private set; }

    public Term? Bound(Term formal) => theta.GetValueOrDefault(formal);

    public void Bind(IEnumerable<KeyValuePair<Term, Term>> trial)
    {
        foreach (var (formal, value) in trial)
        {
            trail.Add((formal, theta.GetValueOrDefault(formal)));
            theta[formal] = value;
            Version++;
        }
        memo = new(ReferenceEqualityComparer.Instance);
    }

    /// <summary>绑定的记录，用于撤销到某个标记。</summary>
    private readonly List<(Term Formal, Term? Previous)> trail = [];

    public int Mark => trail.Count;

    /// <summary>撤销标记之后的绑定。</summary>
    public void Undo(int mark)
    {
        for (var i = trail.Count - 1; i >= mark; i--)
        {
            var (formal, previous) = trail[i];
            if (previous is null) theta.Remove(formal);
            else theta[formal] = previous;
        }
        trail.RemoveRange(mark, trail.Count - mark);
        Version++;
        memo = new(ReferenceEqualityComparer.Instance);
    }

    public Dictionary<Term, Term> Snapshot() => new(theta, ReferenceEqualityComparer.Instance);

    public void Reset(IReadOnlyDictionary<Term, Term> seed)
    {
        trail.Clear();
        theta.Clear();
        foreach (var (k, v) in seed) theta[k] = v;
        Version++;
        memo = new(ReferenceEqualityComparer.Instance);
    }

    /// <summary>代入当前绑定。</summary>
    public Term Apply(Term term) => !term.HasFormal || theta.Count == 0 ? term
        : terms.Substitute(term, t => t.IsAtom(AtomKind.Formal) ? theta.GetValueOrDefault(t) : null, memo);

    // ---- 合一 ----

    /// <summary>模板一侧的项与调用方一侧的项合一：代入后相同，或未绑定的形参可以绑定成使其相同。成功时提交绑定。</summary>
    public bool Unify(Term template, Term caller)
    {
        var trial = new Dictionary<Term, Term>(ReferenceEqualityComparer.Instance);
        if (!Match(template, caller, trial)) return false;
        if (trial.Count > 0) Bind(trial);
        return true;
    }

    /// <summary>
    /// Φ 下的试探合一：比较按 Φ 的规范形，绑定取调用方未折叠的项。先按原项合一并核对两侧在 Φ 下相同；原项对不上时按折叠后的项合一，
    /// 但不接受折叠才得到的常量绑定：那个常量只在这条路径上成立，θ 却在各路径间共享。
    /// </summary>
    public bool MatchUnder(ImmutableList<Term> phi, Term template, Term caller, Dictionary<Term, Term> trial)
    {
        var plain = new Dictionary<Term, Term>(trial, ReferenceEqualityComparer.Instance);
        if (Match(template, caller, plain) && ReferenceEquals(Fold(phi, With(template, plain)), Fold(phi, caller)))
        {
            foreach (var (formal, value) in plain) trial[formal] = value;
            return true;
        }
        var folded = new Dictionary<Term, Term>(trial, ReferenceEqualityComparer.Instance);
        if (!Match(Fold(phi, template), Fold(phi, caller), folded)) return false;
        if (folded.Any(b => !trial.ContainsKey(b.Key) && b.Value.IsConstant)) return false;
        foreach (var (formal, value) in folded) trial[formal] = value;
        return true;
    }

    /// <summary>Φ 下合一，成功时提交绑定。</summary>
    public bool UnifyUnder(ImmutableList<Term> phi, Term template, Term caller)
    {
        var trial = new Dictionary<Term, Term>(ReferenceEqualityComparer.Instance);
        if (!MatchUnder(phi, template, caller, trial)) return false;
        if (trial.Count > 0) Bind(trial);
        return true;
    }

    /// <summary>代入当前绑定与试探绑定。</summary>
    private Term With(Term term, Dictionary<Term, Term> trial)
    {
        var applied = Apply(term);
        return trial.Count == 0 || !applied.HasFormal ? applied
            : terms.Substitute(applied, t => t.IsAtom(AtomKind.Formal) ? trial.GetValueOrDefault(t) : null, new(ReferenceEqualityComparer.Instance));
    }

    /// <summary>试探合一，不提交。</summary>
    public bool Match(Term template, Term caller, Dictionary<Term, Term> trial)
    {
        if (ReferenceEquals(template, caller)) return true;
        if (!template.HasFormal) return false;
        var applied = Apply(template);
        if (!applied.HasFormal) return ReferenceEquals(applied, caller);
        return MatchFree(applied, caller, trial);
    }

    private bool MatchFree(Term t, Term c, Dictionary<Term, Term> trial)
    {
        if (ReferenceEquals(t, c)) return true;
        if (!t.HasFormal) return false;
        if (t.IsAtom(AtomKind.Formal))
        {
            if (trial.TryGetValue(t, out var tried)) return ReferenceEquals(tried, c);
            if (t.Width != c.Width && !(c.Kind == TermKind.Tuple && t.Width == 0)) return false;
            if (t.Hint is { } declared && c.Hint is { } actual && !Compatible(declared, actual)) return false;
            trial[t] = c;
            return true;
        }
        // 经引用的位置：引用形参指向调用方位置的前缀。
        if (t.Kind == TermKind.Location && t.Root == RootKind.Reference && t.Args[0].IsAtom(AtomKind.Formal) && c.Kind == TermKind.Location
            && c.Root is RootKind.Field or RootKind.Static or RootKind.Element or RootKind.MultiElement or RootKind.Cell or RootKind.Reference)
        {
            var suffix = t.Path;
            var path = TermTable.PathOf(c);
            if (path.Count < suffix.Count) return false;
            for (var i = 0; i < suffix.Count; i++)
                if (!path.Fields[path.Count - suffix.Count + i].Equals(suffix.Fields[i])) return false;
            var prefix = Truncate(c, path.Count - suffix.Count);
            if (prefix is null) return false;
            return MatchFree(t.Args[0], terms.Address(prefix), trial);
        }
        if (t.Kind != c.Kind || t.Code != c.Code || t.Aux != c.Aux || t.Width != c.Width || t.Args.Length != c.Args.Length
            || !Equals(t.Key, c.Key)) return false;
        var saved = new Dictionary<Term, Term>(trial, ReferenceEqualityComparer.Instance);
        if (MatchAll(t.Args, c.Args, trial)) return true;
        // 交换律：另一种次序。
        if (t.Args.Length == 2 && Commutative(t))
        {
            trial.Clear();
            foreach (var (k, v) in saved) trial[k] = v;
            if (MatchFree(t.Args[0], c.Args[1], trial) && MatchFree(t.Args[1], c.Args[0], trial)) return true;
        }
        trial.Clear();
        foreach (var (k, v) in saved) trial[k] = v;
        return false;
    }

    /// <summary>
    /// θ 遵守类型：形参只绑定到静态类型与之相容的项。引用类型须一方可赋给另一方（同一泛型定义的不同实例按共享代码相容），
    /// 类型形参不作判断；值类型的宽度已比过。
    /// </summary>
    private bool Compatible(TypeRef declared, TypeRef actual)
    {
        if (types is null || declared.Equals(actual) || !ManagedTypes.IsReferenceType(declared) || !ManagedTypes.IsReferenceType(actual)) return true;
        if (declared is GenericParameterRef || actual is GenericParameterRef) return true;
        if (declared is DefinitionRef d && actual is DefinitionRef a && ReferenceEquals(d.Definition, a.Definition)) return true;
        return types.IsAssignable(actual, declared) || types.IsAssignable(declared, actual);
    }

    private bool MatchAll(Term[] ts, Term[] cs, Dictionary<Term, Term> trial)
    {
        for (var i = 0; i < ts.Length; i++)
        {
            var ti = ts[i];
            if (ti.HasFormal && trial.Count > 0)
                ti = terms.Substitute(ti, a => a.IsAtom(AtomKind.Formal) ? trial.GetValueOrDefault(a) : null, new(ReferenceEqualityComparer.Instance));
            if (!MatchFree(ti, cs[i], trial)) return false;
        }
        return true;
    }

    private static bool Commutative(Term t) => t.Kind == TermKind.Operation && (t.Op is OpCode.And or OpCode.Or
        || t.Op == OpCode.Binary && t.BinOp is BinOp.Add or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor or BinOp.FAdd or BinOp.FMul
        || t.Op == OpCode.Compare && t.Cond is Cond.Eq or Cond.Ne);

    /// <summary>位置去掉末尾若干字段；去到根以上时为 null。</summary>
    private Term? Truncate(Term location, int keep)
    {
        var path = TermTable.PathOf(location);
        if (keep == path.Count) return location;
        var prefix = terms.Prefix(path, keep);
        return location.Root switch
        {
            RootKind.Field when keep >= 1 => terms.FieldRoot(location.Args[0], prefix),
            RootKind.Static when keep >= 1 => terms.StaticRoot(prefix),
            RootKind.Element => terms.ElementRoot(location.Args[0], location.Args[1], prefix),
            RootKind.MultiElement => terms.MultiElementRoot(location.Args[0], location.Args.Skip(1).ToArray(), prefix),
            RootKind.Cell => terms.CellRoot(location.Aux, TermTable.CellVariable(location), prefix),
            RootKind.Reference => terms.ReferenceRoot(location.Args[0], prefix),
            _ => null,
        };
    }

    // ---- 判定 ----

    /// <summary>Φ 代入绑定后自相矛盾：某个文字为假，或由其余文字判定为假。</summary>
    public bool Infeasible(ImmutableList<Term> phi)
    {
        var applied = phi.Select(Apply).ToArray();
        var set = new HashSet<Term>(applied, ReferenceEqualityComparer.Instance);
        if (applied.Any(l => l.IsConstant && l.Bits == 0 || set.Contains(Terms.Not(l)))) return true;
        for (var i = 0; i < applied.Length; i++)
            if (Decide(ImmutableList.CreateRange(applied.Where((_, k) => k != i)), applied[i]) == false) return true;
        return false;
    }

    /// <summary>
    /// Φ 在当前绑定下的视图：已知值（x == c 的 x 取 c，其他文字取真，文字的否定取假）、文字集合，
    /// 以及按已知的常量值折叠后的文字（如已知 x == 0 时 l <= x 即 l == 0）。
    /// </summary>
    private sealed record View(Dictionary<Term, Term> Known, HashSet<Term> Literals, ImmutableList<Term> Folded);

    private (ImmutableList<Term> Phi, int Version, View View)? viewed;

    private View ViewOf(ImmutableList<Term> phi)
    {
        if (viewed is { } cached && ReferenceEquals(cached.Phi, phi) && cached.Version == Version) return cached.View;
        var known = new Dictionary<Term, Term>(ReferenceEqualityComparer.Instance);
        var values = new Dictionary<Term, Term>(ReferenceEqualityComparer.Instance);
        var applied = phi.Select(Apply).ToArray();
        foreach (var literal in applied)
        {
            if (literal.IsOp(OpCode.Compare) && literal.Cond == Cond.Eq && literal.Args[1].IsConstant)
            {
                known.TryAdd(literal.Args[0], literal.Args[1]);
                values.TryAdd(literal.Args[0], literal.Args[1]);
            }
            else if (literal.Width == 1 && !literal.IsOp(OpCode.Not) && !literal.IsConstant) known.TryAdd(literal, terms.True);
            else if (literal.IsOp(OpCode.Not)) known.TryAdd(literal.Args[0], terms.False);
        }
        var literals = new HashSet<Term>(applied, ReferenceEqualityComparer.Instance);
        // 文字按常量值折叠（定义常量值的等式本身除外）；折叠出的新文字同样成立。
        var folded = applied.ToList();
        if (values.Count > 0)
        {
            var memo = new Dictionary<Term, Term>(ReferenceEqualityComparer.Instance);
            foreach (var literal in applied)
            {
                if (literal.IsOp(OpCode.Compare) && literal.Cond == Cond.Eq && literal.Args[1].IsConstant && values.ContainsKey(literal.Args[0])) continue;
                var f = terms.ToBit(terms.Replace(literal, t => values.GetValueOrDefault(t), memo));
                if (!ReferenceEquals(f, literal) && literals.Add(f)) folded.Add(f);
            }
        }
        var view = new View(known, literals, ImmutableList.CreateRange(folded));
        viewed = (phi, Version, view);
        return view;
    }

    /// <summary>
    /// 项在 Φ 下的规范形：代入当前绑定，再把 Φ 已知等于常量的子项换成常量。两侧的值、写入与事件操作数都在共享的 Φ 下比较：
    /// 编译器按路径事实折叠过的代码（如已知 x == 0 时把 x + 1 写成 1）与未折叠的模板在这条路径上相同。
    /// </summary>
    public Term Fold(ImmutableList<Term> phi, Term term)
    {
        var applied = Apply(term);
        if (applied.IsConstant || phi.IsEmpty) return applied;
        var known = ViewOf(phi).Known;
        return known.Count == 0 ? applied : terms.Replace(applied, t => known.GetValueOrDefault(t), new(ReferenceEqualityComparer.Instance));
    }

    /// <summary>Φ 下 c 的真值；判定不出为 null。c 与按已知值代入后的 c 都同 Φ 的文字（含折叠出的文字）比较，再看非空与区间。</summary>
    public bool? Decide(ImmutableList<Term> phi, Term condition)
    {
        var c = terms.ToBit(Apply(condition));
        if (c.IsConstant) return c.Bits != 0;
        if (phi.IsEmpty) return NonNull(phi, c);
        var view = ViewOf(phi);
        if (view.Literals.Contains(c)) return true;
        if (view.Literals.Contains(terms.Not(c))) return false;
        if (NonNull(phi, c) is { } nonNull) return nonNull;
        var substituted = c;
        if (view.Known.Count > 0)
        {
            substituted = terms.ToBit(terms.Replace(c, t => view.Known.GetValueOrDefault(t), new(ReferenceEqualityComparer.Instance)));
            if (substituted.IsConstant) return substituted.Bits != 0;
            if (view.Literals.Contains(substituted)) return true;
            if (view.Literals.Contains(terms.Not(substituted))) return false;
        }
        return Interval(view.Folded, substituted) ?? (ReferenceEquals(substituted, c) ? null : Interval(view.Folded, c));
    }

    /// <summary>判空：分配得到的对象、Φ 中的 x != null。</summary>
    private bool? NonNull(ImmutableList<Term> phi, Term c)
    {
        bool? Negated(bool? b) => b is null ? null : !b;
        if (c.IsOp(OpCode.Compare) && c.Cond is Cond.Eq or Cond.Ne && c.Width == 1 && c.Args[1].IsConstant && c.Args[1].Bits == 0 && c.Args[0].Width == 64)
        {
            var x = c.Args[0];
            if (Allocations.Contains(x) || x.Kind == TermKind.Address || x.IsAtom(AtomKind.Text))
                return c.Cond == Cond.Ne;
        }
        if (c.IsOp(OpCode.Not)) return Negated(NonNull(phi, c.Args[0]));
        return null;
    }

    /// <summary>与常量比较的区间推理：Φ 中同一项与常量的比较给出上下界。</summary>
    private bool? Interval(ImmutableList<Term> phi, Term c)
    {
        if (!(c.IsOp(OpCode.Compare) && c.Args[1].IsConstant && c.Cond is Cond.Eq or Cond.Ne or Cond.Sle or Cond.Sge or Cond.Ule or Cond.Uge)) return null;
        var x = c.Args[0];
        var w = x.Width;
        if (w is <= 0 or > 64) return null;
        // 有符号与无符号的区间分别收紧。
        long slo = w >= 64 ? long.MinValue : -(1L << (w - 1)), shi = w >= 64 ? long.MaxValue : (1L << (w - 1)) - 1;
        ulong ulo = 0, uhi = TermTable.Mask(w);
        var excluded = new HashSet<ulong>();
        var any = false;
        foreach (var raw in phi)
        {
            var literal = Apply(raw);
            if (!literal.IsOp(OpCode.Compare) || !ReferenceEquals(literal.Args[0], x) || !literal.Args[1].IsConstant) continue;
            var k = literal.Args[1].Bits;
            var sk = Signed(k, w);
            any = true;
            switch (literal.Cond)
            {
                case Cond.Eq: slo = Math.Max(slo, sk); shi = Math.Min(shi, sk); ulo = Math.Max(ulo, k); uhi = Math.Min(uhi, k); break;
                case Cond.Ne: excluded.Add(k); break;
                case Cond.Sle: shi = Math.Min(shi, sk); break;
                case Cond.Sge: slo = Math.Max(slo, sk); break;
                case Cond.Ule: uhi = Math.Min(uhi, k); break;
                case Cond.Uge: ulo = Math.Max(ulo, k); break;
            }
        }
        if (!any) return null;
        // 有符号区间不跨零时也是无符号区间。
        if (slo >= 0) { ulo = Math.Max(ulo, (ulong)slo); uhi = Math.Min(uhi, (ulong)shi); }
        if (uhi <= TermTable.Mask(w) >> 1) { slo = Math.Max(slo, (long)ulo); shi = Math.Min(shi, (long)uhi); }
        var q = c.Args[1].Bits;
        var sq = Signed(q, w);
        return c.Cond switch
        {
            Cond.Eq => sq < slo || sq > shi || q < ulo || q > uhi || excluded.Contains(q) ? false : slo == shi && slo == sq ? true : null,
            Cond.Ne => sq < slo || sq > shi || q < ulo || q > uhi || excluded.Contains(q) ? true : slo == shi && slo == sq ? false : null,
            Cond.Sle => shi <= sq ? true : slo > sq ? false : null,
            Cond.Sge => slo >= sq ? true : shi < sq ? false : null,
            Cond.Ule => uhi <= q ? true : ulo > q ? false : null,
            Cond.Uge => ulo >= q ? true : uhi < q ? false : null,
            _ => null,
        };
    }

    private static long Signed(ulong bits, int width) => width >= 64 ? (long)bits : (long)(bits << (64 - width)) >> (64 - width);
}
