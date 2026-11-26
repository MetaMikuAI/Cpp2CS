using System.Collections.Immutable;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Kernel.Engine;

/// <summary>内核自用的属性项的编号。规格登记的具名函数用 RuntimeFunction 的值，都小于 1000。</summary>
public static class KernelAttributes
{
    /// <summary>堆上的读取：操作数是地址与历元；位宽是读取的位宽。</summary>
    public const int Load = 1000;
    /// <summary>本侧自上一个事件以来有一次可能重叠的写入之后的读取：操作数是地址、历元、哪一侧、第几次写入之后。</summary>
    public const int LoadAfter = 1001;
    /// <summary>一次事件的结果：操作数是事件的序号与结果槽的序号。</summary>
    public const int EventResult = 1002;
    /// <summary>帧里没有写过的位置上的读取：操作数是相对入口栈指针的偏移、帧的代次、哪一个帧（0 是现场，其余是第几次展开）。</summary>
    public const int FrameWord = 1003;
    /// <summary>映像数据区里的一个字：操作数是地址、历元与序号。</summary>
    public const int ImageWord = 1004;
    /// <summary>运行时构造的异常对象：操作数是异常的种类与事件的序号。</summary>
    public const int ExceptionObject = 1007;
    /// <summary>被展开的方法入口处没有由实参给出的槽位：操作数是第几次展开、槽位的种类与序号。</summary>
    public const int InnerEntry = 1006;
}

/// <summary>
/// 路径条件格（设计 7.7）：沿路径成立的文字，以及在它们之下对条件与项的求值。全系统只有这一处判断
/// “这组条件能否同时成立”“这个条件在此处取什么值”。不可变；加入一条文字得到新的格，矛盾时得到空。
/// 判断是保守的：回答“不能判定”总是允许的。
/// </summary>
public sealed class PathConditions
{
    private readonly TermPool terms;
    private readonly ImmutableDictionary<Term, bool> literals;
    private readonly ImmutableDictionary<Term, Term> constants;
    private readonly ImmutableHashSet<EntityRef> initialized;
    private readonly ImmutableDictionary<Term, int> immutable;
    /// <summary>区间：项按无符号数不超过的上界（含）。来自规格登记的取值范围，以及成立的无符号比较。</summary>
    private readonly ImmutableDictionary<Term, UInt128> upper;

    private PathConditions(TermPool terms, ImmutableDictionary<Term, bool> literals, ImmutableDictionary<Term, Term> constants,
        ImmutableHashSet<EntityRef> initialized, ImmutableDictionary<Term, int> immutable, ImmutableDictionary<Term, UInt128>? upper = null)
    {
        this.terms = terms;
        this.literals = literals;
        this.constants = constants;
        this.initialized = initialized;
        this.immutable = immutable;
        this.upper = upper ?? ImmutableDictionary<Term, UInt128>.Empty;
    }

    public static PathConditions Empty(TermPool terms) => new(terms, ImmutableDictionary<Term, bool>.Empty,
        ImmutableDictionary<Term, Term>.Empty, [], ImmutableDictionary<Term, int>.Empty);

    /// <summary>登记一个取值范围：项按无符号数不超过 maximum。</summary>
    public PathConditions WithUpperBound(Term term, UInt128 maximum) =>
        upper.TryGetValue(term, out var known) && known <= maximum ? this
            : new(terms, literals, constants, initialized, immutable, upper.SetItem(term, maximum));

    private UInt128? UpperBound(Term term) =>
        term.IsConstant ? term.Value : upper.TryGetValue(term, out var bound) ? bound : null;

    /// <summary>成立的文字，供诊断。</summary>
    public IEnumerable<string> Describe() => literals.Select(l => $"{l.Key} = {(l.Value ? 1 : 0)}");

    /// <summary>某个类的初始化已触发。</summary>
    public bool Initialized(EntityRef type) => initialized.Contains(type);
    public PathConditions WithInitialized(EntityRef type) => new(terms, literals, constants, initialized.Add(type), immutable, upper);

    /// <summary>登记一个运行时不可变的位置：它上面的读取与历元无关。</summary>
    public PathConditions WithImmutable(Term address, int width)
    {
        if (immutable.GetValueOrDefault(address) >= width) return this;
        var fields = immutable.SetItem(address, width);
        // 用读取身份重建键。若用旧键上的等式化简其自身，读数等于零的文字会被化成真而丢失。
        var canonical = new PathConditions(terms, ImmutableDictionary<Term, bool>.Empty, ImmutableDictionary<Term, Term>.Empty,
            initialized, fields);
        var rekeyed = ImmutableDictionary<Term, bool>.Empty.ToBuilder();
        foreach (var (literal, truth) in literals)
        {
            bool value = truth;
            var now = Strip(canonical.Evaluate(literal), ref value);
            if (!now.IsConstant) rekeyed[now] = value;
        }
        var values = ImmutableDictionary<Term, Term>.Empty.ToBuilder();
        foreach (var (term, constant) in constants) values[canonical.Evaluate(term)] = constant;
        var bounds = ImmutableDictionary<Term, UInt128>.Empty.ToBuilder();
        foreach (var (term, maximum) in upper)
        {
            var key = canonical.Evaluate(term);
            if (!bounds.TryGetValue(key, out var bound) || maximum < bound) bounds[key] = maximum;
        }
        return new PathConditions(terms, rekeyed.ToImmutable(), values.ToImmutable(), initialized, fields, bounds.ToImmutable());
    }

    /// <summary>从同一地址开始的读取是否完全落在已登记的不可变字内。</summary>
    public bool IsImmutable(Term address, int width) => immutable.GetValueOrDefault(Evaluate(address)) >= width;

    /// <summary>在成立的文字之下求值：已定的条件换成常量，已知等于常量的项换成常量，不可变位置上的读取去掉历元。</summary>
    public Term Evaluate(Term term) => Evaluate(term, literals);

    private Term Evaluate(Term term, ImmutableDictionary<Term, bool> known)
    {
        var memo = new Dictionary<Term, Term>(ReferenceEqualityComparer.Instance);
        Term Known(Term t)
        {
            if (t.Width == 1 && known.TryGetValue(t, out bool value)) return value ? terms.True : terms.False;
            if (constants.TryGetValue(t, out var constant)) return constant;
            // 选择项与常量相等，当且仅当选中臂与该常量相等。il2cpp-codegen-il2cpp.h 的 IsInstClass 两臂分别返回对象和空。
            if (t.Kind == TermKind.Operation && t.Op == Op.Eq && t.Operands[0] is { Kind: TermKind.Select } choice && t.Operands[1].IsConstant)
                return terms.Select(choice.Operands[0], terms.Eq(choice.Operands[1], t.Operands[1]), terms.Eq(choice.Operands[2], t.Operands[1]));
            // ARM64 小端上，同址窄读取存储字的低位。Il2CppArray::max_length 由 IL2CPP_ARRAY_BOUNDS_CHECK 转为 uint32_t。
            // 只统一已登记的不可变字，跨历元或可能重叠的写入后仍是同一读取（设计 7.4）。
            if (t.Kind == TermKind.Attribute && t.Attribute.Value is KernelAttributes.Load or KernelAttributes.LoadAfter
                && immutable.TryGetValue(t.Operands[0], out int width) && t.Width <= width)
            {
                var word = terms.Attribute(new AttributeId(KernelAttributes.Load), width, t.Operands[0], terms.Zero(32));
                return terms.Slice(word, 0, t.Width);
            }
            // 规格登记的等式：登记的操作数为零时，具名函数的结果为零。
            if (t.Kind == TermKind.Attribute)
                foreach (var (function, operand) in Cpp2CS.Spec.Runtime.RuntimeEquations.ZeroPreserving)
                    if (t.Attribute.Value == (int)function && t.Operands[operand].IsZero) return terms.Zero(t.Width);
            // 区间判定：最高位已知为 0 的值，符号扩展就是零扩展。
            if (t.Kind == TermKind.Operation && t.Op == Op.SignExtend && t.Operands[0].Width <= 128
                && Bounded(t.Operands[0]) is { } bound && bound < UInt128.One << (t.Operands[0].Width - 1))
                return terms.ZeroExtend(t.Operands[0], t.Width);
            // 除数已知非零时，余数按定义写成 被除数 − 商 × 除数；两种写法由此归一。
            if (t.Kind == TermKind.Operation && t.Op is Op.SRem or Op.URem && Nonzero(t.Operands[1]))
                return terms.Sub(t.Operands[0], terms.Mul(terms.Divide(t.Op == Op.SRem ? Op.SDiv : Op.UDiv, t.Operands[0], t.Operands[1]), t.Operands[1]));
            return t;
        }
        // 上界：登记的取值范围，或一条成立的无符号比较（x < y，或 非(y < x)）给出的界。
        UInt128? Bounded(Term x)
        {
            if (UpperBound(x) is { } direct) return direct;
            foreach (var (literal, truth) in literals)
            {
                if (literal.Kind != TermKind.Operation || literal.Op != Op.Ult) continue;
                if (truth && ReferenceEquals(literal.Operands[0], x) && UpperBound(literal.Operands[1]) is { } limit && limit > 0) return limit - 1;
                if (!truth && ReferenceEquals(literal.Operands[1], x) && UpperBound(literal.Operands[0]) is { } most) return most;
            }
            return null;
        }
        bool Nonzero(Term t) =>
            t.Width <= 128 && (t.IsConstant ? !t.IsZero : known.TryGetValue(terms.Eq(t, terms.Zero(t.Width)), out bool zero) && !zero);
        Term Go(Term t)
        {
            if (memo.TryGetValue(t, out var done)) return done;
            Term result = Known(t);
            if (ReferenceEquals(result, t) && t.Operands.Length > 0)
            {
                var parts = new Term[t.Operands.Length];
                bool changed = false;
                for (int i = 0; i < parts.Length; i++)
                {
                    parts[i] = Go(t.Operands[i]);
                    changed |= !ReferenceEquals(parts[i], t.Operands[i]);
                }
                if (changed) result = Known(terms.Rebuild(t, parts));
            }
            else if (!ReferenceEquals(result, t) && result.Operands.Length > 0) result = Go(result);
            memo[t] = result;
            return result;
        }
        return Go(term);
    }

    private static Term Strip(Term condition, ref bool value)
    {
        while (condition.Kind == TermKind.Operation && condition.Op == Op.Not) { condition = condition.Operands[0]; value = !value; }
        return condition;
    }

    /// <summary>条件在此处的取值：真、假，或不能判定（空）。</summary>
    public bool? Decide(Term condition)
    {
        if (condition.Width != 1) throw new ArgumentException("条件须为 1 位");
        bool positive = true;
        var c = Strip(Evaluate(condition), ref positive);
        if (c.IsConstant) return c.IsZero != positive;
        if (c.Kind == TermKind.Operation && c.Op is Op.And or Op.Or)
        {
            bool? x = Decide(c.Operands[0]), y = Decide(c.Operands[1]);
            bool absorbing = c.Op == Op.Or;
            if (x == absorbing || y == absorbing) return absorbing == positive;
            if (x == !absorbing && y == !absorbing) return !absorbing == positive;
        }
        return null;
    }

    /// <summary>加入一条文字：条件取 value。与已有的文字矛盾时返回空。</summary>
    public PathConditions? With(Term condition, bool value)
    {
        if (condition.Width != 1) throw new ArgumentException("条件须为 1 位");
        var c = Strip(Evaluate(condition), ref value);
        if (c.IsConstant) return c.IsZero != value ? this : null;
        // 合取为真、析取为假：拆成各自的文字。
        if (c.Kind == TermKind.Operation && ((c.Op == Op.And && value) || (c.Op == Op.Or && !value)))
            return With(c.Operands[0], value)?.With(c.Operands[1], value);
        var nextLiterals = literals.SetItem(c, value);
        var nextConstants = constants;
        if (value && c.Kind == TermKind.Operation && c.Op == Op.Eq && c.Operands[1].IsConstant && !c.Operands[0].IsConstant)
            nextConstants = constants.SetItem(c.Operands[0], c.Operands[1]);
        var nextUpper = upper;
        var next = new PathConditions(terms, nextLiterals, nextConstants, initialized, immutable, nextUpper);
        if (ReferenceEquals(nextConstants, constants)) return next;
        // 新的等式可能使已有的文字成为常量：与原取值不符就是矛盾。
        var settled = ImmutableDictionary<Term, bool>.Empty.ToBuilder();
        foreach (var (literal, truth) in nextLiterals)
        {
            if (ReferenceEquals(literal, c)) { settled[literal] = truth; continue; }
            bool expected = truth;
            var now = Strip(next.Evaluate(literal, ImmutableDictionary<Term, bool>.Empty), ref expected);
            if (now.IsConstant) { if (now.IsZero == expected) return null; }
            else settled[now] = expected;
        }
        return new PathConditions(terms, settled.ToImmutable(), nextConstants, initialized, immutable, nextUpper);
    }

    /// <summary>值判定（设计 7.8）在路径条件下的部分：两个项在此处是否同值。只回答“已证明相同”或“不能证明”。</summary>
    public bool Same(Term a, Term b)
    {
        if (a.Width != b.Width) return false;
        Term x = Evaluate(a), y = Evaluate(b);
        if (ReferenceEquals(x, y)) return true;
        return x.Width <= 128 && (SameLinear(x, y) || Decide(terms.Eq(x, y)) == true);
    }

    /// <summary>
    /// 线性范式：两个项各写成“原子乘常数之和加常数”（按位宽回绕），逐项相消后为零就是同值。
    /// 左移常数位写成乘以 2 的幂；原子是不能再拆的项。
    /// </summary>
    private bool SameLinear(Term x, Term y)
    {
        int width = x.Width;
        UInt128 mask = width >= 128 ? UInt128.MaxValue : (UInt128.One << width) - 1, constant = 0;
        var sum = new Dictionary<Term, UInt128>(ReferenceEqualityComparer.Instance);
        void Add(Term t, UInt128 factor)
        {
            if (t.IsConstant) { constant += factor * t.Value; return; }
            if (t.Kind == TermKind.Operation)
                switch (t.Op)
                {
                    case Op.Add: Add(t.Operands[0], factor); Add(t.Operands[1], factor); return;
                    case Op.Sub: Add(t.Operands[0], factor); Add(t.Operands[1], UInt128.Zero - factor); return;
                    case Op.Neg: Add(t.Operands[0], UInt128.Zero - factor); return;
                    case Op.Mul when t.Operands[1].IsConstant: Add(t.Operands[0], factor * t.Operands[1].Value); return;
                }
            // 低位补零：原值左移，即乘以 2 的幂。
            if (t.Kind == TermKind.Concat && t.Operands.Length == 2 && t.Operands[0].IsZero
                && t.Operands[1] is { Kind: TermKind.Slice, Offset: 0 } low && low.Operands[0].Width >= width)
            {
                Add(terms.Slice(low.Operands[0], 0, width), factor << t.Operands[0].Width);
                return;
            }
            sum[t] = sum.GetValueOrDefault(t) + factor;
        }
        Add(x, UInt128.One);
        Add(y, UInt128.MaxValue);
        if ((constant & mask) != 0) return false;
        foreach (var coefficient in sum.Values)
            if ((coefficient & mask) != 0) return false;
        return true;
    }
}
