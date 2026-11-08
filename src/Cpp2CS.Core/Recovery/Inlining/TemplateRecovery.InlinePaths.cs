using Cpp2CS.Ir;
using Cpp2CS.Recovery.Effects;

namespace Cpp2CS.Recovery.Inlining;

internal sealed partial class TemplateRecovery
{
    /// <summary>区域里没有调用、检查和写入时还原的调用：不改变内存，路径事实可以跨过它。</summary>
    private readonly HashSet<ManagedStatement> pureInlines = new(ReferenceEqualityComparer.Instance);

    /// <summary>沿唯一前驱链收集入口条件与已保存的读取；写入使可能别名的读取失效，调用截断链。</summary>
    private void SeedPath(Walker caller)
    {
        var chain = new List<ManagedBlock>();
        var seen = new HashSet<ulong> { caller.Block };
        var at = caller.Block;
        bool Trackable(ManagedStatement statement) => statement is ManagedJump or ManagedBranch or ManagedCheck || pureInlines.Contains(statement)
            || (statement is ManagedAssignment or ManagedStore { Target: FieldValue or StaticFieldValue or ArrayElementValue })
            && !ManagedValues.Of(statement).SelectMany(ManagedValues.Walk).Any(v => v is NewObjectValue or NewArrayValue or BoxValue or DelegateValue or HoleValue);
        if (caller.Blocks[at].Statements.Take(caller.Index).Any(s => !Trackable(s))) return;
        while (chain.Count < 16)
        {
            if (Predecessors(caller.Blocks, at) is not [var predecessor] || !seen.Add(predecessor.Address) || predecessor.Statements.Any(s => !Trackable(s))) break;
            chain.Add(predecessor);
            at = predecessor.Address;
        }
        chain.Reverse();
        var walker = new Walker { Blocks = caller.Blocks, Caller = true, Block = at, Index = 0 };
        foreach (var block in chain.Append(caller.Blocks[caller.Block]))
        {
            var statements = block.Address == caller.Block ? block.Statements.Take(caller.Index) : block.Statements;
            foreach (var statement in statements)
            {
                if (statement is ManagedStore store && Location(walker, store.Target) is { } location)
                {
                    foreach (var variable in walker.Env.Where(p => ReadsLocation(p.Value, location)).Select(p => p.Key).ToArray()) walker.Env.Remove(variable);
                    caller.Assumptions.RemoveAll(p => ReadsLocation(p.Condition, location));
                }
                NoteAccesses(walker, statement);
                if (statement is ManagedCall { Result: { } returned }) walker.Env.Remove(returned.Variable);
                if (statement is ManagedAssignment assignment && Term(walker, assignment.Value) is { } value) walker.Env[assignment.Target.Variable] = value;
                if (statement is ManagedCheck check && Term(walker, check.Condition) is { } passed) caller.Assumptions.Add((passed, false));
                ManagedEdge? edge = null;
                if (statement is ManagedJump jump) edge = jump.Edge;
                if (statement is ManagedBranch branch)
                {
                    var next = chain.SkipWhile(b => b.Address != block.Address).Skip(1).FirstOrDefault()?.Address ?? caller.Block;
                    if ((branch.Taken.Target == next) == (branch.Fallthrough.Target == next)) continue;
                    var taken = branch.Taken.Target == next;
                    if (Term(walker, branch.Condition) is { } condition) caller.Assumptions.Add((condition, taken));
                    edge = taken ? branch.Taken : branch.Fallthrough;
                }
                if (edge is null) continue;
                var copied = edge.Copies.Select(c => (c.Target.Variable, Value: Term(walker, c.Value))).ToArray();
                foreach (var (variable, copiedValue) in copied)
                    if (copiedValue is not null) walker.Env[variable] = copiedValue;
            }
        }
        foreach (var (variable, value) in walker.Env) caller.Env[variable] = value;
        caller.Dereferenced.UnionWith(walker.Dereferenced);
    }

    private static ManagedValue Bind(ManagedValue value, IReadOnlyDictionary<int, ManagedValue> binding) => value switch
    {
        ArgumentValue argument when binding.TryGetValue(argument.Index, out var bound) => bound,
        _ => MapTerm(value, child => Bind(child, binding)),
    };

    /// <summary>路径事实给出的常量：条件 x == k 成立或 x != k 不成立时，x 就是 k。</summary>
    private ConstantValue? KnownValue(ManagedValue term, Walker caller)
    {
        foreach (var (condition, truth) in caller.Assumptions)
        {
            if (condition is not ComparisonValue { Condition: Cond.Eq or Cond.Ne, Right: ConstantValue constant } equality
                || (equality.Condition == Cond.Eq) != truth || !SameTerm(equality.Left, term)) continue;
            return constant with { Type = term.Type, Width = term.Width };
        }
        return null;
    }

    /// <summary>
    /// 调用方已知某个读取的值时，内联后的代码按这个值折叠（如判过 Count == 0 之后的 Add）。把读取换成常量，两边才能比较。
    /// 模板的项先代入已绑定的形参再查事实。
    /// </summary>
    private ManagedValue Specialize(ManagedValue term, Walker caller, IReadOnlyDictionary<int, ManagedValue> binding)
    {
        if (caller.Assumptions.Count == 0) return term;
        ManagedValue Visit(ManagedValue value) => value is Observed && KnownValue(Bind(value, binding), caller) is { } known ? known : MapTerm(value, Visit);
        return Visit(term);
    }

    /// <summary>折叠常量，并把无符号数与 0、1 的边界比较统一写成判零：clang 折叠掉一侧常量后常换成这种写法。</summary>
    private ManagedValue Fold(ManagedValue value)
    {
        var mapped = MapTerm(value, Fold);
        ComparisonValue IsZero(ComparisonValue c, ManagedValue operand, Cond condition) =>
            c with { Condition = condition, Left = operand, Right = new ConstantValue(0, operand.Type, operand.Width) };
        return mapped switch
        {
            BinaryValue { Op: BinOp.Add, Left: ConstantValue a, Right: ConstantValue b } add => new ConstantValue((a.Bits + b.Bits) & Expr.Mask(add.Width), add.Type, add.Width),
            // 同宽的模加可以结合：(x + a) + b = x + (a + b)。
            BinaryValue { Op: BinOp.Add, Left: BinaryValue { Op: BinOp.Add, Right: ConstantValue a } inner, Right: ConstantValue b } add when inner.Width == add.Width
                => Fold(add with { Left = inner.Left, Right = new ConstantValue((a.Bits + b.Bits) & Expr.Mask(add.Width), b.Type, add.Width) }),
            BinaryValue { Op: BinOp.Add, Left: var left, Right: ConstantValue { Bits: 0 } } => left,
            BinaryValue { Op: BinOp.Add, Left: ConstantValue { Bits: 0 }, Right: var right } => right,
            ComparisonValue { Left: ConstantValue a, Right: ConstantValue b } c when ConstantComparison(c.Condition, a, b) is { } truth
                => new ConstantValue(truth ? 1UL : 0UL, types.Boolean, 8),
            NegatedValue { Operand: ConstantValue operand } => new ConstantValue(operand.Bits == 0 ? 1UL : 0UL, types.Boolean, 8),
            ChoiceValue { Condition: ConstantValue known } choice => known.Bits != 0 ? choice.True : choice.False,
            ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.Truncate, Operand: ConstantValue operand } conversion
                => new ConstantValue(operand.Bits & Expr.Mask(conversion.Width), conversion.Type, conversion.Width),
            ComparisonValue { Condition: Cond.Ule, Right: ConstantValue { Bits: 0 }, Left: var x } c => IsZero(c, x, Cond.Eq),
            ComparisonValue { Condition: Cond.Uge, Left: ConstantValue { Bits: 0 }, Right: var x } c => IsZero(c, x, Cond.Eq),
            ComparisonValue { Condition: Cond.Ult, Right: ConstantValue { Bits: 1 }, Left: var x } c => IsZero(c, x, Cond.Eq),
            ComparisonValue { Condition: Cond.Ugt, Left: ConstantValue { Bits: 1 }, Right: var x } c => IsZero(c, x, Cond.Eq),
            ComparisonValue { Condition: Cond.Ugt, Right: ConstantValue { Bits: 0 }, Left: var x } c => IsZero(c, x, Cond.Ne),
            ComparisonValue { Condition: Cond.Ult, Left: ConstantValue { Bits: 0 }, Right: var x } c => IsZero(c, x, Cond.Ne),
            ComparisonValue { Condition: Cond.Uge, Right: ConstantValue { Bits: 1 }, Left: var x } c => IsZero(c, x, Cond.Ne),
            ComparisonValue { Condition: Cond.Ule, Left: ConstantValue { Bits: 1 }, Right: var x } c => IsZero(c, x, Cond.Ne),
            ComposedValue composed when Whole(composed) is { } whole => whole,
            _ => mapped,
        };
    }

    /// <summary>
    /// 按叶子组成的结构体值，各叶子恰是同一结构体值的对应叶子时，就是这个值（模板逐字段读出再组成，调用方整体复制）。
    /// 叶子是同一代对堆、静态或间接位置的读取，或对同一代整体读取的投影。
    /// </summary>
    private ManagedValue? Whole(ComposedValue composed)
    {
        if (composed.StructType is not DefinitionRef structure || composed.Leaves.Count == 0) return null;
        var expected = types.Leaves(structure).Select(l => l.Path).ToArray();
        if (expected.Length != composed.Leaves.Count) return null;
        ManagedValue? whole = null;
        for (var i = 0; i < expected.Length; i++)
        {
            var (path, value) = composed.Leaves[i];
            if (!path.SequenceEqual(expected[i]) || value is not Observed { Read: var read, Epoch: var epoch }) return null;
            for (var k = path.Count - 1; k >= 0; k--)
            {
                if (read is not FieldValue field || !field.Field.Equals(path[k])) return null;
                read = field.Receiver;
            }
            ManagedValue? source = read switch
            {
                Observed observed when observed.Epoch == epoch => observed,
                FieldValue or StaticFieldValue or ArrayElementValue or IndirectValue => new Observed(read, epoch),
                _ => null,
            };
            if (source is null || !source.Type.Equals(structure) || whole is not null && !whole.Equals(source)) return null;
            whole = source;
        }
        return whole;
    }

    private bool? KnownCondition(ManagedValue condition, Walker caller, IReadOnlyDictionary<int, ManagedValue> binding)
    {
        var instantiated = Fold(Specialize(Bind(condition, binding), caller, NoBinding));
        if (instantiated is ConstantValue truth) return truth.Bits != 0;
        if (instantiated is ComparisonValue { Left: ConstantValue left, Right: ConstantValue right } comparison)
            return ConstantComparison(comparison.Condition, left, right);
        // 解引用过的项不为空。
        if (instantiated is ComparisonValue { Condition: Cond.Eq or Cond.Ne, Right: ConstantValue { Bits: 0 }, Left: var tested } nullTest && caller.Dereferenced.Contains(tested))
            return nullTest.Condition == Cond.Ne;
        var canonical = Canonical(instantiated);
        foreach (var assumption in caller.Assumptions)
        {
            if (SameTerm(canonical, Canonical(assumption.Condition))) return assumption.Value;
            if (SameTerm(canonical, Canonical(Negate(assumption.Condition)))) return !assumption.Value;
        }
        return RangeCondition(instantiated, caller);
    }

    /// <summary>
    /// 同一项与常量的比较按值域判定：路径上关于这一项的比较合成有符号区间和排除的值（如 x != 1 且 x &lt;= 1 得 x &lt;= 0）。
    /// clang 按同样的值域删掉内联代码里已经确定的分支。无符号的上界在常量非负时折成区间，其余无符号事实不用；矛盾的路径不判定。
    /// </summary>
    private bool? RangeCondition(ManagedValue condition, Walker caller)
    {
        if (Bound(condition) is not var (term, query, constant)) return null;
        var width = term.Width;
        if (width is not (8 or 16 or 32 or 64)) return null;
        var (min, max) = (-(1L << (width - 1)), (long)((1UL << (width - 1)) - 1));
        var (lo, hi) = (min, max);
        var excluded = new HashSet<long>();
        var facts = 0;
        foreach (var (assumed, truth) in caller.Assumptions)
        {
            if (Bound(Fold(assumed)) is not var (other, op, value) || !SameTerm(other, term)) continue;
            if (!truth && Negated(op) is { } negated) op = negated;
            else if (!truth) continue;
            var v = Signed(value, width);
            var unsigned = value & Expr.Mask(width);
            facts++;
            switch (op)
            {
                case Cond.Eq: lo = Math.Max(lo, v); hi = Math.Min(hi, v); break;
                case Cond.Ne: excluded.Add(v); break;
                case Cond.Slt: if (v == min) return null; hi = Math.Min(hi, v - 1); break;
                case Cond.Sle: hi = Math.Min(hi, v); break;
                case Cond.Sgt: if (v == max) return null; lo = Math.Max(lo, v + 1); break;
                case Cond.Sge: lo = Math.Max(lo, v); break;
                case Cond.Ult when unsigned is > 0 && unsigned <= (ulong)max + 1: lo = Math.Max(lo, 0); hi = Math.Min(hi, (long)unsigned - 1); break;
                case Cond.Ule when unsigned <= (ulong)max: lo = Math.Max(lo, 0); hi = Math.Min(hi, (long)unsigned); break;
                default: facts--; break;
            }
        }
        if (facts == 0) return null;
        while (lo <= hi && excluded.Contains(lo)) lo++;
        while (lo <= hi && excluded.Contains(hi)) hi--;
        if (lo > hi) return null;
        var k = Signed(constant, width);
        var ku = constant & Expr.Mask(width);
        if (query is Cond.Ult or Cond.Ule or Cond.Ugt or Cond.Uge)
        {
            // 区间非负时无符号次序与有符号相同；常量超过有符号上界时，非负的项都比它小。
            if (lo < 0) return null;
            if (ku > (ulong)max) return query is Cond.Ult or Cond.Ule;
            query = query switch { Cond.Ult => Cond.Slt, Cond.Ule => Cond.Sle, Cond.Ugt => Cond.Sgt, _ => Cond.Sge };
            k = (long)ku;
        }
        return query switch
        {
            Cond.Eq => lo == hi && lo == k ? true : k < lo || k > hi || excluded.Contains(k) ? false : null,
            Cond.Ne => lo == hi && lo == k ? false : k < lo || k > hi || excluded.Contains(k) ? true : null,
            Cond.Slt => hi < k ? true : lo >= k ? false : null,
            Cond.Sle => hi <= k ? true : lo > k ? false : null,
            Cond.Sgt => lo > k ? true : hi <= k ? false : null,
            Cond.Sge => lo >= k ? true : hi < k ? false : null,
            _ => null,
        };

        static long Signed(ulong bits, int width) => width == 64 ? (long)bits : (long)(bits << (64 - width)) >> (64 - width);
    }

    /// <summary>项与常量的整数比较，常量在左侧时换到右侧。</summary>
    private static (ManagedValue Term, Cond Condition, ulong Constant)? Bound(ManagedValue condition) => condition switch
    {
        ComparisonValue { Condition: > Cond.Uge } => null,
        ComparisonValue { Left: ConstantValue, Right: ConstantValue } => null,
        ComparisonValue { Right: ConstantValue right } c => (c.Left, c.Condition, right.Bits),
        ComparisonValue { Left: ConstantValue left } c => (c.Right, Swapped(c.Condition), left.Bits),
        _ => null,
    };

    private static Cond Swapped(Cond condition) => condition switch
    {
        Cond.Slt => Cond.Sgt, Cond.Sle => Cond.Sge, Cond.Sgt => Cond.Slt, Cond.Sge => Cond.Sle,
        Cond.Ult => Cond.Ugt, Cond.Ule => Cond.Uge, Cond.Ugt => Cond.Ult, Cond.Uge => Cond.Ule,
        _ => condition,
    };

    /// <summary>解引用项的语句访问：读取或写入字段、数组元素和数组长度。</summary>
    private void NoteAccesses(Walker walker, ManagedStatement statement)
    {
        foreach (var value in ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).SelectMany(ManagedValues.Walk))
            if (Accessed(value) is { } receiver && Term(walker, receiver) is { } term) walker.Dereferenced.Add(term);
    }

    private static ManagedValue? Accessed(ManagedValue value) => value switch
    {
        FieldValue { Receiver: var receiver } when ManagedTypes.IsReferenceType(receiver.Type) => receiver,
        ArrayLengthValue array => array.Array,
        ArrayElementValue element => element.Array,
        _ => null,
    };

    private bool NonNull(Walker caller, ManagedValue receiver)
    {
        if (Term(caller, receiver) is not { } term) return false;
        return caller.Dereferenced.Contains(term) || KnownCondition(new ComparisonValue(Cond.Eq, term, new ConstantValue(0, term.Type, term.Width), types.Boolean), caller, NoBinding) == false;
    }

    /// <summary>
    /// 语句在这条路径上可能抛出：调用、检查与抛出总是；字段、长度和元素访问只有在接收者可能为空或下标可能越界时才是。
    /// 判过边界的元素访问、已解引用对象上的字段访问不会抛出，也就不受 try 边界约束（原生调用点表不覆盖这些语句）。
    /// </summary>
    private bool Raises(Walker caller, ManagedStatement statement)
    {
        if (statement is not (ManagedJump or ManagedBranch or ManagedReturn or ManagedAssignment or ManagedStore)) return true;
        EffectSummary? Evidence(ManagedValue value) => value switch
        {
            FieldValue { Accessor: null } field when ManagedTypes.IsReferenceType(field.Receiver.Type) && NonNull(caller, field.Receiver)
                => ManagedEffects.Value(field.Receiver, Evidence),
            ArrayLengthValue length when NonNull(caller, length.Array) => ManagedEffects.Value(length.Array, Evidence),
            ArrayElementValue element when NonNull(caller, element.Array) && Term(caller, element.Index) is { } index && Term(caller, element.Array) is { } array
                && KnownCondition(new ComparisonValue(Cond.Uge, index, new ArrayLengthValue(array, index.Type, index.Width), types.Boolean), caller, NoBinding) == false
                => ManagedEffects.Value(element.Array, Evidence) | ManagedEffects.Value(element.Index, Evidence),
            _ => null,
        };
        return ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).Any(v => ManagedEffects.Value(v, Evidence).MayThrow);
    }
}
