using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Analysis;

namespace Cpp2CS.Recovery;

/// <summary>
/// 只用于 C# 输出的整理（执行对照仍用原方法体）。每条规则在 C# 语义下等价：
/// 1. 删去 RuntimeHelpers.RunClassConstructor（C# 访问静态成员时自动初始化类型）；
/// 2. 删去紧接着解引用同一对象的显式判空（C# 的成员访问本身对 null 抛 NullReferenceException）；
/// 3. 位宽往返（截断回原位宽的零/符号扩展）与 bool 的 ?1:0、&amp;1 还原；只在截断中使用的扩展副本内联到使用处；
/// 4. 只赋值一次、不取地址的局部变量之间的复制传播；删去结果不再使用的无副作用赋值。
/// </summary>
public static class SourceRewriter
{
    public static ManagedBody Rewrite(ManagedBody body, ManagedTypes types, Func<MethodRef, bool>? fieldGetter = null,
        Action<IterationResult<ManagedBody>>? iteration = null, Action<Cpp2CS.Structure.SourcePass>? trace = null)
    {
        var original = body;
        void Apply(string rule, Func<ManagedBody, ManagedBody> transform)
        {
            var before = body;
            var started = System.Diagnostics.Stopwatch.GetTimestamp();
            body = transform(before);
            if (trace is not null) trace(new(rule, !ManagedStructure.Same(before, body),
                before.Blocks.Sum(b => b.Statements.Count), body.Blocks.Sum(b => b.Statements.Count),
                System.Diagnostics.Stopwatch.GetElapsedTime(started).TotalMilliseconds));
        }
        Apply("source.normalize", Normalize);
        Apply("source.struct-copies", SourceStructCopies.Rewrite);
        Apply("source.typed-catches", TypedCatches);
        Apply("source.cached-delegates", CachedDelegates);
        Apply("source.values", b => Map(b, v => Simplify(v, types)));
        Apply("source.array-lengths", b => FreshArrayLengths(b, types));
        Apply("source.drop-checks", DropStatements);
        Apply("source.checked-casts", SourceCheckedCasts.Rewrite);
        Apply("source.argument-aliases", b => Normalize(SourceArgumentAliases.Rewrite(b)));
        var reduced = Iteration.Run(body, current => DeadAssignments(Map(Retype(Propagate(current)), v => Simplify(v, types))), ManagedStructure.Same, 16);
        iteration?.Invoke(reduced);
        if (reduced.Status != IterationStatus.Stable) return original;
        Apply("source.scalar-reduction", _ => reduced.Value);
        Apply("source.boolean-stores", b => DropStatements(BooleanStores(b, types)));
        Apply("source.struct-copies-final", SourceStructCopies.Rewrite);
        Apply("source.scalar-struct-copies", SourceScalarStructCopies.Rewrite);
        Apply("source.struct-snapshots", SourceStructCopies.SnapshotReads);
        Apply("source.caught-exceptions", b => DeadAssignments(Map(SourceCaughtExceptions.Rewrite(b, types), v => Simplify(v, types))));
        Apply("source.nonnull-branches", b => DropStatements(SourceNonNullReceivers.FoldBranches(b)));
        Apply("source.exception-paths", SourceExceptionPaths.Rewrite);
        Apply("source.dead-stores", DeadStores);
        Apply("source.field-copies", FoldFieldCopies);
        Apply("source.returns", SourceReturns.Rewrite);
        Apply("source.catch-handlers", SourceCatchHandlers.Rewrite);
        Apply("source.try-blocks", b => SourceTryBlocks.Rewrite(b, fieldGetter));
        Apply("structure.iterator-dispatch", SourceIteratorDispatch.Rewrite);
        Apply("structure.iterator-cleanup", Cpp2CS.Structure.IteratorCleanup.Rewrite);
        return body;
    }

    /// <summary>bool 目标上的参数恒等复制不保留寄存器搬运转换，供普通字段与迭代器入口共同使用。</summary>
    private static ManagedBody BooleanStores(ManagedBody body, ManagedTypes types) => body with
    {
        Blocks = body.Blocks.Select(b => b with
        {
            Statements = b.Statements.Select(s => s is ManagedStore store && types.Kind(store.Target.Type) == TypeKind.Bool
                && BooleanCopies.Argument(store.Value) is { } argument && argument.Type.Equals(store.Target.Type)
                ? store with { Value = argument } : s).ToArray(),
        }).ToArray(),
    };

    /// <summary>局部变量的整体读写 *&amp;x 写成 x：结构体局部变量的整体写入成为普通赋值，参与复制传播。</summary>
    private static ManagedBody Normalize(ManagedBody body)
    {
        static ManagedValue Deep(ManagedValue v) => ManagedValues.Map(v is IndirectValue { Address: AddressValue { Target: LocalValue l } } i && l.Type.Equals(i.Type) ? l : v, Deep);
        return body with
        {
            Blocks = body.Blocks.Select(b => b with
            {
                Statements = b.Statements.Select(s => s switch
                {
                    ManagedStore { Target: IndirectValue { Address: AddressValue { Target: LocalValue l } } i, Value: not ComposedValue } store when l.Type.Equals(i.Type)
                        => new ManagedAssignment(store.Address, l, Deep(store.Value)),
                    ManagedStore { Target: IndirectValue { Address: AddressValue { Target: FieldValue f } } i, Value: not ComposedValue } store when f.Type.Equals(i.Type)
                        => store with { Target = f, Value = Deep(store.Value) },
                    _ => ManagedValues.Map(s, Deep, t => ManagedValues.Map(t, Deep)),
                }).ToArray(),
            }).ToArray(),
        };
    }

    /// <summary>相邻字段复制直接写成 dst.field = src.field，保留读取顺序和求值次数。</summary>
    private static ManagedBody FoldFieldCopies(ManagedBody body)
    {
        var reads = body.Blocks.SelectMany(b => b.Statements).SelectMany(s =>
            (s is ManagedAssignment a ? [a.Value] : ManagedValues.Of(s)).Concat(ManagedValues.CopiedValues(s)))
            .SelectMany(ManagedValues.Walk).OfType<LocalValue>().GroupBy(l => l.Variable).ToDictionary(g => g.Key, g => g.Count());
        return body with { Blocks = body.Blocks.Select(b =>
        {
            var statements = b.Statements.ToList();
            for (var i = 0; i + 1 < statements.Count; i++)
                if (statements[i] is ManagedAssignment { Value: FieldValue { Receiver: ArgumentValue or LocalValue, Accessor: null } field } assignment
                    && reads.GetValueOrDefault(assignment.Target.Variable) == 1
                    && statements[i + 1] is ManagedStore { Target: FieldValue { Receiver: ArgumentValue or LocalValue, Accessor: null }, Value: LocalValue value } store
                    && value.Variable == assignment.Target.Variable)
                {
                    statements[i + 1] = store with { Value = field };
                    statements.RemoveAt(i--);
                }
            return b with { Statements = statements };
        }).ToArray() };
    }

    private static ManagedBody Map(ManagedBody body, Func<ManagedValue, ManagedValue> f)
    {
        ManagedValue Deep(ManagedValue v) => f(ManagedValues.Map(v, Deep));
        return body with { Blocks = body.Blocks.Select(b => b with { Statements = b.Statements.Select(s => ManagedValues.Map(s, Deep, t => ManagedValues.Map(t, Deep))).ToArray() }).ToArray() };
    }

    // 新建数组的长度不可变；只传播无重定义、未取地址的分配结果，保留分配与元素写入。
    private static ManagedBody FreshArrayLengths(ManagedBody body, ManagedTypes types)
    {
        var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
        var written = statements.SelectMany(ManagedValues.Edges).SelectMany(e => e.Copies).Select(c => c.Target.Variable)
            .Concat(statements.OfType<ManagedCall>().Where(c => c.Result is not null).Select(c => c.Result!.Variable))
            .Concat(statements.OfType<ManagedAwait>().Where(c => c.Result is not null).Select(c => c.Result!.Variable))
            .Concat(statements.SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk)
                .OfType<AddressValue>().Select(a => a.Target).OfType<LocalValue>().Select(l => l.Variable)).ToHashSet();
        var lengths = statements.OfType<ManagedAssignment>().GroupBy(a => a.Target.Variable)
            .Where(g => g.Count() == 1 && !written.Contains(g.Key) && g.Single().Value is NewArrayValue { Length: ConstantValue { Bits: <= int.MaxValue } })
            .ToDictionary(g => g.Key, g => ((ConstantValue)((NewArrayValue)g.Single().Value).Length).Bits);
        return lengths.Count == 0 ? body : Map(body, v => Simplify(v is ArrayLengthValue { Array: LocalValue array } length
            && lengths.TryGetValue(array.Variable, out var count) ? new ConstantValue(count, length.Type, length.Width) : v, types));
    }

    // ---------- 0：catch 类型与委托缓存 ----------

    /// <summary>
    /// il2cpp 的 catch 一律接住异常再判断类型：handler 入口的直线序列中，按 isinst 结果分支、不匹配一侧重新抛出时，
    /// 改成带类型的 catch，分支只留匹配一侧（不匹配的异常本来就继续传播）。
    /// </summary>
    internal static ManagedBody TypedCatches(ManagedBody body)
    {
        if (body.Regions.Count == 0) return body;
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var predecessors = Predecessors(body);
        var definitions = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().GroupBy(a => a.Target.Variable)
            .Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single().Value);
        IEnumerable<ManagedValue> Expand(ManagedValue v, int depth) => depth > 4 ? [v] : ManagedValues.Walk(v)
            .SelectMany(x => x is LocalValue l && definitions.TryGetValue(l.Variable, out var d) ? Expand(d, depth + 1).Prepend(x) : [x]);
        bool IsException(ManagedValue v, Variable exception) => v is LocalValue l && (l.Variable == exception
            || definitions.TryGetValue(l.Variable, out var d) && d is LocalValue copied && copied.Variable == exception);
        bool Rethrows(ulong target, Variable exception)
        {
            foreach (var (_, _, s) in Straight(body, blocks, predecessors, target, 0))
                return s is ManagedRethrow || s is ManagedThrow { Exception: var thrown } && IsException(thrown, exception);
            return false;
        }
        var regions = body.Regions.ToList();
        var replaced = new Dictionary<ManagedStatement, ManagedStatement>(ReferenceEqualityComparer.Instance);
        for (var k = 0; k < regions.Count; k++)
        {
            if (regions[k] is not { Kind: ManagedRegionKind.Catch, CatchType: null, Exception: { } exception } region) continue;
            foreach (var (_, _, s) in Straight(body, blocks, predecessors, region.HandlerEntry, 0))
            {
                if (s is ManagedBranch test)
                {
                    var check = Expand(test.Condition, 0).OfType<IsInstValue>().FirstOrDefault(i => IsException(i.Operand, exception.Variable));
                    // catch 的类型必须是 Exception 或其子类；handler 内的 object/interface 检查不是 catch 类型。
                    bool ExceptionType(TypeRef type)
                    {
                        for (TypeRef? current = type; current is DefinitionRef definition; current = definition.Definition.BaseType?.Substitute(definition.Arguments, []))
                            if (definition.Definition is { Assembly: "mscorlib.dll", FullName: "System.Exception" }) return true;
                        return false;
                    }
                    if (check is null || !ExceptionType(check.Target)) break;
                    bool taken = Rethrows(test.Taken.Target, exception.Variable), fallthrough = Rethrows(test.Fallthrough.Target, exception.Variable);
                    if (taken == fallthrough) break;
                    regions[k] = region with { CatchType = check.Target };
                    replaced[test] = new ManagedJump(test.Address, taken ? test.Fallthrough : test.Taken);
                    break;
                }
                if (s is not ManagedAssignment) break;
            }
        }
        if (replaced.Count == 0) return body;
        return body with
        {
            Blocks = body.Blocks.Select(b => b with { Statements = b.Statements.Select(s => replaced.GetValueOrDefault(s, s)).ToArray() }).ToArray(),
            Regions = regions,
        };
    }

    private static bool CacheField(FieldRef field) => field.Field.Name.StartsWith("<>9__", StringComparison.Ordinal);

    /// <summary>
    /// 编译器为不捕获变量的 lambda 生成的委托缓存（&lt;&gt;c.&lt;&gt;9__N 为 null 时新建并写回）：C# 源码里就是 lambda 本身。
    /// 判断缓存是否为 null 的分支只留新建一侧，写回缓存删去。
    /// </summary>
    private static ManagedBody CachedDelegates(ManagedBody body)
    {
        var cached = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().GroupBy(a => a.Target.Variable).Where(g => g.Count() == 1)
            .Where(g => g.Single().Value is StaticFieldValue f && CacheField(f.Field)).Select(g => g.Key).ToHashSet();
        if (cached.Count == 0) return body;
        ManagedStatement Rewrite(ManagedStatement s) => s switch
        {
            ManagedBranch { Condition: ComparisonValue { Condition: Cond.Eq or Cond.Ne, Left: LocalValue l, Right: ConstantValue { Bits: 0 } } c } b when cached.Contains(l.Variable)
                => new ManagedJump(b.Address, c.Condition == Cond.Eq ? b.Taken : b.Fallthrough),
            _ => s,
        };
        return body with
        {
            Blocks = body.Blocks.Select(b => b with
            {
                Statements = b.Statements.Where(s => s is not ManagedStore { Target: StaticFieldValue f } || !CacheField(f.Field)).Select(Rewrite).ToArray(),
            }).ToArray(),
        };
    }

    // ---------- 1、2：类型初始化与判空 ----------

    private static bool Dereferences(ManagedStatement statement, ManagedValue target)
    {
        bool Same(ManagedValue v) => v.Equals(target);
        var values = ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).SelectMany(ManagedValues.Walk);
        return values.Any(v => v is FieldValue f && Same(f.Receiver) || v is ArrayLengthValue l && Same(l.Array) || v is ArrayElementValue e && Same(e.Array))
            || statement is ManagedCall { Invocation.Receiver: { } receiver } && Same(receiver) || statement is ManagedStore { Target: FieldValue field } && Same(field.Receiver);
    }

    private static bool SideEffects(ManagedStatement statement) => statement is not ManagedAssignment;

    /// <summary>从 (块, 下标) 起的直线语句序列：块末的无复制跳转若通向只有这一个前驱的块，接着读那个块。</summary>
    private static IEnumerable<(ulong Block, int Index, ManagedStatement Statement)> Straight(ManagedBody body, Dictionary<ulong, ManagedBlock> blocks, Dictionary<ulong, int> predecessors, ulong block, int start)
    {
        var seen = new HashSet<ulong>();
        while (seen.Add(block) && blocks.TryGetValue(block, out var current))
        {
            for (var i = start; i < current.Statements.Count; i++)
            {
                var statement = current.Statements[i];
                if (statement is ManagedJump { Edge: { Copies.Count: 0, Target: var next } } && predecessors.GetValueOrDefault(next) == 1
                    && !body.Regions.Any(r => r.Try.Contains(block) != r.Try.Contains(next) || r.Handler.Contains(block) != r.Handler.Contains(next)))
                { block = next; start = -1; break; }
                yield return (block, i, statement);
            }
            if (start != -1) yield break;
            start = 0;
        }
    }

    private static Dictionary<ulong, int> Predecessors(ManagedBody body)
    {
        var count = new Dictionary<ulong, int>();
        foreach (var edge in body.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Edges)) count[edge.Target] = count.GetValueOrDefault(edge.Target) + 1;
        foreach (var region in body.Regions) count[region.HandlerEntry] = count.GetValueOrDefault(region.HandlerEntry) + 2;
        return count;
    }

    private static ManagedBody DropStatements(ManagedBody body)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var predecessors = Predecessors(body);
        var drop = new HashSet<ManagedStatement>(ReferenceEqualityComparer.Instance);
        foreach (var block in body.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var statement = block.Statements[i];
                if (statement is ManagedCheck { Condition: ConstantValue { Bits: 0 } }) { drop.Add(statement); continue; }
                if (statement is ManagedCall { Invocation.Method: { Method.Name: "RunClassConstructor" } method }
                    && method.DeclaringType is DefinitionRef { Definition.FullName: "System.Runtime.CompilerServices.RuntimeHelpers" }) { drop.Add(statement); continue; }
                if (statement is not ManagedCheck { Exception.DeclaringType: DefinitionRef { Definition.FullName: "System.NullReferenceException" },
                    Condition: ComparisonValue { Condition: Cond.Eq, Left: LocalValue or ArgumentValue, Right: ConstantValue { Bits: 0 } } condition }) continue;
                foreach (var (_, _, next) in Straight(body, blocks, predecessors, block.Address, i + 1))
                {
                    if (Dereferences(next, condition.Left)) { drop.Add(statement); break; }
                    if (SideEffects(next) && next is not ManagedCall { Invocation.Method.Method.Name: "RunClassConstructor" }) break;
                }
            }
        return body with { Blocks = body.Blocks.Select(b => b with { Statements = b.Statements.Where(s => !drop.Contains(s)).ToArray() }).ToArray() };
    }

    // ---------- 3：位宽与 bool ----------

    private static ManagedValue Simplify(ManagedValue value, ManagedTypes types)
    {
        static ManagedValue? Extended(ManagedValue v) => v is ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend } c ? c.Operand : null;
        bool Bool(ManagedValue v) => types.Kind(v.Type) == TypeKind.Bool;
        switch (value)
        {
            case IsInstValue { BoxedType: null } test when ManagedTypes.IsReferenceType(test.Operand.Type)
                && types.IsAssignable(test.Operand.Type, test.Target):
                return test.Operand;
            case ConversionValue { Kind: ConvKind.Truncate or ConvKind.ZeroExtend or ConvKind.SignExtend, Operand: ConstantValue c } conversion
                when types.Kind(c.Type) is TypeKind.Int or TypeKind.Bool && types.Kind(conversion.Type) is TypeKind.Int or TypeKind.Bool
                    && Fold.Simplify(new Ir.Convert(conversion.Kind, Expr.C(c.Bits, c.Width), conversion.Width)) is Const converted:
                return new ConstantValue(converted.Value, conversion.Type, conversion.Width);
            case ComparisonValue { Left: ConstantValue left, Right: ConstantValue right } comparison
                when types.Kind(left.Type) is TypeKind.Int or TypeKind.Bool && types.Kind(right.Type) is TypeKind.Int or TypeKind.Bool
                    && Fold.Simplify(new Compare(comparison.Condition, Expr.C(left.Bits, left.Width), Expr.C(right.Bits, right.Width))) is Const compared:
                return new ConstantValue(compared.Value, comparison.Type, comparison.Width);
            case BinaryValue { Left: ConstantValue left, Right: ConstantValue right } binary
                when types.Kind(left.Type) is TypeKind.Int or TypeKind.Bool && types.Kind(right.Type) is TypeKind.Int or TypeKind.Bool
                    && Fold.Simplify(new Binary(binary.Op, Expr.C(left.Bits, left.Width), Expr.C(right.Bits, right.Width), binary.Width)) is Const result:
                return new ConstantValue(result.Value, binary.Type, binary.Width);
            case NegatedValue { Operand: ConstantValue constant } negated:
                return new ConstantValue(constant.Bits == 0 ? 1UL : 0UL, negated.Type, negated.Width);
            case ComposedValue composed when SourceStructCopies.WholeValue(composed) is { } whole:
                return whole;
            // 整数等值比较可按同一位宽移项，避免状态判断遗留为 state + 3 == 0。
            case ComparisonValue { Condition: Cond.Eq or Cond.Ne, Left: BinaryValue { Op: BinOp.Add or BinOp.Sub, Right: ConstantValue offset } sum,
                Right: ConstantValue expected } comparison when sum.Width == sum.Left.Width && sum.Width == offset.Width && sum.Width == expected.Width
                    && types.Kind(sum.Type) == TypeKind.Int:
                return comparison with { Left = sum.Left, Right = new ConstantValue(
                    (sum.Op == BinOp.Add ? unchecked(expected.Bits - offset.Bits) : unchecked(expected.Bits + offset.Bits)) & Expr.Mask(sum.Width), sum.Left.Type, sum.Width) };
            // (T)(ulong)x，截断回 x 的位宽：x 本身（类型不同时保留一次转换）
            case ConversionValue { Kind: ConvKind.Truncate } t when Extended(t.Operand) is { } inner && inner.Width == t.Width
                // IR 的运算与比较自带有无符号，同位宽整数之间换类型不改变语义。
                && (inner.Type.Equals(t.Type) || types.Kind(inner.Type) == TypeKind.Int && types.Kind(t.Type) == TypeKind.Int):
                return inner;
            case ConversionValue { Kind: ConvKind.Truncate } t when Extended(t.Operand) is { } inner && inner.Width > t.Width:
                return t with { Operand = inner };
            case ConversionValue { Kind: ConvKind.Truncate, Operand: ConversionValue { Kind: ConvKind.ZeroExtend } extension } t
                when extension.Operand.Width < t.Width && t.Width < extension.Width
                    && types.Kind(extension.Operand.Type) is TypeKind.Int or TypeKind.Bool && types.Kind(t.Type) is TypeKind.Int or TypeKind.Bool:
                return extension with { Type = t.Type, Width = t.Width };
            case ConversionValue { Kind: ConvKind.Truncate } t when t.Operand is ConversionValue { Kind: ConvKind.Truncate } u:
                return t with { Operand = u.Operand };
            // (b ? 1 : 0) & 1 → (b ? 1 : 0)
            case BinaryValue { Op: BinOp.And, Right: ConstantValue { Bits: 1 } } masked when Extended(masked.Left) is { } b && Bool(b):
                return masked.Left;
            case BinaryValue { Op: BinOp.And, Left: ConstantValue { Bits: 1 } } masked when Extended(masked.Right) is { } b && Bool(b):
                return masked.Right;
            // (b ? 1 : 0) != 0 → b；== 0 → !b
            case ComparisonValue { Condition: Cond.Ne or Cond.Eq, Right: ConstantValue { Bits: 0 } } c when Extended(c.Left) is { } b && Bool(b):
                return c.Condition == Cond.Ne ? b : new NegatedValue(b, c.Type);
            case ComparisonValue { Condition: Cond.Ne or Cond.Eq, Right: ConstantValue { Bits: 0 } } c when Bool(c.Left) && c.Left is not ConstantValue:
                return c.Condition == Cond.Ne ? c.Left : new NegatedValue(c.Left, c.Type);
            case ConversionValue { Kind: ConvKind.Truncate } t when Bool(t) && t.Operand is ConversionValue { Kind: ConvKind.ZeroExtend } z && Bool(z.Operand):
                return z.Operand;
            case NegatedValue { Operand: NegatedValue inner }:
                return inner.Operand;
            // 寄存器结构体的拼装与拆分：0 | a | (b << 32)
            case BinaryValue { Op: BinOp.Shl or BinOp.LShr or BinOp.AShr, Left: ConstantValue { Bits: 0 }, Right: ConstantValue } shiftedZero:
                return new ConstantValue(0, shiftedZero.Type, shiftedZero.Width);
            case BinaryValue { Op: BinOp.Or, Left: ConstantValue { Bits: 0 } } or0:
                return or0.Right;
            case BinaryValue { Op: BinOp.Or, Right: ConstantValue { Bits: 0 } } or1:
                return or1.Left;
            case BinaryValue { Op: BinOp.LShr, Right: ConstantValue { Bits: 32 } } high when Packed(high.Left) is (_, { } upper):
                return Widen(upper, high);
            case ConversionValue { Kind: ConvKind.Truncate, Width: 32 } low when Packed(low.Operand) is ({ } lower, _):
                return lower.Width == 32 && (lower.Type.Equals(low.Type) || types.Kind(lower.Type) == types.Kind(low.Type)) ? lower : low with { Operand = lower };
            default:
                return value;
        }
    }

    /// <summary>a | (b &lt;&lt; 32)，a、b 是 32 位值的零扩展：返回 (a, b)。</summary>
    private static (ManagedValue? Lower, ManagedValue? Upper) Packed(ManagedValue v)
    {
        static ManagedValue? Word(ManagedValue x) => x is ConversionValue { Kind: ConvKind.ZeroExtend, Operand: { Width: <= 32 } o } ? o : null;
        if (v is not BinaryValue { Op: BinOp.Or } or) return (null, null);
        foreach (var (a, b) in new[] { (or.Left, or.Right), (or.Right, or.Left) })
            if (b is BinaryValue { Op: BinOp.Shl, Right: ConstantValue { Bits: 32 } } shifted && Word(shifted.Left) is { } upper)
                return (Word(a), upper);
        return (null, null);
    }

    private static ManagedValue Widen(ManagedValue word, ManagedValue like) => word.Width == like.Width ? word : new ConversionValue(ConvKind.ZeroExtend, word, like.Type, like.Width);

    // ---------- 4：内联与复制传播 ----------

    private static ManagedBody Propagate(ManagedBody body)
    {
        var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
        var assignments = statements.OfType<ManagedAssignment>().GroupBy(a => a.Target.Variable).ToDictionary(g => g.Key, g => g.ToArray());
        // 局部变量的其他写入：边上的复制、调用结果、await 结果、整体写入其地址。
        var written = statements.SelectMany(ManagedValues.Edges).SelectMany(e => e.Copies).Select(c => c.Target.Variable)
            .Concat(statements.OfType<ManagedCall>().Where(c => c.Result is not null).Select(c => c.Result!.Variable))
            .Concat(statements.OfType<ManagedAwait>().Where(a => a.Result is not null).Select(a => a.Result!.Variable))
            .Concat(body.Regions.Where(r => r.Exception is not null).Select(r => r.Exception!.Variable)).ToHashSet();
        var addresses = statements.SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk)
            .OfType<AddressValue>().Select(a => a.Target).ToArray();
        var addressed = addresses.OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
        var addressedArguments = addresses.OfType<ArgumentValue>().Select(a => a.Index).ToHashSet();
        bool Single(Variable v) => assignments.TryGetValue(v, out var a) && a.Length == 1 && !written.Contains(v) && !addressed.Contains(v);
        var replace = new Dictionary<Variable, ManagedValue>();
        foreach (var (variable, list) in assignments)
        {
            if (!Single(variable)) continue;
            var value = list[0].Value;
            // 复制：t2 = t1（t1 只赋值一次或是参数）
            if (value is LocalValue source && source.Type.Equals(list[0].Target.Type) && (Single(source.Variable) || !assignments.ContainsKey(source.Variable) && !written.Contains(source.Variable)))
                replace[variable] = value;
            else if (value is ConstantValue && value.Type.Equals(list[0].Target.Type)) replace[variable] = value;
            else if (value is ArgumentValue argument && !addressedArguments.Contains(argument.Index) && value.Type.Equals(list[0].Target.Type)) replace[variable] = value;
            // lambda 所在类的单例 <>c.<>9（只读静态字段）
            else if (value is StaticFieldValue { Field.Field.Name: "<>9" } && value.Type.Equals(list[0].Target.Type)) replace[variable] = value;
            // 只在截断中使用的扩展：内联后与截断抵消
            else if (value is ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend, Operand: LocalValue or ArgumentValue or ConstantValue } && OnlyTruncated(statements, variable))
                replace[variable] = value;
        }
        // 直线序列中的复制 y = x（y 只赋值一次、只使用一次、不取地址）：x 在两者之间没有被改写时，把使用处的 y 换成 x。
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var predecessors = Predecessors(body);
        var useCount = statements.SelectMany(s => ManagedValues.Of(s).Where(v => s is not ManagedAssignment a || !ReferenceEquals(v, a.Target)).Concat(ManagedValues.CopiedValues(s)))
            .SelectMany(ManagedValues.Walk).OfType<LocalValue>().GroupBy(l => l.Variable).ToDictionary(g => g.Key, g => g.Count());
        bool Writes(ManagedStatement s, Variable v) => s is ManagedAssignment a && a.Target.Variable == v || s is ManagedCall { Result: { } r } && r.Variable == v
            || s is ManagedAwait { Result: { } w } && w.Variable == v || ManagedValues.Edges(s).SelectMany(e => e.Copies).Any(c => c.Target.Variable == v)
            || s is ManagedStore { Target: IndirectValue { Address: AddressValue { Target: LocalValue t } } } && t.Variable == v
            || ManagedValues.Of(s).SelectMany(ManagedValues.Walk).Any(x => x is AddressValue { Target: LocalValue t } && t.Variable == v);
        foreach (var block in body.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                // 扩展后只被截断使用一次的值：使用处紧随其后（之间只有对其他局部变量的无副作用赋值）时代入，与截断抵消。
                if (block.Statements[i] is ManagedAssignment { Value: ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend } extension } widened
                    && !replace.ContainsKey(widened.Target.Variable) && useCount.GetValueOrDefault(widened.Target.Variable) == 1
                    && assignments.TryGetValue(widened.Target.Variable, out var widenedDefs) && widenedDefs.Length == 1 && !written.Contains(widened.Target.Variable)
                    && !addressed.Contains(widened.Target.Variable) && OnlyTruncated(statements, widened.Target.Variable))
                {
                    var reads = ManagedValues.Walk(extension).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
                    foreach (var (_, _, next) in Straight(body, blocks, predecessors, block.Address, i + 1))
                    {
                        if (ManagedValues.Of(next).Concat(ManagedValues.CopiedValues(next)).SelectMany(ManagedValues.Walk).Any(v => v is LocalValue l && l.Variable == widened.Target.Variable))
                        { replace[widened.Target.Variable] = extension; break; }
                        if (next is not ManagedAssignment a || reads.Contains(a.Target.Variable)) break;
                    }
                    continue;
                }
                if (block.Statements[i] is not ManagedAssignment { Value: LocalValue x } copy || replace.ContainsKey(copy.Target.Variable)
                    || !x.Type.Equals(copy.Target.Type) || useCount.GetValueOrDefault(copy.Target.Variable) != 1
                    || !assignments.TryGetValue(copy.Target.Variable, out var defs) || defs.Length != 1 || written.Contains(copy.Target.Variable) || addressed.Contains(copy.Target.Variable)) continue;
                foreach (var (_, _, next) in Straight(body, blocks, predecessors, block.Address, i + 1))
                {
                    if (ManagedValues.Of(next).Concat(ManagedValues.CopiedValues(next)).SelectMany(ManagedValues.Walk).Any(v => v is LocalValue l && l.Variable == copy.Target.Variable))
                    { replace[copy.Target.Variable] = x; break; }
                    if (Writes(next, x.Variable)) break;
                }
            }
        if (replace.Count == 0) return body;
        ManagedValue Resolve(ManagedValue v)
        {
            var seen = 0;
            while (v is LocalValue l && replace.TryGetValue(l.Variable, out var r) && seen++ < 16) v = r;
            return v;
        }
        ManagedValue Deep(ManagedValue v) => ManagedValues.Map(v is LocalValue ? Resolve(v) : v, Deep);
        return body with
        {
            Blocks = body.Blocks.Select(b => b with
            {
                Statements = b.Statements.Where(s => s is not ManagedAssignment a || !replace.ContainsKey(a.Target.Variable))
                    .Select(s => s is ManagedAssignment a ? a with { Value = Deep(a.Value) } : ManagedValues.Map(s, Deep)).ToArray(),
            }).ToArray(),
        };
    }

    /// <summary>只赋值一次、使用处仍保留全部原始位的扩展副本，局部改用原类型，使用处保留必要扩展。</summary>
    private static ManagedBody Retype(ManagedBody body)
    {
        var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
        var definitions = statements.OfType<ManagedAssignment>().GroupBy(a => a.Target.Variable).Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
        var written = statements.SelectMany(ManagedValues.Edges).SelectMany(e => e.Copies).Select(c => c.Target.Variable)
            .Concat(statements.OfType<ManagedCall>().Where(c => c.Result is not null).Select(c => c.Result!.Variable)).ToHashSet();
        var retyped = new Dictionary<Variable, LocalValue>();
        foreach (var (variable, definition) in definitions)
            if (definition.Value is ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend, Operand: var operand } && !written.Contains(variable)
                && OnlyTruncated(statements, variable) && statements.SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk)
                    .OfType<ConversionValue>().Where(c => c is { Kind: ConvKind.Truncate, Operand: LocalValue l } && l.Variable == variable)
                    .All(c => c.Width >= operand.Width && c.Width <= definition.Value.Width))
                retyped[variable] = new LocalValue(variable, operand.Type, operand.Width);
        if (retyped.Count == 0) return body;
        ManagedValue Deep(ManagedValue v) => v is ConversionValue { Kind: ConvKind.Truncate, Operand: LocalValue l } conversion && retyped.TryGetValue(l.Variable, out var r)
            ? conversion.Width == r.Width ? r : new ConversionValue(((ConversionValue)definitions[l.Variable].Value).Kind, r, conversion.Type, conversion.Width)
            : ManagedValues.Map(v, Deep);
        return body with
        {
            Blocks = body.Blocks.Select(b => b with
            {
                Statements = b.Statements.Select(s => s is ManagedAssignment a && retyped.TryGetValue(a.Target.Variable, out var r)
                    ? new ManagedAssignment(a.Address, r, ((ConversionValue)a.Value).Operand is var o ? Deep(o) : o) : ManagedValues.Map(s, Deep, t => ManagedValues.Map(t, Deep))).ToArray(),
            }).ToArray(),
        };
    }

    /// <summary>
    /// 死存储：活跃性分析（块间按出边与异常 handler 入口传播）之后，删去写入后不再被读取的局部变量上的无副作用赋值。
    /// </summary>
    private static ManagedBody DeadStores(ManagedBody body)
    {
        static IEnumerable<Variable> Reads(ManagedStatement s) => ManagedValues.Of(s).Where(v => s is not ManagedAssignment a || !ReferenceEquals(v, a.Target))
            .Concat(ManagedValues.CopiedValues(s)).SelectMany(ManagedValues.Walk).OfType<LocalValue>().Select(l => l.Variable);
        // 取地址的局部变量可能经地址读写，不参与。
        var addressed = body.Blocks.SelectMany(b => b.Statements).SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk)
            .OfType<AddressValue>().Select(a => a.Target).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var handlers = body.Regions.SelectMany(r => r.Try.Select(t => (t, r.HandlerEntry))).ToLookup(p => p.t, p => p.HandlerEntry);
        var liveIn = body.Blocks.ToDictionary(b => b.Address, _ => new HashSet<Variable>());
        HashSet<Variable> LiveOut(ManagedBlock block)
        {
            var live = new HashSet<Variable>();
            foreach (var edge in block.Statements.SelectMany(ManagedValues.Edges))
            {
                if (liveIn.TryGetValue(edge.Target, out var target)) live.UnionWith(target);
            }
            foreach (var handler in handlers[block.Address]) if (liveIn.TryGetValue(handler, out var h)) live.UnionWith(h);
            return live;
        }
        bool changed;
        do
        {
            changed = false;
            foreach (var block in body.Blocks.Reverse())
            {
                var live = LiveOut(block);
                for (var i = block.Statements.Count - 1; i >= 0; i--)
                {
                    var s = block.Statements[i];
                    foreach (var copy in ManagedValues.Edges(s).SelectMany(e => e.Copies)) live.Remove(copy.Target.Variable);
                    if (s is ManagedAssignment a) live.Remove(a.Target.Variable);
                    live.UnionWith(Reads(s));
                }
                // 处于 try 中的块：异常可在块内任意位置发生，handler 需要的变量在块入口也活跃。
                foreach (var handler in handlers[block.Address]) if (liveIn.TryGetValue(handler, out var h)) live.UnionWith(h);
                if (!live.SetEquals(liveIn[block.Address])) { liveIn[block.Address] = live; changed = true; }
            }
        } while (changed);
        bool Pure(ManagedValue v) => ManagedValues.Walk(v).All(x => x is ConstantValue or LocalValue or ArgumentValue or ConversionValue or ComparisonValue
            or NegatedValue or BooleanValue or StringValue or ComposedValue or StaticFieldValue or IsInstValue or BinaryValue { Op: not (BinOp.SDiv or BinOp.UDiv or BinOp.SRem or BinOp.URem) });
        return body with
        {
            Blocks = body.Blocks.Select(block =>
            {
                var live = LiveOut(block);
                var kept = new List<ManagedStatement>();
                for (var i = block.Statements.Count - 1; i >= 0; i--)
                {
                    var s = block.Statements[i];
                    foreach (var copy in ManagedValues.Edges(s).SelectMany(e => e.Copies)) live.Remove(copy.Target.Variable);
                    if (s is ManagedAssignment a && !live.Contains(a.Target.Variable) && !addressed.Contains(a.Target.Variable) && Pure(a.Value)
                        && !handlers[block.Address].Any() && !body.Regions.Any(r => r.Exception?.Variable == a.Target.Variable)) continue;
                    if (s is ManagedAssignment assigned) live.Remove(assigned.Target.Variable);
                    live.UnionWith(Reads(s));
                    kept.Add(s);
                }
                kept.Reverse();
                return block with { Statements = kept };
            }).ToArray(),
        };
    }

    private static bool OnlyTruncated(ManagedStatement[] statements, Variable variable)
    {
        var uses = 0;
        bool Inspect(ManagedValue value)
        {
            if (value is ConversionValue { Kind: ConvKind.Truncate, Operand: LocalValue local } && local.Variable == variable)
            { uses++; return true; }
            if (value is LocalValue other && other.Variable == variable) return false;
            var valid = true;
            ManagedValues.Map(value, child => { valid &= Inspect(child); return child; });
            return valid;
        }
        foreach (var statement in statements)
            foreach (var root in ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)))
            {
                if (statement is ManagedAssignment a && ReferenceEquals(root, a.Target)) continue;
                if (!Inspect(root)) return false;
            }
        return uses > 0;
    }

    private static ManagedBody DeadAssignments(ManagedBody body)
    {
        var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
        var used = statements.SelectMany(s => ManagedValues.Of(s).Where(v => s is not ManagedAssignment a || !ReferenceEquals(v, a.Target)).Concat(ManagedValues.CopiedValues(s)))
            .SelectMany(ManagedValues.Walk).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
        foreach (var copy in statements.SelectMany(ManagedValues.Edges).SelectMany(e => e.Copies)) used.Add(copy.Target.Variable);
        bool Pure(ManagedValue v) => ManagedValues.Walk(v).All(x => x is ConstantValue or LocalValue or ArgumentValue or ConversionValue or ComparisonValue
            or NegatedValue or BooleanValue or StringValue or BinaryValue { Op: not (BinOp.SDiv or BinOp.UDiv or BinOp.SRem or BinOp.URem) });
        var changed = false;
        var blocks = body.Blocks.Select(b =>
        {
            var kept = b.Statements.Where(s => !(s is ManagedAssignment a && !used.Contains(a.Target.Variable) && Pure(a.Value))).ToArray();
            changed |= kept.Length != b.Statements.Count;
            return b with { Statements = kept };
        }).ToArray();
        return changed ? body with { Blocks = blocks } : body;
    }
}
