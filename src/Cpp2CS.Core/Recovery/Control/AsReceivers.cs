using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Recovery.Effects;

namespace Cpp2CS.Recovery.Control;

/// <summary>
/// (x as T).M() 的判空被 IL2CPP 和 clang 拆开：先判 x，再判类型（失败抛空引用），之后直接用 x。
/// isinst 对 null 和类型不符都得到 null（ECMA-335 III.4.6），callvirt 和字段访问对 null 抛同样的异常，
/// 所以判空并入类型判断；类型判断之后直到第一次访问都没有其他效果时，它也并入这次访问。
/// ((T)x).M() 拆开后类型不符抛 InvalidCast：castclass 让 null 通过（III.4.3），由访问抛空引用，两次判断都并回 castclass 和访问。
/// </summary>
internal static class AsReceivers
{
    /// <summary>沿直线路径最多看的语句数。</summary>
    private const int Horizon = 32;

    public static ManagedBody Run(ManagedBody body)
    {
        var pass = new Pass(body);
        return pass.Rewrite();
    }

    private sealed class Pass
    {
        private readonly ManagedBody body;
        private readonly Dictionary<ulong, ManagedBlock> blocks;
        private readonly Dictionary<ulong, int> incoming = [];
        private readonly HashSet<ulong> entries;
        private readonly Dictionary<Variable, int> reads = [];
        private readonly Dictionary<Variable, List<ManagedValue?>> definitions = [];
        private readonly HashSet<ManagedStatement> removed = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<ManagedStatement, ManagedStatement> replaced = new(ReferenceEqualityComparer.Instance);

        public Pass(ManagedBody body)
        {
            this.body = body;
            blocks = body.Blocks.ToDictionary(b => b.Address);
            entries = body.Regions.Select(r => r.HandlerEntry).Append(body.Blocks[0].Address).ToHashSet();
            foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
            {
                foreach (var edge in ManagedValues.Edges(statement))
                {
                    incoming[edge.Target] = incoming.GetValueOrDefault(edge.Target) + 1;
                    foreach (var copy in edge.Copies) Define(copy.Target.Variable, copy.Value);
                }
                if (statement is ManagedAssignment assignment) Define(assignment.Target.Variable, assignment.Value);
                if (statement is ManagedCall { Result: { } result }) Define(result.Variable, null);
                foreach (var value in (statement is ManagedAssignment a ? [a.Value] : ManagedValues.Of(statement)).Concat(ManagedValues.CopiedValues(statement)))
                    foreach (var local in ManagedValues.Walk(value).OfType<LocalValue>())
                        reads[local.Variable] = reads.GetValueOrDefault(local.Variable) + 1;
            }
        }

        private void Define(Variable variable, ManagedValue? value)
        {
            if (!definitions.TryGetValue(variable, out var list)) definitions[variable] = list = [];
            list.Add(value);
        }

        public ManagedBody Rewrite()
        {
            foreach (var block in body.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not ManagedCheck check || !Throws(check, "System.NullReferenceException")) continue;
                    if (NullTest(check) is { } tested) MergeNullTest(block.Address, i, check, tested);
                    else if (TypeTest(block, i, check) is var (cast, flag)) MergeTypeTest(block.Address, i, check, cast, flag);
                }
            var changed = removed.Count + replaced.Count > 0;
            var blocksAfter = body.Blocks.Select(b => b with
            {
                Statements = b.Statements.Where(s => !removed.Contains(s)).Select(s =>
                {
                    var current = replaced.GetValueOrDefault(s, s);
                    if (current is ManagedAssignment { Value: IsInstValue { Operand: LocalValue operand } again } assignment && SameCast(operand, again.Target))
                    {
                        changed = true;
                        return assignment with { Value = operand };
                    }
                    return current;
                }).ToArray(),
            }).ToArray();
            return changed ? body with { Blocks = blocksAfter } : body;
        }

        private static bool Throws(ManagedCheck check, string exception) => check.Exception.Method.Owner.FullName == exception;

        /// <summary>局部只有一个来源，就是到同一类型的 isinst：再判一次得到同一个值。</summary>
        private bool SameCast(LocalValue local, TypeRef target) =>
            definitions.GetValueOrDefault(local.Variable) is [IsInstValue first] && first.Target.Equals(target);

        private static ManagedValue? NullTest(ManagedCheck check) =>
            check.Condition is ComparisonValue { Condition: Cond.Eq, Left: var tested and (LocalValue or ArgumentValue), Right: ConstantValue { Bits: 0 } } && ManagedTypes.IsReferenceType(tested.Type) ? tested : null;

        /// <summary>类型判断：check (isinst(x) == null)，或先把 isinst(x) != null 存进局部再判这个局部。</summary>
        private static (IsInstValue Cast, ManagedAssignment? Flag)? TypeTest(ManagedBlock block, int index, ManagedCheck check)
        {
            if (check.Condition is ComparisonValue { Condition: Cond.Eq, Left: IsInstValue { Operand: LocalValue or ArgumentValue } direct, Right: ConstantValue { Bits: 0 } }) return (direct, null);
            if (check.Condition is ComparisonValue { Condition: Cond.Eq, Left: LocalValue flag, Right: ConstantValue { Bits: 0 } } && index > 0
                && block.Statements[index - 1] is ManagedAssignment { Value: ComparisonValue { Condition: Cond.Ne, Left: IsInstValue { Operand: LocalValue or ArgumentValue } stored, Right: ConstantValue { Bits: 0 } } } assignment
                && assignment.Target.Variable.Equals(flag.Variable)) return (stored, assignment);
            return null;
        }

        private IEnumerable<(ManagedBlock Block, int Index)> Following(ulong address, int index)
        {
            var scope = Scope(address);
            for (var budget = Horizon; budget > 0; budget--)
            {
                var block = blocks[address];
                index++;
                if (index >= block.Statements.Count) yield break;
                if (block.Statements[index] is ManagedJump { Edge: { Copies.Count: 0 } edge })
                {
                    if (incoming.GetValueOrDefault(edge.Target) != 1 || entries.Contains(edge.Target) || !blocks.ContainsKey(edge.Target) || Scope(edge.Target) != scope) yield break;
                    (address, index) = (edge.Target, -1);
                    continue;
                }
                yield return (block, index);
            }
        }

        private string Scope(ulong address) => string.Join(",", body.Regions.Select((r, i) => r.Try.Contains(address) ? $"t{i}" : r.Handler.Contains(address) ? $"h{i}" : ""));

        private void MergeNullTest(ulong address, int index, ManagedCheck check, ManagedValue tested)
        {
            foreach (var (block, at) in Following(address, index))
            {
                var statement = block.Statements[at];
                if (statement is ManagedCheck next && TypeTest(block, at, next) is var (cast, flag) && Same(cast.Operand, tested))
                {
                    if (Throws(next, "System.NullReferenceException")) removed.Add(check);
                    else if (Throws(next, "System.InvalidCastException")) MergeTypeTest(block.Address, at, next, cast, flag, check);
                    return;
                }
                if (statement is not ManagedAssignment { ExceptionArrival: false } assignment || !Transparent(assignment.Value) || Same(assignment.Target, tested)) return;
            }
        }

        /// <param name="nullTest">类型不符抛 InvalidCast 时，前面的判空。</param>
        private void MergeTypeTest(ulong address, int index, ManagedCheck check, IsInstValue cast, ManagedAssignment? flag, ManagedCheck? nullTest = null)
        {
            if (flag is not null && reads.GetValueOrDefault(flag.Target.Variable) != 1) return;
            var source = cast.Operand;
            var hard = nullTest is not null;
            ManagedValue conversion = hard ? new CheckedCastValue(source, cast.Target) : cast;
            ManagedAssignment? converted = null;
            var results = new HashSet<Variable>();
            foreach (var (block, at) in Following(address, index))
            {
                var statement = block.Statements[at];
                if (replaced.ContainsKey(statement) || removed.Contains(statement)) return;
                ManagedStatement? access = statement switch
                {
                    ManagedCall { Invocation: { Receiver: { } receiver, Constraint: null } invocation } call when IsSource(receiver) && invocation.Arguments.All(Transparent)
                        && (invocation.Virtual || !invocation.Method.Method.IsOverridable) =>
                        call with { Invocation = invocation with { Receiver = Cast(receiver), Virtual = true } },
                    ManagedStore { Target: FieldValue { Pending: null } field } store when IsSource(field.Receiver) && Transparent(store.Value) =>
                        store with { Target = field with { Receiver = Cast(field.Receiver) } },
                    // 访问器已经证明等于字段访问，对 null 同样抛空引用。
                    ManagedAssignment { Value: FieldValue { Pending: null } field } read when IsSource(field.Receiver) && !Same(read.Target, source) =>
                        read with { Value = field with { Receiver = Cast(field.Receiver) } },
                    _ => null,
                };
                if (access is not null)
                {
                    removed.Add(check);
                    if (flag is not null) removed.Add(flag);
                    if (nullTest is not null) removed.Add(nullTest);
                    if (converted is not null) replaced[converted] = converted with { Value = conversion };
                    replaced[statement] = access;
                    return;
                }
                if (statement is not ManagedAssignment { ExceptionArrival: false } assignment || Same(assignment.Target, source)) return;
                if (assignment.Value is IsInstValue { Operand: var operand } next && next.Target.Equals(cast.Target) && IsSource(operand)
                    && definitions.GetValueOrDefault(assignment.Target.Variable) is [_])
                {
                    if (hard && converted is null) converted = assignment;
                    results.Add(assignment.Target.Variable);
                }
                // InvalidCast 和空引用不能互换：转换之前不允许任何可能抛出的读取。
                else if (hard && converted is null ? !ManagedEffects.Value(assignment.Value).CanDiscard : !Transparent(assignment.Value)) return;
            }

            bool IsSource(ManagedValue value) => Same(value, source) || value is LocalValue local && results.Contains(local.Variable);
            ManagedValue Cast(ManagedValue receiver) => Same(receiver, source) ? conversion : receiver;
        }

        private static bool Same(ManagedValue a, ManagedValue b) => (a, b) switch
        {
            (LocalValue x, LocalValue y) => x.Variable.Equals(y.Variable),
            (ArgumentValue x, ArgumentValue y) => x.Index == y.Index,
            _ => false,
        };

        /// <summary>只读，且最多抛空引用：和判空互换顺序观察不到差别。beforefieldinit 的静态字段读取不构成时序约束（ECMA-335 II.10.5.3.2）。</summary>
        private static bool Transparent(ManagedValue value)
        {
            var effect = ManagedEffects.Value(value, v => v is StaticFieldValue { Accessor: null } read
                && (read.Field.Field.Owner.Attributes & System.Reflection.TypeAttributes.BeforeFieldInit) != 0 ? new EffectSummary(EffectKind.Read) : null);
            return (effect.Kinds & ~EffectKind.Read) == 0 && (effect.Exceptions & ~ExceptionEffect.NullReference) == 0;
        }
    }
}
