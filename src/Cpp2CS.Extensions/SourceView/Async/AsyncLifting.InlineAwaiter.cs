using Cpp2CS.Ir;

namespace Cpp2CS.Extensions.SourceView;

public static partial class AsyncLifting
{
    private sealed partial class Lifter
    {
        private readonly HashSet<Variable> inlineReads = [];

        private static ManagedValue StorageValue(ManagedValue value) => value switch
        {
            AddressValue address => StorageValue(address.Target),
            IndirectValue { Address: AddressValue address } => StorageValue(address.Target),
            _ => value,
        };

        // UniTask.Awaiter 只有 task 字段；IL2CPP 把 GetAwaiter 内联成对该字段的结构体复制。
        private static bool InlineTaskField(ManagedValue value, Variable awaiter) => StorageValue(value) is FieldValue
        { Field.Field.Name: "task", Receiver: var receiver, Field.DeclaringType: DefinitionRef owner }
            && owner.Definition.FullName == "Cysharp.Threading.Tasks.UniTask.Awaiter"
            && StorageValue(receiver) is LocalValue local && local.Variable == awaiter;

        private void FoldInlineAwaiter(Variable awaiter, LocalValue held)
        {
            var definitions = blocks.Values.SelectMany(s => s).OfType<ManagedAssignment>()
                .GroupBy(a => a.Target.Variable).Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single().Value);
            ManagedValue Resolve(ManagedValue value)
            {
                var seen = new HashSet<Variable>();
                while (true)
                {
                    value = StorageValue(value);
                    if (value is ConversionValue conversion) { value = conversion.Operand; continue; }
                    if (value is LocalValue local && seen.Add(local.Variable) && definitions.TryGetValue(local.Variable, out var definition))
                    { value = definition; continue; }
                    return value;
                }
            }
            bool Member(ManagedValue value, string name) => Resolve(value) is FieldValue field
                && field.Field.Field.Name == name && InlineTaskField(Resolve(field.Receiver), awaiter);
            bool SourceCall(ManagedCall call) => call.Invocation.Receiver is { } receiver && Member(receiver, "source")
                && call.Invocation.Arguments is [var token] && Member(token, "token");
            bool Read(ManagedValue value) => Member(value, "source") || Member(value, "token");
            foreach (var (variable, value) in definitions)
                if (Read(value)) inlineReads.Add(variable);

            // 重定向挂起边之后，状态查询只用于已消除的调度判断，真正的状态与异常交给 await。
            foreach (var statements in blocks.Values)
                for (var i = 0; i < statements.Count; i++)
                    if (statements[i] is ManagedCall { Invocation.Method.Method.Name: "GetStatus", Result: { } result } call && SourceCall(call))
                        statements[i] = new ManagedAssignment(call.Address, result, new ConstantValue(1, result.Type, result.Width));

            ulong SkipJumps(ulong address)
            {
                var seen = new HashSet<ulong>();
                while (seen.Add(address) && blocks[address] is [ManagedJump { Edge.Copies.Count: 0 } jump]) address = jump.Edge.Target;
                return address;
            }
            var addressed = blocks.Values.SelectMany(s => s).SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
                .SelectMany(ManagedValues.Walk).OfType<AddressValue>().Select(a => a.Target).OfType<LocalValue>()
                .Select(l => l.Variable).ToHashSet();
            // 非泛型 GetResult：source 为 null 时立即成功，否则沿直线调用 source.GetResult(token)。
            // 两条路径合并成一次 await，避免 null 快路跳过 await 或引入额外的 GetResult。
            foreach (var address in order)
            {
                var statements = blocks[address];
                if (statements.LastOrDefault() is not ManagedBranch
                    { Condition: ComparisonValue { Condition: Cond.Eq or Cond.Ne } comparison } branch) continue;
                if (!(Member(comparison.Left, "source") && comparison.Right is ConstantValue { Bits: 0 }
                    || Member(comparison.Right, "source") && comparison.Left is ConstantValue { Bits: 0 })) continue;
                var empty = comparison.Condition == Cond.Eq ? branch.Taken : branch.Fallthrough;
                var present = comparison.Condition == Cond.Eq ? branch.Fallthrough : branch.Taken;
                if (empty.Copies.Count == 0 && present.Copies.Count == 0
                    && FoldInlineResult(held, branch, statements, empty, present, definitions, Member, SourceCall, SkipJumps)) continue;
                if (present.Copies.Count != 0) continue;
                var current = present.Target;
                var seen = new HashSet<ulong>();
                ManagedCall? getResult = null;
                ulong callBlock = 0;
                var valid = true;
                IReadOnlyList<ManagedCopy> exitCopies = [];
                while (SkipJumps(current) != SkipJumps(empty.Target) && seen.Add(current))
                {
                    var path = blocks[current];
                    foreach (var statement in path.SkipLast(1))
                    {
                        if (statement is ManagedAssignment assignment && Read(assignment.Value)) continue;
                        // 异常区域标志在 GetResult 前写入；保留该写入，并证明正常合流后读取前会被覆盖。
                        if (statement is ManagedAssignment { Value: ConstantValue } marker && !addressed.Contains(marker.Target.Variable)
                            && AsyncBranchCopies.OverwrittenAtEntry(marker.Target.Variable, empty.Target, blocks)) continue;
                        if (statement is ManagedCall { Invocation.Method.Method.Name: "GetResult", Result: null } call && SourceCall(call) && getResult is null)
                        { getResult = call; callBlock = current; continue; }
                        valid = false;
                    }
                    if (!valid || path.LastOrDefault() is not ManagedJump jump
                        || jump.Edge.Copies.Count != 0 && SkipJumps(jump.Edge.Target) != SkipJumps(empty.Target)) { valid = false; break; }
                    exitCopies = jump.Edge.Copies;
                    current = jump.Edge.Target;
                }
                if (!valid || getResult is null || SkipJumps(current) != SkipJumps(empty.Target) || !exitCopies.SequenceEqual(empty.Copies)) continue;
                statements[^1] = new ManagedJump(branch.Address, present);
                var index = blocks[callBlock].IndexOf(getResult);
                blocks[callBlock][index] = new ManagedAwait(getResult.Address, held, null);
            }
        }
    }
}
