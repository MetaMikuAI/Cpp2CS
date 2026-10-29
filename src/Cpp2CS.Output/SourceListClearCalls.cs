using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

internal static partial class SourceListCalls
{
    /// <summary>保存旧长度、归零、版本加一，并在旧长度为正时清空原有元素。</summary>
    private static ManagedBody? MatchClear(ManagedBody body, ManagedTypes types, Action<ulong, MethodRef> matched)
    {
        var list = types.CorlibDefinition("System.Collections.Generic.List");
        var clear = list?.Methods.SingleOrDefault(m => m.Name == "Clear" && !m.IsStatic && m.Parameters.Count == 0 && ManagedTypes.IsVoid(m.ReturnType));
        if (clear is null) return null;
        var flow = new PatternFlow(body);
        foreach (var block in body.Blocks)
        for (var start = 0; start < block.Statements.Count; start++)
        {
            if (block.Statements[start] is not ManagedAssignment first || Strip(first.Value) is not FieldValue field
                || field.Field.Field.Owner != list || field.Field.Field.Name is not ("_size" or "_version")
                || field.Receiver is not (LocalValue or ArgumentValue) || field.Receiver.Type is not DefinitionRef { Arguments.Count: 1 } owner) continue;
            var receiver = field.Receiver;
            var values = new Dictionary<Variable, ManagedValue>();
            var remove = new HashSet<ManagedStatement>(ReferenceEqualityComparer.Instance);
            var zeroed = false;
            var versioned = false;
            ManagedValue Resolve(ManagedValue value)
            {
                value = Strip(value);
                if (value is LocalValue local && values.TryGetValue(local.Variable, out var known)) return known;
                return ManagedValues.Map(value, Resolve);
            }
            bool IsField(ManagedValue value, string name) => value is FieldValue f && f.Receiver.Equals(receiver)
                && f.Field.DeclaringType.Equals(owner) && f.Field.Field.Name == name;
            // 循环退出判断已经读过 Count，紧接着 Clear 可复用这个旧长度；两者之间没有写入或调用。
            if (start == 0 && flow.Predecessors.GetValueOrDefault(block.Address) == 1)
                foreach (var previous in body.Blocks)
                    if (flow.SameRegion(previous.Address, block.Address)
                        && previous.Statements is [ManagedAssignment snapshot, ManagedBranch guard]
                        && ManagedValues.Edges(guard).Any(e => e.Target == block.Address && e.Copies.Count == 0)
                        && IsField(snapshot.Value, "_size")) values[snapshot.Target.Variable] = snapshot.Value;
            bool ReadsChanged(ManagedValue value) => ManagedValues.Walk(value).OfType<FieldValue>()
                .Any(f => zeroed && IsField(f, "_size") || versioned && IsField(f, "_version"));
            bool Assign(ManagedAssignment assignment)
            {
                if (values.ContainsKey(assignment.Target.Variable)) return false;
                // 读取发生在写入之后时不能再当成旧值；局部变量中保存的旧值仍可使用。
                if (ReadsChanged(assignment.Value)) return false;
                var value = Resolve(assignment.Value);
                if (ManagedValues.Walk(value).Any(v => v is not (FieldValue or LocalValue or ArgumentValue or ConstantValue or BinaryValue)
                    || v is FieldValue f && !(IsField(f, "_size") || IsField(f, "_version") || IsField(f, "_items"))
                    || v is BinaryValue { Op: not BinOp.Add })) return false;
                values[assignment.Target.Variable] = value;
                remove.Add(assignment);
                return true;
            }
            using var prefix = flow.Straight(block.Address, start, block.Address).GetEnumerator();
            ManagedBranch? branch = null;
            while (prefix.MoveNext())
            {
                var statement = prefix.Current;
                if (statement is ManagedAssignment assignment && Assign(assignment)) continue;
                if (!zeroed && statement is ManagedStore size && IsField(size.Target, "_size") && Resolve(size.Value) is ConstantValue { Bits: 0 })
                { zeroed = true; remove.Add(size); continue; }
                if (!versioned && statement is ManagedStore version && IsField(version.Target, "_version")
                    && Resolve(version.Value) is BinaryValue { Op: BinOp.Add, Right: ConstantValue { Bits: 1 } } increment && IsField(increment.Left, "_version"))
                { versioned = true; remove.Add(version); continue; }
                branch = statement as ManagedBranch;
                break;
            }
            if (!zeroed || !versioned || branch is null
                || ReadsChanged(branch.Condition) || Resolve(branch.Condition) is not ComparisonValue condition || !IsField(condition.Left, "_size")
                || condition.Right is not ConstantValue limit) continue;
            bool? nonemptyTaken = (condition.Condition, limit.Bits) switch
            {
                (Cond.Sgt, 0) or (Cond.Sge, 1) => true,
                (Cond.Sle, 0) or (Cond.Slt, 1) => false,
                _ => null,
            };
            if (nonemptyTaken is null) continue;
            var filledEdge = nonemptyTaken.Value ? branch.Taken : branch.Fallthrough;
            var emptyEdge = nonemptyTaken.Value ? branch.Fallthrough : branch.Taken;
            // 清理调用留在原保护区，正常退出边可以离开；下面仍须证明两臂具有同一出口。
            if (filledEdge.Copies.Count != 0 || flow.Predecessors.GetValueOrDefault(filledEdge.Target) != 1
                || !flow.SameRegion(block.Address, filledEdge.Target)) continue;
            using var filled = flow.Straight(filledEdge.Target, 0, block.Address).GetEnumerator();
            ManagedStatement? Next()
            {
                while (filled.MoveNext())
                {
                    if (filled.Current is ManagedAssignment assignment && Assign(assignment)) continue;
                    return filled.Current;
                }
                return null;
            }
            if (Next() is not ManagedCall { Result: null, Invocation: { Receiver: null, Arguments.Count: 3 } invocation } arrayClear
                || invocation.Method.Method.Name != "Clear" || invocation.Method.Method.Owner != types.CorlibDefinition("System.Array")
                || invocation.Arguments.Any(ReadsChanged)
                || !IsField(Resolve(invocation.Arguments[0]), "_items") || Resolve(invocation.Arguments[1]) is not ConstantValue { Bits: 0 }
                || !Resolve(invocation.Arguments[2]).Equals(condition.Left)) continue;
            var exit = arrayClear.Tail ? new ManagedReturn(arrayClear.Address, null) : Next();
            var sameExit = exit is ManagedJump jump && jump.Edge.Target == emptyEdge.Target && jump.Edge.Copies.SequenceEqual(emptyEdge.Copies)
                || emptyEdge.Copies.Count == 0 && SameExit(exit, flow.Straight(emptyEdge.Target, 0, block.Address).FirstOrDefault());
            remove.Add(arrayClear);
            if (sameExit) remove.Add(branch);
            else
            {
                // 两臂还有不同的结果或重读时保留原分支；只收回已证明的 Clear 操作。
                if (arrayClear.Tail) continue;
                while (true)
                {
                    var used = body.Blocks.SelectMany(b => b.Statements).Where(s => !remove.Contains(s))
                        .SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
                        .SelectMany(ManagedValues.Walk).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
                    var needed = remove.OfType<ManagedAssignment>().Where(a => used.Contains(a.Target.Variable)).ToArray();
                    if (needed.Length == 0) break;
                    foreach (var assignment in needed) remove.Remove(assignment);
                }
                if (values.Keys.Any(v => !remove.OfType<ManagedAssignment>().Any(a => a.Target.Variable == v)
                    && ManagedValues.Walk(values[v]).OfType<FieldValue>().Any(f => !IsField(f, "_size")))) continue;
            }
            if (body.Blocks.SelectMany(b => b.Statements).Where(s => !remove.Contains(s))
                .SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk)
                .OfType<LocalValue>().Any(l => remove.OfType<ManagedAssignment>().Any(a => a.Target.Variable == l.Variable))) continue;
            var method = new MethodRef(clear, owner.Arguments, []);
            if (!ManagedAccess.Method(types, body.Method.Method.Owner, method, receiver.Type)) continue;
            var call = new ManagedCall(sameExit ? first.Address : branch.Address, new ManagedInvocation(method, receiver, [], true), null, false);
            var rewritten = body with
            {
                Blocks = body.Blocks.Select(b => b with
                {
                    Statements = b.Statements.SelectMany(s => sameExit && ReferenceEquals(s, first) ? new ManagedStatement[] { call }
                        : ReferenceEquals(s, branch) ? sameExit ? [new ManagedJump(branch.Address, emptyEdge)] : [call, branch]
                        : remove.Contains(s) ? [] : [s]).ToArray(),
                }).ToArray(),
            };
            matched(first.Address, method);
            return Prune(rewritten);
        }
        return null;
    }
}
