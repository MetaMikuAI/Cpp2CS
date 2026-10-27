using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>将共享返回或抛出尾部还原到前驱；保留异常区域、边复制与迭代器状态写入。</summary>
internal static class SourceReturns
{
    public static ManagedBody Rewrite(ManagedBody body)
    {
        var returnType = body.Method.Method.ReturnType.Substitute(body.Method.TypeArguments, body.Method.MethodArguments);
        ManagedValue Result(ManagedValue value)
        {
            if (ManagedTypes.PrimitiveName(returnType) != "Boolean") return value;
            var source = value;
            while (source is ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.Truncate } conversion) source = conversion.Operand;
            return source is { Width: 1 } && ManagedTypes.PrimitiveName(source.Type) == "Boolean" ? source : value;
        }
        static bool Pure(ManagedValue value) => value is LocalValue or ArgumentValue or ConstantValue or ComposedValue { Leaves.Count: 0 }
            || value is ConversionValue conversion && Pure(conversion.Operand);
        var addressed = body.Blocks.SelectMany(b => b.Statements).SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
            .SelectMany(ManagedValues.Walk).OfType<AddressValue>().Select(a => a.Target).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
        var method = body.Method.Method;
        var iterator = method.Name == "MoveNext" && !method.IsStatic && method.Parameters.Count == 0
            && method.Owner.Interfaces.OfType<DefinitionRef>().Any(t => t.Definition.FullName == "System.Collections.IEnumerator")
            && method.Owner.CustomAttributes.Any(a => a.Constructor.Owner.FullName == "System.Runtime.CompilerServices.CompilerGeneratedAttribute");
        bool StateWrite(ManagedStatement statement) => iterator && statement is ManagedStore
            { Target: FieldValue { Receiver: ArgumentValue { Index: -1 }, Accessor: null, Field.Field.Name: "<>1__state" } field, Value: var value }
            && field.Field.Field.Owner == method.Owner && Pure(value);
        bool SameRegion(ulong left, ulong right) => body.Regions.All(r => r.Try.Contains(left) == r.Try.Contains(right)
            && r.Handler.Contains(left) == r.Handler.Contains(right));
        var blocks = body.Blocks.ToDictionary(b => b.Address, b => b with
        {
            Statements = b.Statements.Select(s => s is ManagedReturn { Value: { } value } ret ? ret with { Value = Result(value) } : s).ToArray(),
        });
        bool changed;
        do
        {
            changed = false;
            foreach (var address in body.Blocks.Select(b => b.Address).Reverse())
            {
                var block = blocks[address];
                if (block.Statements is { Count: >= 2 } sequence && sequence[^1] is ManagedReturn { Value: LocalValue result } direct
                    && sequence[^2] is ManagedAssignment assignment && assignment.Target.Variable == result.Variable
                    && assignment.Value.Type.Equals(result.Type) && assignment.Value.Width == result.Width
                    && !addressed.Contains(result.Variable) && (Pure(assignment.Value) || assignment.Value is IndirectValue { Address: LocalValue { Type: ByRefRef } }))
                {
                    block = block with { Statements = [.. sequence.Take(sequence.Count - 2), direct with { Value = assignment.Value }] };
                    blocks[address] = block;
                    changed = true;
                }
                if (block.Statements.LastOrDefault() is not ManagedJump jump
                    || blocks[jump.Edge.Target].Statements is not { Count: > 0 } tail) continue;
                if (tail[^1] is ManagedThrow thrown && Pure(thrown.Exception) && SameRegion(address, jump.Edge.Target)
                    && tail.SkipLast(1).All(s => s is ManagedAssignment assignment && Pure(assignment.Value))
                    && jump.Edge.Copies.All(c => Pure(c.Value)))
                {
                    var targets = jump.Edge.Copies.Select(c => c.Target.Variable).ToHashSet();
                    // 无交叉依赖时，同时复制可顺序写入；写入仍保留，外层 catch 可以观察这些局部。
                    if (jump.Edge.Copies.Any(c => ManagedValues.Walk(c.Value).OfType<LocalValue>()
                        .Any(l => targets.Contains(l.Variable) && l.Variable != c.Target.Variable))) continue;
                    blocks[address] = block with { Statements = [.. block.Statements.SkipLast(1),
                        .. jump.Edge.Copies.Select(c => new ManagedAssignment(jump.Address, c.Target, c.Value)),
                        .. tail.SkipLast(1), thrown with { Address = jump.Address }] };
                    changed = true;
                    continue;
                }
                if (tail[^1] is not ManagedReturn { Value: { } value }
                    || tail.Count != 1 && !(tail.Count == 2 && StateWrite(tail[0]) && SameRegion(address, jump.Edge.Target))
                    || jump.Edge.Copies.Any(c => c.Value is not (LocalValue or ArgumentValue or ConstantValue or AddressValue { Target: LocalValue { Type: not ByRefRef } }))) continue;
                var copies = jump.Edge.Copies.ToDictionary(c => c.Target.Variable, c => c.Value);
                // 边复制同时生效：替换成源值之后不再沿本条边递归追踪其他目标。
                ManagedValue Replace(ManagedValue v)
                {
                    var mapped = v is LocalValue l && copies.TryGetValue(l.Variable, out var copy) ? copy : ManagedValues.Map(v, Replace);
                    return mapped is IndirectValue { Address: AddressValue { Target: LocalValue local } } load && load.Type.Equals(local.Type) ? local : mapped;
                }
                var returned = Replace(value);
                // 通过地址读到的是边复制完成后的存储值，不能误用同时复制前的局部快照。
                if (value is IndirectValue && returned is LocalValue selected && copies.ContainsKey(selected.Variable)) continue;
                // 未解析的 ref 读取可能抛异常，只可穿过同一异常区域内的纯跳转。
                if (!Pure(returned) && !(tail.Count == 1 && returned is IndirectValue { Address: LocalValue { Type: ByRefRef } }
                    && jump.Edge.Copies.Count == 0 && SameRegion(address, jump.Edge.Target))) continue;
                // 同一异常区域内，状态写入与返回仍相邻且执行一次；分别代入本条边上的同时复制值。
                blocks[address] = block with { Statements = [.. block.Statements.SkipLast(1),
                    .. tail.Take(tail.Count - 1).Cast<ManagedStore>().Select(s => s with { Value = Replace(s.Value) }),
                    new ManagedReturn(jump.Address, Result(returned))] };
                changed = true;
            }
        } while (changed);
        return body with { Blocks = body.Blocks.Select(b =>
        {
            var block = blocks[b.Address];
            if (!iterator) return block;
            // 共享尾部展开后，相邻的常量状态写入只保留最后一次；中间没有读取、调用或异常点。
            var statements = block.Statements.ToList();
            for (var i = statements.Count - 2; i >= 0; i--)
                if (StateWrite(statements[i]) && StateWrite(statements[i + 1])
                    && statements[i] is ManagedStore { Value: ConstantValue } first
                    && statements[i + 1] is ManagedStore { Value: ConstantValue } second
                    && first.Target.Equals(second.Target)) statements.RemoveAt(i);
            // 指令调度可把捕获局部值的保存插进 current/state 序列。相互独立且不抛出的写入先完成，再连续挂起。
            static bool Scalar(ManagedValue value) => Pure(value) || value is BinaryValue
                { Op: BinOp.Add or BinOp.Sub or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor or BinOp.Shl or BinOp.LShr or BinOp.AShr
                    or BinOp.FAdd or BinOp.FSub or BinOp.FMul or BinOp.FDiv } binary && Scalar(binary.Left) && Scalar(binary.Right);
            for (var i = 0; i < statements.Count - 3; i++)
            {
                if (statements[i] is not ManagedStore { Target: FieldValue { Receiver: ArgumentValue { Index: -1 }, Accessor: null,
                        Field.Field.Name: "<>2__current" } current, Value: var yielded }
                    || current.Field.Field.Owner != method.Owner || !Scalar(yielded)) continue;
                var end = i + 1;
                while (end < statements.Count && statements[end] is ManagedStore
                    { Target: FieldValue { Receiver: ArgumentValue { Index: -1 }, Accessor: null } field, Value: var saved }
                    && field.Field.Field.Owner == method.Owner && field.Field.Field.Name is not ("<>1__state" or "<>2__current")
                    && Scalar(saved)) end++;
                if (end == i + 1 || end + 1 >= statements.Count || !StateWrite(statements[end])
                    || statements[end] is not ManagedStore { Value: ConstantValue }
                    || statements[end + 1] is not ManagedReturn { Value: ConstantValue { Bits: 1 } }) continue;
                var write = statements[i];
                statements.RemoveAt(i);
                statements.Insert(end - 1, write);
                i = end;
            }
            return block with { Statements = statements };
        }).ToArray() };
    }
}
