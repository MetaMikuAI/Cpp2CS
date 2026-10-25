using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>将共享返回尾部还原到前驱；迭代器保留对应状态写入，布尔结果不保留寄存器扩展包装。</summary>
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
        static bool Pure(ManagedValue value) => value is LocalValue or ArgumentValue or ConstantValue
            || value is ConversionValue conversion && Pure(conversion.Operand);
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
                if (block.Statements.LastOrDefault() is not ManagedJump jump
                    || blocks[jump.Edge.Target].Statements is not { Count: > 0 } tail
                    || tail[^1] is not ManagedReturn { Value: { } value } || !Pure(value)
                    || tail.Count != 1 && !(tail.Count == 2 && StateWrite(tail[0]) && SameRegion(address, jump.Edge.Target))
                    || jump.Edge.Copies.Any(c => c.Value is not (LocalValue or ArgumentValue or ConstantValue))) continue;
                var copies = jump.Edge.Copies.ToDictionary(c => c.Target.Variable, c => c.Value);
                // 边复制同时生效：替换成源值之后不再沿本条边递归追踪其他目标。
                ManagedValue Replace(ManagedValue v) => v is LocalValue l && copies.TryGetValue(l.Variable, out var copy)
                    ? copy : ManagedValues.Map(v, Replace);
                // 同一异常区域内，状态写入与返回仍相邻且执行一次；分别代入本条边上的同时复制值。
                blocks[address] = block with { Statements = [.. block.Statements.SkipLast(1),
                    .. tail.Take(tail.Count - 1).Cast<ManagedStore>().Select(s => s with { Value = Replace(s.Value) }),
                    new ManagedReturn(jump.Address, Result(Replace(value)))] };
                changed = true;
            }
        } while (changed);
        return body with { Blocks = body.Blocks.Select(b => blocks[b.Address]).ToArray() };
    }
}
