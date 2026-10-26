using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        // ABI 聚合参数被认回后，其原始寄存器复制可能已无使用；尤其不能写出 null 的托管 ref 局部。
        private static ManagedBody DropUnusedRegisterCopies(ManagedBody body)
        {
            bool Pure(ManagedValue value) => ManagedValues.Walk(value).All(v => v is ConstantValue or LocalValue or ArgumentValue or ConversionValue);
            while (true)
            {
                var used = body.Blocks.SelectMany(b => b.Statements).SelectMany(s => s switch
                {
                    ManagedAssignment a => new[] { a.Value },
                    _ => ManagedValues.Of(s),
                }).Concat(body.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.CopiedValues))
                    .SelectMany(ManagedValues.Walk).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
                var changed = false;
                bool Keep(LocalValue target, ManagedValue value)
                {
                    if (used.Contains(target.Variable) || !Pure(value)) return true;
                    changed = true;
                    return false;
                }
                body = body with { Blocks = body.Blocks.Select(b => b with { Statements = b.Statements
                    .Where(s => s is not ManagedAssignment a || Keep(a.Target, a.Value))
                    .Select(s => ManagedValues.MapEdges(s, edge => edge with { Copies = edge.Copies.Where(c =>
                        Keep(c.Target, c.Value)).ToArray() })).ToArray() }).ToArray() };
                if (!changed) return body;
            }
        }
    }
}
