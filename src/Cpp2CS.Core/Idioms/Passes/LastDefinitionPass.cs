using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class LastDefinitionPass
{
    internal static Variable? LastDefinition(this IdiomState state, Block block, Storage storage, int end, ulong boundary)
    {
        Define? dead = null;
        foreach (var (b, d) in state.function.Dead)
            if (b == block && d.Target.Storage == storage && d.Address < boundary && (dead is null || d.Address >= dead.Address))
                dead = d;
        for (var i = end - 1; i >= 0; i--)
        {
            var stmt = block.Statements[i];
            if (dead is not null && dead.Address > stmt.Address)
                return dead.Target;
            switch (stmt)
            {
                case Define d when d.Target.Storage == storage:
                    return d.Target;
                case Phi p when p.Target.Storage == storage:
                    return p.Target;
                case Call c when c.Defines.FirstOrDefault(v => v?.Storage == storage) is { } v:
                    return v;
                // 检查与内联类型检查在通过一侧不调用任何函数；其余（含守卫，慢路径会调用）按调用约定破坏寄存器
                case Call { Op.Kind: OpKind.NullCheck or OpKind.BoundsCheck or OpKind.ThrowIf or OpKind.TypeCheck }:
                    break;
                case Call c when state.owner.calls.Clobbers(c).Contains(storage):
                    return new Variable(storage, -1);
            }
        }

        return dead?.Target;
    }
}
