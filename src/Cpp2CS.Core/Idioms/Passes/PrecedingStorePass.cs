using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class PrecedingStorePass
{
    // 引用自赋值被消去后可只留下屏障；从同一位置读取到屏障之间不能有写入或其他调用。
    internal static bool UnchangedReference(this IdiomState state, Block block, int index, Expr address, Expr value)
    {
        if (value is not Use source) return false;
        var target = state.defs.Expand(address);
        var visited = new HashSet<Block> { block };
        for (var i = index - 1; ; i--)
        {
            if (i < 0)
            {
                if (block.Predecessors is not [var previous] || previous.NormalSuccessors.Count() != 1 || !visited.Add(previous))
                    return false;
                block = previous;
                i = block.Statements.Count;
                continue;
            }
            switch (block.Statements[i])
            {
                case Define define when define.Target == source.Variable:
                    return state.defs.Expand(define.Value) is Load { Width: 64 } load && load.Address == target;
                case Store or Call:
                    return false;
            }
        }
    }

    internal static bool PrecedingStore(this IdiomState state, Block block, int index, Expr address, Expr value)
        => PrecedingStore(state, block, index, address, value, []);

    private static bool PrecedingStore(IdiomState state, Block block, int index, Expr address, Expr value, HashSet<Block> visited)
    {
        if (!visited.Add(block)) return false;
        // 编译器把各路径的写屏障尾合并到汇合块：参数是本块的 φ，逐个前驱核对对应的写入
        if (block.Statements.Take(index).All(s => s is Phi) && (address is Use { Variable: var pa } || value is Use { Variable: var _ }))
        {
            var phis = block.Statements.Take(index).OfType<Phi>().ToDictionary(p => p.Target);
            Expr Along(Expr e, int j) => e is Use { Variable: var v } && phis.TryGetValue(v, out var phi) ? new Use(phi.Sources[j], e.Width) : e;
            if ((address is Use ua && phis.ContainsKey(ua.Variable)) || (value is Use uv && phis.ContainsKey(uv.Variable)))
                return block.Predecessors.Count > 0 && block.Predecessors.Select((p, j) => (p, j)).All(x => x.p.NormalSuccessors.Count() == 1 && PrecedingStore(state, x.p, x.p.Statements.Count, Along(address, x.j), Along(value, x.j), new(visited)));
        }

        var target = state.defs.Expand(address);
        var stored = state.defs.Expand(value);
        bool SameValue(Expr candidate)
        {
            candidate = state.defs.Expand(candidate);
            if (candidate == stored) return true;
            if (candidate is not Use left || stored is not Use right) return false;
            Call? Producer(Variable variable) => state.All.OfType<Call>().FirstOrDefault(c => c.Op is { Kind: OpKind.IsInst, Operand: TypeRef }
                && c.Defines.FirstOrDefault() == variable);
            // 同一对象的运行时类型不变；同一类型测试的结果不受期间的字段写入影响。
            return Producer(left.Variable) is { } a && Producer(right.Variable) is { } b && a.Op == b.Op
                && a.Arguments.Select(state.defs.Expand).SequenceEqual(b.Arguments.Select(state.defs.Expand));
        }
        var (basis, offset) = SplitPass.Split(target);
        // 处于 try 区间的调用自成一块：沿唯一前驱（其唯一正常后继是本块）继续向前找
        for (var i = index - 1; ; i--)
        {
            if (i < 0)
            {
                if (block.Predecessors is not [var previous] || previous.NormalSuccessors.Count() != 1 || !visited.Add(previous))
                    return false;
                block = previous;
                i = block.Statements.Count;
                continue;
            }

            switch (block.Statements[i])
            {
                case Store store when store.Target == address && store.Value == value:
                    return true;
                case Store store when state.defs.Expand(store.Target) == target && SameValue(store.Value):
                    return true;
                // 值为 0 的屏障跟在结构写入（清零或整体复制）之后：该写入覆盖屏障地址处的 8 字节
                case Store store when stored is Const { Value: 0 }:
                    var (storeBasis, storeOffset) = SplitPass.Split(state.defs.Expand(store.Target));
                    var bytes = store.Value.Width / 8;
                    if (target is FrameAddress f && storeBasis is FrameAddress g)
                    {
                        if (g.Offset <= f.Offset && f.Offset + 8 <= g.Offset + bytes)
                            return true;
                    }
                    else if (storeBasis == basis && storeOffset <= offset && offset + 8 <= storeOffset + (ulong)bytes)
                        return true;
                    break;
                case Call { Op.Kind: OpKind.IsInst or OpKind.ThrowIf or OpKind.NullCheck }:
                    // 沿正常返回路径，类型测试与检查不会改写先前的存储。
                    break;
                case Call call when call.Op?.Kind != OpKind.WriteBarrier:
                    return false;
            }
        }
    }
}
