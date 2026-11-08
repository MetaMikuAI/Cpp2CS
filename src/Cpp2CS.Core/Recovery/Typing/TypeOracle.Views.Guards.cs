using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Ssa;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Typing;

/// <summary>
/// 类型判断之后的视图。对象 o 通过类型判断之后，clang 仍可能经 o 本身访问判断类型的字段
/// （模式变量 o is T t 之后读 t.f，或几条判断路径的尾部合并后共用一次读取）。
/// 读写在 o 的静态类型上定位不到时，沿支配树由近及远取对 o 的判断：isinst&lt;T&gt;(o) 的结果（按它定位），
/// 或内联继承检查 TypeCheck&lt;T&gt;(o 的类) 成立的分支、类指针等于密封类 T 的分支、类指针不是密封类 T 就抛出的检查之后（位置带上视图类型 T，写出为 castclass）。
/// isinst 的结果按启发式使用：假定原生代码只在已知 o 是 T 的路径上按 T 的布局访问 o。
/// </summary>
public sealed partial class TypeOracle
{
    private Dominators? viewDominators;
    private Dictionary<Sym, List<Call>>? typeViews;

    /// <summary>经类型判断的视图定位访问；没有判断或按判断类型也定位不到时为 null。</summary>
    public Location? ViewLocate(Sym address, int width, Stmt site)
    {
        var block = values.BlockOf(site);
        return ViewLocate(address, width, block, block.Statements.IndexOf(site));
    }

    /// <summary>访问若位于 block 的第 position 条语句之前，经类型判断的视图定位。</summary>
    public Location? ViewLocate(Sym address, int width, Block block, int position)
    {
        var (root, offset, index, _) = Decompose(address);
        if (index is not null) return null;
        root = SymTable.Resolve(root);
        foreach (var (type, result) in Guards(root, block, position))
        {
            if (result is not null)
            {
                if (Locate(values.Syms.Binary(BinOp.Add, result, values.Syms.Const(unchecked((ulong)offset), 64), 64), width) is { } viewed) return viewed;
                continue;
            }
            if (type is DefinitionRef reference && ManagedTypes.IsReferenceType(reference)
                && FieldAt(reference, (int)offset, width, false, false) is var (path, fieldType))
                return new(LocationKind.Instance, root, null, 0, null, path, fieldType) { View = reference };
        }
        return null;
    }

    /// <summary>由近及远支配这个位置的、对 root 的类型判断：类型与 isinst 的结果（继承检查没有结果）。</summary>
    private IEnumerable<(TypeRef Type, Sym? Result)> Guards(Sym root, Block block, int position)
    {
        typeViews ??= values.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>()
            .Where(c => c.Op?.Kind == OpKind.IsInst && values.Operands(c).Count > 1 && ClassOperand(c) is not null)
            .GroupBy(c => SymTable.Resolve(values.Operands(c)[1])).ToDictionary(g => g.Key, g => g.ToList());
        viewDominators ??= Dominators.Compute(values.Function);
        var casts = typeViews.GetValueOrDefault(root) ?? [];
        var blocks = values.Function.Blocks;
        for (var current = block; ;)
        {
            var limit = current == block ? position : current.Statements.Count;
            foreach (var call in casts.Where(c => values.BlockOf(c) == current && current.Statements.IndexOf(c) < limit)
                .OrderByDescending(c => current.Statements.IndexOf(c)))
                yield return (ClassOperand(call)!, values.Syms.Result(call, 0, 64));
            // 类指针与密封类不同时抛出（as 之后访问成员的空引用检查）：之后 o 就是这个类。
            for (var i = Math.Min(limit, current.Statements.Count) - 1; i >= 0; i--)
                if (current.Statements[i] is Call { Op.Kind: OpKind.ThrowIf } guard
                    && values.Operands(guard).Skip(1).FirstOrDefault() is { } condition
                    && SymTable.Resolve(condition) is OpSym { Op: { Kind: OperatorKind.Compare, Cond: Cond.Ne }, Args: [var left, var right] }
                    && ClassIdentity(left, right) is var (owner, exact) && ReferenceEquals(SymTable.Resolve(owner), root))
                    yield return (exact, null);
            if (current.Predecessors is [var predecessor] && Checked(predecessor, current, root) is { } tested)
                yield return (tested, null);
            var parent = viewDominators.Idom[current.Index];
            if (parent < 0 || parent == current.Index) yield break;
            current = blocks[parent];
        }
    }

    /// <summary>
    /// 地址里的选择在 block 处已由支配它的分支决定条件时取决定的一路（clang 把按条件取对象或空的选择外提到分支之前）。
    /// 条件值是 SSA 值：支配 block 的块只有一个前驱、经条件分支的一侧进入时，到 block 的每条路径上条件都取这一侧的真假。
    /// </summary>
    public Sym Decided(Sym address, Block block)
    {
        address = SymTable.Resolve(address);
        switch (address)
        {
            case OpSym { Op.Kind: OperatorKind.Select, Args: [var condition, var first, var second] } when Known(condition, block) is { } known:
                return Decided(known ? first : second, block);
            case OpSym { Op: { Kind: OperatorKind.Binary } op, Args: [var left, var right] } binary when op.Binary is BinOp.Add or BinOp.Sub:
                {
                    var (l, r) = (Decided(left, block), Decided(right, block));
                    return ReferenceEquals(l, SymTable.Resolve(left)) && ReferenceEquals(r, SymTable.Resolve(right)) ? binary : values.Syms.Binary(op.Binary, l, r, binary.Width);
                }
            default:
                return address;
        }
    }

    /// <summary>由支配 block 的条件分支决定的 condition 真假；沿支配树找不到时为 null。</summary>
    private bool? Known(Sym condition, Block block)
    {
        viewDominators ??= Dominators.Compute(values.Function);
        for (var current = block; ;)
        {
            if (current.Predecessors is [var predecessor] && predecessor.Statements.LastOrDefault() is Branch branch && branch.Target != branch.Fallthrough
                && Implied(values.Operands(branch)[0], branch.Target == current.Start, condition) is { } known)
                return known;
            var parent = viewDominators.Idom[current.Index];
            if (parent < 0 || parent == current.Index) return null;
            current = values.Function.Blocks[parent];
        }
    }

    /// <summary>predecessor 以继承检查 TypeCheck&lt;T&gt;(root 的类) 的结果或 root 的类指针与密封类 T 的比较分支、successor 是检查成立的一侧时为 T。</summary>
    private TypeRef? Checked(Block predecessor, Block successor, Sym root)
    {
        if (predecessor.Statements.LastOrDefault() is not Branch branch || branch.Target == branch.Fallthrough
            || values.Operands(branch) is not [OpSym { Op.Kind: OperatorKind.Compare, Op.Cond: Cond.Eq or Cond.Ne, Args: [var left, var right] } compare]) return null;
        // 类指针等于密封类的一侧：o 就是这个类。
        if (ClassIdentity(left, right) is var (owner, exact) && ReferenceEquals(SymTable.Resolve(owner), root))
            return successor.Start == (compare.Op.Cond == Cond.Eq ? branch.Target : branch.Fallthrough) ? exact : null;
        if (right is not ConstSym { Value: 0 } || SymTable.Resolve(left) is not ResultSym { Site: { Op.Kind: OpKind.TypeCheck } check }
            || values.Operands(check) is not [_, var klass] || ClassOwner(klass) is not { } checkedOwner
            || !ReferenceEquals(SymTable.Resolve(checkedOwner), root) || check.Op.Operand is not TypeRef type) return null;
        var passed = compare.Op.Cond == Cond.Ne ? branch.Target : branch.Fallthrough;
        return successor.Start == passed ? type : null;
    }
}
