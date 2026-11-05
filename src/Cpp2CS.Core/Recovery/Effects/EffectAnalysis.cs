using Cpp2CS.Ir;
using Cpp2CS.Machine.Algebra;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Control;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Effects;

/// <summary>
/// 副作用与异常的次序模型。原生代码的显式检查与类初始化可以并入随后的 IL 操作，条件是两点之间的语句对可观察行为透明：
/// 没有副作用，且抛出的异常不改变结果。三种证明共用同一条直线路径、同一读取异常分类与非空事实：
/// 判空被随后经同一对象的访问吸收；越界检查被随后对同一数组同一下标的元素访问吸收；显式类构造被随后按 IL 语义触发同一初始化的访问代替。
/// </summary>
internal sealed class EffectAnalysis(ValueModel values, TypeOracle oracle, IReadOnlyList<ExceptionRegionPlan> regions)
{
    private static readonly StraightLinePolicy flow = new(_ => true, true, false);

    private readonly MachineEffects semantics = new(values, oracle);

    /// <summary>
    /// (block, index) 之后的直线路径：跨块只进入唯一的正常后继，且后继只有这一个前驱。
    /// Guarded 表示该语句与起点的异常去向相同（同一处理入口，入口 φ 在两条异常边上取同一个值），在两处抛出的异常对处理块不可区分；
    /// 没有异常边的块也可经过，但其中的语句只能不抛出、无副作用（调用方按 Guarded 判断）。
    /// </summary>
    private IEnumerable<(Stmt Statement, bool Guarded)> Following(Block block, int index)
    {
        var origin = block;
        foreach (var (next, statement) in StraightLine.Following(block, index - 1, flow))
        {
            var guarded = next == origin || SameUnwind(origin, next);
            if (!guarded && next.Handler is not null) yield break;
            if (statement is not (Nop or Phi or Ir.Jump)) yield return (statement, guarded);
        }
    }

    /// <summary>
    /// 不抛出、无副作用：纯定义（其中的读取都不抛出）与无 IL 效果的运行时操作。分派查找在 IL 中不存在（并入随后的 callvirt），也算在内。
    /// </summary>
    private bool Transparent(Stmt statement, IReadOnlySet<Sym> nonNull) =>
        semantics.Statement(statement, nonNull).CanDiscard;

    internal bool SameUnwind(Block a, Block b)
    {
        // 不含原生抛出点的块没有异常边；移动过去的 IL 检查仍处于相同的托管异常区域，处理入口的复制已在原抛出点保存。
        if (a.Handler is not null && b.Handler is null && regions.All(r => r.Try.Contains(a) == r.Try.Contains(b) && r.Handler.Contains(a) == r.Handler.Contains(b)))
            return true;
        if (a.Handler != b.Handler) return false;
        if (a.Handler is not { } pad) return true;
        var (i, j) = (pad.Predecessors.IndexOf(a), pad.Predecessors.IndexOf(b));
        return i >= 0 && j >= 0 && pad.Statements.OfType<Phi>().All(p => ReferenceEquals(values.Of(p.Sources[i]), values.Of(p.Sources[j])));
    }

    /// <summary>
    /// 在 (block, index) 处已知非空的对象：沿唯一前驱链已执行完的判空、经该对象的读写（未抛出即非空）、分配的结果，
    /// 以及进入这条链的分支条件（与 0 比较的不等一侧）。
    /// </summary>
    private HashSet<Sym> NonNull(Block block, int index)
    {
        var known = new HashSet<Sym>();
        void Executed(Stmt statement)
        {
            if (statement is Call { Op.Kind: OpKind.NullCheck } check && values.Operands(check) is [_, var checkedValue, ..]) known.Add(SymTable.Resolve(checkedValue));
            if (statement is Call { Op.Kind: OpKind.NewObject or OpKind.NewArray or OpKind.Box } allocation) known.Add(values.Syms.Result(allocation, 0, 64));
            foreach (var read in values.ReadsAt(statement)) known.Add(oracle.Decompose(read.Address).Root);
            if (statement is Store store) known.Add(oracle.Decompose(values.Operands(store)[0]).Root);
        }
        var visited = new HashSet<Block>();
        while (visited.Add(block))
        {
            for (var i = Math.Min(index, block.Statements.Count) - 1; i >= 0; i--) Executed(block.Statements[i]);
            if (block.Predecessors.Count != 1) break;
            var from = block.Predecessors[0];
            if (!from.NormalSuccessors.Contains(block)) break;
            if (from.Statements.LastOrDefault() is Ir.Branch branch && values.Operands(branch) is [var condition]
                && SymTable.Resolve(condition) is OpSym { Op: { Kind: OperatorKind.Compare } test, Args: [var tested, ConstSym { Value: 0 }] }
                && test.Cond is Cond.Eq or Cond.Ne && branch.Target != branch.Fallthrough)
            {
                var taken = block.Start == branch.Target;
                if (taken == (test.Cond == Cond.Ne)) known.Add(SymTable.Resolve(tested));
            }
            block = from;
            index = block.Statements.Count;
        }
        return known;
    }

    /// <summary>
    /// 判空被吸收：直线路径上随后第一个经 target 的访问（字段、元素、实例调用的接收者、写入）对 null 抛出同一异常。
    /// 两点之间只允许无副作用的语句与只可能抛出 NullReferenceException 的读取：无论哪个对象为 null，两种写法都在任何副作用之前抛出同一种异常。
    /// </summary>
    public bool Absorbed(Block block, int index, Sym target)
    {
        var nonNull = NonNull(block, index);
        foreach (var (statement, guarded) in Following(block, index))
        {
            if (!guarded)
            {
                if (Transparent(statement, nonNull)) continue;
                return false;
            }
            // 读对象头用于类型判断时，下降后不留下解引用（isinst 对 null 不抛出），不能吸收判空；用于分派时并入随后的 callvirt。
            bool TypeTest(ReadSym read) => oracle.Decompose(read.Address) is (var root, 0, null, _) && oracle.TypeOf(root) is { } type && ManagedTypes.IsReferenceType(type)
                && Following(block, index).Select(f => f.Statement).OfType<Call>().FirstOrDefault() is { Op.Kind: OpKind.ThrowIf or OpKind.TypeCheck or OpKind.IsInst };
            var reads = values.ReadsAt(statement).Select(r => semantics.Read(r, nonNull)).ToArray();
            if (values.ReadsAt(statement).Any(r => ReferenceEquals(semantics.Read(r, nonNull).Root, target) && !TypeTest(r))) return true;
            if (reads.Any(r => (r.Effects.Exceptions & ~ExceptionEffect.NullReference) != 0)) return false;
            switch (statement)
            {
                case Define when (semantics.Statement(statement, nonNull).Exceptions & ~ExceptionEffect.NullReference) == 0
                    && (semantics.Statement(statement, nonNull).Kinds & ~EffectKind.Read) == 0: continue;
                case Store store: return ReferenceEquals(oracle.Decompose(values.Operands(store)[0]).Root, target);
                case Call { Op: null } call:
                    // 直接调用可覆盖的虚方法可能是 base 调用，不能为了判空改成动态分派；其他方法 IL 里本来就是 callvirt。
                    return oracle.Callee(call) is { Method: { IsStatic: false, IsOverridable: false } }
                        && call.Arguments.Length > 0 && ReferenceEquals(SymTable.Resolve(values.Operands(call)[1]), target);
                // 分派调用在 IL 中是对接收者的 callvirt；分派查找并入其中，对象为 null 时只抛出 NullReferenceException。
                case Call { Op.Kind: OpKind.CallVirtual or OpKind.CallInterface or OpKind.CallGenericVirtual or OpKind.CallDelegate or OpKind.InvokeVirtualGeneric } dispatch:
                    return dispatch.Arguments.Length > 0 && ReferenceEquals(SymTable.Resolve(values.Operands(dispatch)[1]), target);
                case Call call when (MachineEffects.Operation(call).Exceptions & ~ExceptionEffect.NullReference) == 0
                    && (MachineEffects.Operation(call).Kinds & ~EffectKind.Read) == 0: continue;
                default: return false;
            }
        }
        return false;
    }

    /// <summary>判空的对象在此处已知非空：检查不会失败。</summary>
    public bool KnownNonNull(Block block, int index, Sym target) => NonNull(block, index).Contains(target);

    /// <summary>
    /// 越界检查被吸收：直线路径上随后第一个有副作用或可能抛出的语句是对同一数组、同一下标的元素读写（ldelem/stelem 自行检查下标，III.4.7）。
    /// 两点之间只允许不抛出的语句。length 是该数组长度的读取。
    /// </summary>
    public bool BoundsAbsorbed(Block block, int index, Sym position, Sym length)
    {
        if (SymTable.Resolve(length) is not ReadSym lengthRead || oracle.Locate(lengthRead.Address, lengthRead.Width) is not { Kind: LocationKind.Length, Base: { } array }) return false;
        var wanted = TypeOracle.ArrayIndex(position);
        bool Same(Sym address, int width) => oracle.Locate(address, width) is { Kind: LocationKind.Element } element && ReferenceEquals(SymTable.Resolve(element.Base!), SymTable.Resolve(array))
            && (element.Index is { } at ? ReferenceEquals(TypeOracle.ArrayIndex(at), wanted) : wanted is ConstSym c && c.Value == (ulong)element.ConstantIndex);
        var nonNull = NonNull(block, index);
        nonNull.Add(SymTable.Resolve(array));
        foreach (var (statement, guarded) in Following(block, index))
        {
            if (!guarded)
            {
                if (Transparent(statement, nonNull)) continue;
                return false;
            }
            var reads = values.ReadsAt(statement).ToArray();
            if (reads.Any(r => Same(r.Address, r.Width))) return true;
            if (reads.Any(r => semantics.Read(r, nonNull).Effects.MayThrow)) return false;
            switch (statement)
            {
                case Define when Transparent(statement, nonNull): continue;
                case Store store: return Same(values.Operands(store)[0], store.Value.Width);
                case Call call when MachineEffects.Operation(call).CanDiscard: continue;
                default: return false;
            }
        }
        return false;
    }

    /// <summary>
    /// 直线路径上随后第一个有副作用的语句按 IL 语义触发 owner 的类初始化（ECMA-335 II.10.5.3）：访问 owner 的静态字段；
    /// 调用非 beforefieldinit 的 owner 的静态方法或构造函数。类初始化本身有副作用，两点之间只允许不抛出的语句。
    /// </summary>
    public bool Initializes(Block block, int index, TypeRef owner)
    {
        var precise = owner is DefinitionRef d && (d.Definition.Attributes & System.Reflection.TypeAttributes.BeforeFieldInit) == 0;
        bool Static(Sym address, int width) => oracle.Locate(address, width) is { Kind: LocationKind.Static, Owner: { } o } && o.Equals(owner);
        var nonNull = NonNull(block, index);
        foreach (var (statement, guarded) in Following(block, index))
        {
            if (!guarded)
            {
                if (Transparent(statement, nonNull)) continue;
                return false;
            }
            var reads = values.ReadsAt(statement).ToArray();
            if (reads.Length > 0 && Static(reads[0].Address, reads[0].Width)) return true;
            if (reads.Any(r => semantics.Read(r, nonNull).Effects.MayThrow)) return false;
            switch (statement)
            {
                case Define when Transparent(statement, nonNull): continue;
                case Store store: return Static(values.Operands(store)[0], store.Value.Width);
                case Call call when MachineEffects.Operation(call).CanDiscard: continue;
                case Call { Op: null } call when oracle.Callee(call) is { } callee:
                    return precise && callee.DeclaringType.Equals(owner) && (callee.Method.IsStatic || callee.Method.Name == ".ctor");
                default: return false;
            }
        }
        return false;
    }
}
