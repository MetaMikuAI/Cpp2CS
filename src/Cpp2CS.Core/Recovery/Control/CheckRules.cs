using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Convert = Cpp2CS.Ir.Convert;

namespace Cpp2CS.Recovery;

internal static class CheckRules
{
    /// <summary>判空与越界的吸收（见类注释第 4 条）。</summary>
    [Analysis("检查吸收", 80, After = ["帧区域"])]
    internal static void Checks(this RecoveryScope ctx)
    {
        // 现有吸收规则只证明普通 CFG；EH 的保护域按语句划分，不能跨界移动抛出点。
        if (ctx.State.Exceptions.exceptionLayout is { Succeeded: true })
            return;
        foreach (var block in ctx.blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call { Op.Kind: OpKind.NullCheck or OpKind.BoundsCheck or OpKind.RunClassConstructor } check)
                    continue;
                var absorbed = check.Op!.Kind switch
                {
                    OpKind.NullCheck => ctx.AbsorbNull(block, i, check.Arguments[0]),
                    OpKind.BoundsCheck => ctx.AbsorbBounds(block, i, check),
                    _ => check.Op.Operand is DefinitionRef type && ctx.Implied(block, i, type),
                };
                if (absorbed)
                    ctx.State.Lowering.dropped.Add(check);
            }
    }

    /// <summary>从 (block, index) 之后沿唯一正常后继（它只有一个前驱）依次列出语句；块末尾可以是跳转，也可以直接落入后继。</summary>
    internal static IEnumerable<Stmt> Straight(Block block, int index) =>
        StraightLine.Following(block, index, StraightLinePolicy.Fallthrough).Select(p => p.Statement);

    internal static IEnumerable<Stmt> Following(Block block, int index) =>
        StraightLine.Following(block, index, StraightLinePolicy.Jump).Select(p => p.Statement);

    internal static bool AbsorbNull(this RecoveryScope ctx, Block block, int index, Expr value)
    {
        foreach (var statement in CheckRules.Following(block, index))
        {
            switch (statement)
            {
                case Phi or Nop or Call { Op.Kind: OpKind.NullCheck }:
                    continue;
                case Define define:
                    if (ExprMap.Walk(define.Value).Any(e => e is Load load && ctx.BaseOf(load.Address) == value))
                        return true;
                    continue;
                case Store store:
                    return ctx.BaseOf(store.Target) == value && !ctx.IsStatic(store.Target);
                case Call call when ConstructionRules.Receiver(call) == value:
                    if (call.Op is null or { Kind: OpKind.CallVirtual or OpKind.CallInterface or OpKind.CallDelegate or OpKind.CallGenericVirtual })
                    {
                        ctx.State.Runtime.virtualCalls.Add(call);
                        return true;
                    }

                    return false;
                default:
                    return false;
            }
        }

        return false;
    }

    internal static bool Implied(this RecoveryScope ctx, Block block, int index, DefinitionRef type)
    {
        bool Static(Expr address) => ctx.Split(address).Base is Symbol { Kind: SymbolKind.StaticFields, Value: DefinitionRef owner } && owner.Equals(type);
        foreach (var statement in CheckRules.Following(block, index))
        {
            switch (statement)
            {
                case Phi or Nop or Call { Op.Kind: OpKind.InitClass }:
                    continue;
                case Define define:
                    // 类构造可能改写其他字段或抛出；不能越过更早的业务读取推迟触发。
                    if (ExprMap.Walk(define.Value).OfType<Load>().FirstOrDefault() is { } load)
                        return Static(load.Address);
                    continue;
                case Store store:
                    return !ExprMap.Walk(store.Value).Any(e => e is Load) && Static(store.Target);
                // beforefieldinit 静态调用不保证触发初始化；原生显式初始化必须保留。
                case Call { Op: null, Kind: CallKind.Direct or CallKind.Tail, Target: Const target } call:
                    return !call.Arguments.SelectMany(ExprMap.Walk).Any(e => e is Load) && ctx.facts.EntriesAt(target.Value).Any(e => e.Method is { Method: var m } && m.Owner == type.Definition && (m.IsStatic && (m.Owner.Attributes & System.Reflection.TypeAttributes.BeforeFieldInit) == 0 || m.Name == ".ctor" && !(m.Owner.IsValueType && (m.Owner.Attributes & System.Reflection.TypeAttributes.BeforeFieldInit) != 0)));
                default:
                    return false;
            }
        }

        return false;
    }

    internal static bool AbsorbBounds(this RecoveryScope ctx, Block block, int index, Call check)
    {
        if (check.Arguments is not [var checkedIndex, var length] || ctx.BaseOf(ctx.StripLength(length)) is not { } array)
            return false;
        foreach (var statement in CheckRules.Following(block, index))
        {
            switch (statement)
            {
                case Phi or Nop:
                    continue;
                case Define define:
                    if (ExprMap.Walk(define.Value).OfType<Load>().Any(l => ctx.ElementOf(l.Address) is var (a, x) && a == array && ctx.SameIndex(x, checkedIndex)))
                        return true;
                    continue;
                case Store store:
                    return ctx.ElementOf(store.Target) is var (a2, x2) && a2 == array && ctx.SameIndex(x2, checkedIndex);
                default:
                    return false;
            }
        }

        return false;
    }

    internal static Expr StripLength(this RecoveryScope ctx, Expr length)
    {
        if (length is Use u && ctx.values.TryGetValue(u.Variable, out var value))
            length = value;
        while (length is Convert { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate } c)
            length = c.Operand;
        return length is Load { Address: var address } && ctx.Split(address).Offset == RuntimeLayout.ArrayMaxLength ? address : new Unknown("length", 64);
    }

    internal static bool SameIndex(this RecoveryScope ctx, Expr element, Expr checkedIndex)
    {
        Expr Strip(Expr e)
        {
            while (true)
            {
                if (e is Convert { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend } c)
                    e = c.Operand;
                else if (e is Use { Width: < 64 } u)
                    return new Use(u.Variable, u.Variable.Width);
                else
                    return e;
            }
        }

        return Strip(element) == Strip(checkedIndex);
    }
}
