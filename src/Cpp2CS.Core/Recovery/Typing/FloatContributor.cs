using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery.Typing;

/// <summary>F2 的操作码与签名/位置浮点约束，原 floatingConstraints 的冲突交由求解器保留。</summary>
internal sealed class FloatContributor(TypingInputs input) : ITypeContributor
{
    public string Name => "浮点";
    public void Contribute(TypingContext context, TypeConstraints constraints)
    {
        void Hint(Expr expression, TypeRef type, ulong address, string detail)
        {
            if (context.Types.Kind(type) is not (TypeKind.Float or TypeKind.Double)) return;
            if (expression is Use use) constraints.Requires(use.Variable, type, new(Name, address, detail));
            else if (expression is Select select)
            {
                Hint(select.True, type, address, detail);
                Hint(select.False, type, address, detail);
            }
        }
        foreach (var (expression, type, address, detail) in Operands(context).Concat(UseContributor.Sites(context, input)))
            Hint(expression, type, address, detail);
    }

    internal static IEnumerable<(Expr Expression, TypeRef Type, ulong Address, string Detail)> Operands(TypingContext context)
    {
        TypeRef Floating(int width) => width == 32 ? context.Types.Single : context.Types.Double;
        foreach (var statement in context.Statements)
            foreach (var e in ExprMap.Operands(statement).SelectMany(ExprMap.Walk))
                switch (e)
                {
                    case Binary b when b.Width is 32 or 64 && b.Op is BinOp.FAdd or BinOp.FSub or BinOp.FMul or BinOp.FDiv or BinOp.FMin or BinOp.FMax:
                        yield return (b.Left, Floating(b.Width), statement.Address, b.Op.ToString());
                        yield return (b.Right, Floating(b.Width), statement.Address, b.Op.ToString()); break;
                    case Unary u when u.Width is 32 or 64 && u.Op is UnOp.FNeg or UnOp.FAbs or UnOp.FSqrt or UnOp.FFloor or UnOp.FCeil or UnOp.FTrunc or UnOp.FRoundEven or UnOp.FRoundAway or UnOp.FRoundCurrent:
                        yield return (u.Operand, Floating(u.Width), statement.Address, u.Op.ToString()); break;
                    case Compare c when c.Left.Width is 32 or 64 && c.Cond is >= Cond.FEq and <= Cond.FUne:
                        yield return (c.Left, Floating(c.Left.Width), statement.Address, c.Cond.ToString());
                        yield return (c.Right, Floating(c.Left.Width), statement.Address, c.Cond.ToString()); break;
                    case Ir.Convert c when c.Operand.Width is 32 or 64 && c.Kind is ConvKind.FloatToFloat or ConvKind.FloatToSInt or ConvKind.FloatToUInt:
                        yield return (c.Operand, Floating(c.Operand.Width), statement.Address, c.Kind.ToString()); break;
                }
    }
}
