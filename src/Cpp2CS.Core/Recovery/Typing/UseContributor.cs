using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Convert = Cpp2CS.Ir.Convert;

namespace Cpp2CS.Recovery.Typing;

/// <summary>T1 的使用侧约束。只反传到常量、φ、整数表达式与已证的浮点选择，不给未知加载或调用结果猜类型。</summary>
internal sealed class UseContributor(TypingInputs input) : ITypeContributor
{
    public string Name => "使用";
    public void Contribute(TypingContext context, TypeConstraints constraints)
    {
        var values = context.Statements.OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        var phis = context.Statements.OfType<Phi>().Select(p => p.Target).ToHashSet();
        void Hint(Expr expression, TypeRef type, ulong address, string detail)
        {
            if (context.Types.Kind(type) is not (TypeKind.Bool or TypeKind.Int or TypeKind.Reference or TypeKind.Float or TypeKind.Double)) return;
            switch (expression)
            {
                case Use u when !context.IsRuntime(u.Variable):
                    if (values.TryGetValue(u.Variable, out var value) && value is Const constant)
                    {
                        if (context.Types.Kind(type) == TypeKind.Reference)
                        {
                            if (constant.Value != 0 || constant.Width != 64 || u.Width != 64) return;
                        }
                        else if (context.Types.Kind(type) is TypeKind.Float or TypeKind.Double)
                        {
                            if (constant.Width != context.Types.Bits(type) || u.Width != constant.Width) return;
                        }
                        else
                        {
                            if (constant.Width is not (1 or 8 or 16 or 32 or 64)) return;
                            type = Integer(constant.Width, ManagedTypes.IsSigned(type));
                        }
                    }
                    else if (!phis.Contains(u.Variable) && !FloatingChoice(context, values, u.Variable, type)) return;
                    constraints.Requires(u.Variable, type, new(Name, address, detail));
                    break;
                case Convert c when context.Types.Kind(type) is TypeKind.Int or TypeKind.Bool
                    && c.Kind is ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate && c.Operand.Width is 1 or 8 or 16 or 32 or 64:
                    Hint(c.Operand, Integer(c.Operand.Width, c.Kind == ConvKind.SignExtend), address, detail); break;
                case Select select:
                    Hint(select.True, type, address, detail); Hint(select.False, type, address, detail); break;
                case Binary binary when context.Types.Kind(type) is TypeKind.Int or TypeKind.Bool
                    && binary.Op is BinOp.Add or BinOp.Sub or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor:
                    Hint(binary.Left, type, address, detail); Hint(binary.Right, type, address, detail); break;
            }
        }
        TypeRef Integer(int width, bool signed) => width == 1 ? context.Types.Boolean : context.Types.Integer(width, signed);
        foreach (var (expression, type, address, detail) in Sites(context, input).Concat(FloatContributor.Operands(context)))
            Hint(expression, type, address, detail);
    }

    internal static bool FloatingChoice(TypingContext context, Dictionary<Variable, Expr> values, Variable variable, TypeRef type)
    {
        if (context.Types.Kind(type) is not (TypeKind.Float or TypeKind.Double) || !values.TryGetValue(variable, out var value)) return false;
        var width = context.Types.Bits(type);
        bool Bits(Expr e) => e.Width == width && (e is Const || e is Use u && context.TypeOf(u.Variable) == type || e is Select s && Bits(s.True) && Bits(s.False));
        return value is Select && Bits(value);
    }

    internal static IEnumerable<(Expr Expression, TypeRef Type, ulong Address, string Detail)> Sites(TypingContext context, TypingInputs input)
    {
        var expressions = input.Expressions(context);
        var abi = new ManagedAbi(context.Types.Layouts);
        foreach (var statement in context.Statements)
            switch (statement)
            {
                case Return { Value: { } value } when input.ReturnSupported:
                    yield return (value, input.Method.Method.ReturnType, statement.Address, "返回签名"); break;
                case Store store when !input.Dropped.Contains(store) && expressions.LocationType(store.Target, store.Value.Width) is { } type:
                    yield return (store.Value, type, store.Address, $"写入 {store.Target}:{store.Value.Width}"); break;
                case Call { Op.Kind: OpKind.BoundsCheck, Arguments: [var index, var length] }:
                    // 已识别的数组边界检查提供整数用途，使常量初始化的循环 φ 能开始定型。
                    yield return (index, context.Types.Integer(index.Width, false), statement.Address, "数组边界检查下标");
                    yield return (length, context.Types.Integer(length.Width, false), statement.Address, "数组边界检查长度");
                    break;
                case Call call when call.Op is null or { Kind: OpKind.CallVirtual or OpKind.CallInterface }
                    && context.Resolve(call) is { } target && abi.Classify(target, out _) is { } signature:
                    var registers = call.ArgumentsBySource();
                    foreach (var parameter in signature.Arguments)
                        if (parameter is { Passing: Passing.Registers, Pieces.Length: 1 } && registers.TryGetValue(parameter.Pieces[0].Register, out var argument))
                            yield return (argument, parameter.Type, call.Address, $"{target} 实参 {parameter.Pieces[0].Register}");
                    break;
            }
    }
}
