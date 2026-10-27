using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Convert = Cpp2CS.Ir.Convert;

namespace Cpp2CS.Recovery.Typing;

/// <summary>T1 的使用侧约束。反传到常量、φ、整数表达式及引用/浮点选择，不给未知加载或调用结果猜类型。</summary>
internal sealed class UseContributor(TypingInputs input) : ITypeContributor
{
    public string Name => "使用";
    public void Contribute(TypingContext context, TypeConstraints constraints)
    {
        var values = context.Statements.OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        var phis = context.Statements.OfType<Phi>().Select(p => p.Target).ToHashSet();
        var active = new HashSet<Variable>();
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
                    else if (context.Types.Kind(type) is TypeKind.Int or TypeKind.Bool
                        && value is Convert or Binary && active.Add(u.Variable))
                    {
                        Hint(value, type, address, detail);
                        active.Remove(u.Variable);
                        return;
                    }
                    else if (context.Types.Kind(type) == TypeKind.Reference && value is Select && active.Add(u.Variable))
                    {
                        Hint(value, type, address, detail);
                        active.Remove(u.Variable);
                        return;
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
        foreach (var (value, type) in input.StackEnumValues) yield return (value, type, 0, "栈上枚举值");
        // 窄整数比较给控制标志与计数 φ 提供用途；64 位判空仍可能是引用，不能据此定为整数。
        foreach (var statement in context.Statements)
            foreach (var comparison in ExprMap.Operands(statement).SelectMany(ExprMap.Walk).OfType<Compare>())
                if (comparison.Cond is >= Cond.Eq and <= Cond.Uge && comparison.Left.Width is 8 or 16 or 32)
                {
                    var integer = context.Types.Integer(comparison.Left.Width, comparison.Cond is Cond.Slt or Cond.Sle or Cond.Sgt or Cond.Sge);
                    yield return (comparison.Left, integer, statement.Address, "整数比较左值");
                    yield return (comparison.Right, integer, statement.Address, "整数比较右值");
                }
        foreach (var statement in context.Statements)
            switch (statement)
            {
                case Return { Value: { } value } when input.ReturnSupported:
                    if (value is Intrinsic { Name: "diagnostic_return" } pieces
                        && abi.Classify(input.Method, out _)?.Return is { Type: DefinitionRef aggregate } returned
                        && context.Types.Layouts.Of(aggregate) is { } layout && pieces.Arguments.Length == returned.Pieces.Length)
                    {
                        for (var i = 0; i < returned.Pieces.Length; i++)
                            if (layout.Fields.Where(f => f.Offset - RuntimeLayout.ObjectHeaderSize == returned.Pieces[i].Offset
                                && context.Types.Size(f.Type) * 8 == returned.Pieces[i].Width).ToArray() is [var leaf])
                                yield return (pieces.Arguments[i], leaf.Type, statement.Address, "聚合返回叶子");
                    }
                    else yield return (value, input.Method.Method.ReturnType, statement.Address, "返回签名");
                    break;
                case Store store when (!input.Dropped.Contains(store) || input.StoredArguments.ContainsKey(store))
                    && (input.StoredArguments.GetValueOrDefault(store) ?? expressions.LocationType(store.Target, store.Value.Width)) is { } type:
                    yield return (store.Value, type, store.Address, $"写入 {store.Target}:{store.Value.Width}"); break;
                case Call { Op.Kind: OpKind.BoundsCheck, Arguments: [var index, var length] }:
                    // 已识别的数组边界检查提供整数用途，使常量初始化的循环 φ 能开始定型。
                    yield return (index, context.Types.Integer(index.Width, false), statement.Address, "数组边界检查下标");
                    yield return (length, context.Types.Integer(length.Width, false), statement.Address, "数组边界检查长度");
                    break;
                case Call { Op.Kind: OpKind.NewArray, Arguments: [_, var length] }:
                    yield return (length, context.Types.Integer(length.Width, false), statement.Address, "数组分配长度");
                    break;
                case Call { Op.Kind: OpKind.CompareExchangeReference, Arguments: [var location, var value, var comparand] } call
                    when expressions.LocationType(location, 64) is { } type && context.Types.Kind(type) == TypeKind.Reference:
                    yield return (value, type, call.Address, "原子交换的新引用");
                    yield return (comparand, type, call.Address, "原子交换的比较引用");
                    break;
                case Call call when call.Op is null or { Kind: OpKind.CallVirtual or OpKind.CallInterface or OpKind.CallGenericVirtual or OpKind.CallDelegate or OpKind.CallMethodPointer }
                    && context.Resolve(call) is { } target && abi.Classify(target, out _) is { } signature:
                    var registers = call.ArgumentsBySource();
                    if (call.DelegateReceiver is { } delegateReceiver && signature.This is { } delegateThis)
                        yield return (delegateReceiver, delegateThis.Type, call.Address, "委托接收者");
                    foreach (var parameter in signature.Arguments)
                        if (parameter is { Passing: Passing.Registers, Pieces.Length: 1 } && registers.TryGetValue(parameter.Pieces[0].Register, out var argument))
                        {
                            if (ReferenceEquals(parameter, signature.This)
                                && (argument is Unknown or Symbol || expressions.TypeOf(argument) is { } actual && !context.Types.IsAssignable(actual, parameter.Type))
                                && input.UnusedInput(call, target, parameter)) continue;
                            yield return (argument, parameter.Type, call.Address, $"{target} 实参 {parameter.Pieces[0].Register}");
                        }
                    break;
            }
    }
}
