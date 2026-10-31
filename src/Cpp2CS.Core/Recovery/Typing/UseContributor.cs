using Cpp2CS.Facts;
using Cpp2CS.Ir;
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
        var pending = new Stack<(Expr Expression, TypeRef Type, bool Publish)>();
        var visited = new HashSet<(Variable Variable, int Width, TypeRef Type)>();
        void Hint(Expr expression, TypeRef type, ulong address, string detail)
        {
            // 同一用途中的共享定义只展开一次；显式栈保留左到右顺序，避免长定义链耗尽调用栈。
            visited.Clear();
            pending.Push((expression, type, false));
            var evidence = new TypeEvidence(Name, address, detail);
            while (pending.TryPop(out var next))
            {
                (expression, type, _) = next;
                if (next.Publish && expression is Use required)
                {
                    constraints.Requires(required.Variable, type, evidence);
                    continue;
                }
                if (context.Types.Kind(type) is not (TypeKind.Bool or TypeKind.Int or TypeKind.Reference or TypeKind.Float or TypeKind.Double)) continue;
                switch (expression)
                {
                    case Use u when !context.IsRuntime(u.Variable):
                        if (!visited.Add((u.Variable, u.Width, type))) break;
                        if (values.TryGetValue(u.Variable, out var value) && value is Const constant)
                        {
                            if (context.Types.Kind(type) == TypeKind.Reference)
                            {
                                if (constant.Value != 0 || constant.Width != 64 || u.Width != 64) break;
                            }
                            else if (context.Types.Kind(type) is TypeKind.Float or TypeKind.Double)
                            {
                                if (constant.Width != context.Types.Bits(type) || u.Width != constant.Width) break;
                            }
                            else
                            {
                                if (constant.Width is not (1 or 8 or 16 or 32 or 64)) break;
                                type = Integer(constant.Width, ManagedTypes.IsSigned(type));
                            }
                        }
                        else if (context.Types.Kind(type) is TypeKind.Int or TypeKind.Bool
                            && value is Convert or Binary or Unary)
                        {
                            // 窄整数运算及其寄存器扩展有明确的整数结果；用途同时约束中间值，避免长链每轮只前进一层。
                            // 64 位加法仍可能是指针运算，不据此定型；未知加载也不接受反向猜测。
                            if (ScalarIntegerResult(value))
                                pending.Push((u, Integer(value.Width, ManagedTypes.IsSigned(type)), true));
                            pending.Push((value, type, false));
                            break;
                        }
                        else if (value is Select && (context.Types.Kind(type) is TypeKind.Reference or TypeKind.Int or TypeKind.Bool || FloatingChoice(context, values, u.Variable, type)))
                        {
                            pending.Push((u, type, true));
                            pending.Push((value, type, false));
                            break;
                        }
                        else if (!phis.Contains(u.Variable) && !FloatingChoice(context, values, u.Variable, type)) break;
                        constraints.Requires(u.Variable, type, evidence);
                        break;
                    case Convert c when context.Types.Kind(type) is TypeKind.Int or TypeKind.Bool
                        && c.Kind is ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate && c.Operand.Width is 1 or 8 or 16 or 32 or 64:
                        pending.Push((c.Operand, Integer(c.Operand.Width, c.Kind == ConvKind.SignExtend), false)); break;
                    case Select select:
                        pending.Push((select.False, type, false)); pending.Push((select.True, type, false)); break;
                    case Unary { Op: UnOp.Not or UnOp.Neg } unary when context.Types.Kind(type) is TypeKind.Int or TypeKind.Bool:
                        pending.Push((unary.Operand, Integer(unary.Operand.Width, unary.Op == UnOp.Neg || ManagedTypes.IsSigned(type)), false)); break;
                    case Binary binary when context.Types.Kind(type) is TypeKind.Int or TypeKind.Bool
                        && binary.Op is BinOp.Add or BinOp.Sub or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor or BinOp.SDiv or BinOp.UDiv or BinOp.MulHighS or BinOp.MulHighU:
                        pending.Push((binary.Right, type, false)); pending.Push((binary.Left, type, false)); break;
                    case Binary binary when context.Types.Kind(type) is TypeKind.Int or TypeKind.Bool
                        && binary.Op is BinOp.Shl or BinOp.LShr or BinOp.AShr
                        && binary.Left.Width is 8 or 16 or 32 or 64 && binary.Right.Width is 8 or 16 or 32 or 64:
                        pending.Push((binary.Right, Integer(binary.Right.Width, false), false));
                        pending.Push((binary.Left, Integer(binary.Left.Width, binary.Op == BinOp.AShr || binary.Op == BinOp.Shl && ManagedTypes.IsSigned(type)), false)); break;
                }
            }
        }
        TypeRef Integer(int width, bool signed) => width == 1 ? context.Types.Boolean : context.Types.Integer(width, signed);
        foreach (var (expression, type, address, detail) in Sites(context, input).Concat(FloatContributor.Operands(context)))
            Hint(expression, type, address, detail);
        // φ 的使用可先定型定义结果；继续向其表达式反传，避免常量控制标志停在上一层合流。
        foreach (var define in context.Statements.OfType<Define>())
            if (context.TypeOf(define.Target) is { } type)
                Hint(define.Value, type, define.Address, "已定型定义的操作数");
    }

    private static bool ScalarIntegerResult(Expr expression) => expression switch
    {
        Convert { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate,
            Width: 8 or 16 or 32 or 64, Operand.Width: 1 or 8 or 16 or 32 } conversion when conversion.Width != conversion.Operand.Width => true,
        Binary { Width: 8 or 16 or 32,
            Op: BinOp.Add or BinOp.Sub or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor or BinOp.Shl or BinOp.LShr or BinOp.AShr } => true,
        Binary { Width: 64, Op: BinOp.SDiv or BinOp.UDiv or BinOp.MulHighS or BinOp.MulHighU or BinOp.Shl or BinOp.LShr or BinOp.AShr or BinOp.And or BinOp.Or or BinOp.Xor } => true,
        Unary { Width: 8 or 16 or 32 or 64, Op: UnOp.Not or UnOp.Neg } => true,
        _ => false,
    };

    internal static bool FloatingChoice(TypingContext context, Dictionary<Variable, Expr> values, Variable variable, TypeRef type)
    {
        if (context.Types.Kind(type) is not (TypeKind.Float or TypeKind.Double) || !values.TryGetValue(variable, out var value)) return false;
        var width = context.Types.Bits(type);
        var active = new HashSet<Variable>();
        bool Bits(Expr e)
        {
            if (e.Width != width) return false;
            if (e is Const) return true;
            if (e is Select s) return Bits(s.True) && Bits(s.False);
            if (e is not Use u) return false;
            if (context.TypeOf(u.Variable) == type) return true;
            if (!active.Add(u.Variable) || !values.TryGetValue(u.Variable, out var source)) return false;
            var result = Bits(source);
            active.Remove(u.Variable);
            return result;
        }
        return value is Select && Bits(value);
    }

    internal static IEnumerable<(Expr Expression, TypeRef Type, ulong Address, string Detail)> Sites(TypingContext context, TypingInputs input)
    {
        var expressions = input.Expressions(context);
        var abi = new ManagedAbi(context.Types.Layouts);
        foreach (var (value, type) in input.StackEnumValues) yield return (value, type, 0, "栈上枚举值");
        foreach (var definition in context.Statements.OfType<Define>())
            if (definition.Target.Storage.Bank == Bank.Vec && definition.Value is Convert { Kind: ConvKind.Bitcast, Width: 32 or 64, Operand: Use { Variable.Storage.Bank: Bank.Gpr } bits })
                yield return (bits, context.Types.Integer(bits.Width, false), definition.Address, "FMOV 的整数位型输入");
        foreach (var statement in context.Statements)
            foreach (var conversion in ExprMap.Operands(statement).SelectMany(ExprMap.Walk).OfType<Convert>())
                if (conversion.Kind is ConvKind.SIntToFloat or ConvKind.UIntToFloat && conversion.Operand.Width is 32 or 64)
                    yield return (conversion.Operand, context.Types.Integer(conversion.Operand.Width, conversion.Kind == ConvKind.SIntToFloat), statement.Address, "整数转浮点输入");
        // 窄整数比较给控制标志与计数 φ 提供用途；64 位判空仍可能是引用，不能据此定为整数。
        foreach (var statement in context.Statements)
            foreach (var comparison in ExprMap.Operands(statement).SelectMany(ExprMap.Walk).OfType<Compare>())
                if (comparison.Cond is >= Cond.Eq and <= Cond.Uge && (comparison.Left.Width is 8 or 16 or 32
                    || comparison.Left.Width == 64 && comparison.Cond is Cond.Slt or Cond.Sle or Cond.Sgt or Cond.Sge))
                {
                    var integer = context.Types.Integer(comparison.Left.Width, comparison.Cond is Cond.Slt or Cond.Sle or Cond.Sgt or Cond.Sge);
                    yield return (comparison.Left, integer, statement.Address, "整数比较左值");
                    yield return (comparison.Right, integer, statement.Address, "整数比较右值");
                }
        foreach (var statement in context.Statements)
            foreach (var addition in ExprMap.Operands(statement).SelectMany(ExprMap.Walk).OfType<Binary>().Where(b => b.Op == BinOp.Add && b.Width == 64))
            {
                if (expressions.TypeOf(addition.Left) is PointerRef)
                    yield return (addition.Right, context.Types.Int64, statement.Address, "原生指针字节偏移");
                if (expressions.TypeOf(addition.Right) is PointerRef)
                    yield return (addition.Left, context.Types.Int64, statement.Address, "原生指针字节偏移");
                var terms = Cpp2CS.Idioms.TermsPass.Terms(addition).ToArray();
                if (terms.Where(t => expressions.TypeOf(t) is ArrayRef).ToArray() is [var array])
                    foreach (var offset in terms.Where(t => t != array))
                        yield return (offset, context.Types.Int64, statement.Address, "数组数据字节偏移");
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
                    {
                        if (parameter.Passing == Passing.Registers && context.Types.Kind(parameter.Type) == TypeKind.Struct && abi.Hfa(parameter.Type) is { } hfa)
                        {
                            foreach (var piece in parameter.Pieces)
                                if (registers.TryGetValue(piece.Register, out var component))
                                    yield return (ScalarVectorNarrowing.Low(component, piece.Width), hfa.Width == 32 ? context.Types.Single : context.Types.Double,
                                        call.Address, $"{target} 同质浮点实参 {piece.Register}");
                            continue;
                        }
                        if (parameter is { Passing: Passing.Registers, Pieces.Length: 1 } && registers.TryGetValue(parameter.Pieces[0].Register, out var argument))
                        {
                            // 未读取的参数可能携带另一种标量的寄存器残值，不反向污染实际使用处的类型。
                            if (!ReferenceEquals(parameter, signature.This) && argument is Use unused
                                && context.TypeOf(unused.Variable) is { } native && context.Types.Kind(native) != context.Types.Kind(parameter.Type)
                                && input.UnusedInput(call, target, parameter)) continue;
                            if (ReferenceEquals(parameter, signature.This)
                                && (argument is Unknown or Symbol || expressions.TypeOf(argument) is { } actual && !context.Types.IsAssignable(actual, parameter.Type))
                                && input.UnusedInput(call, target, parameter)) continue;
                            yield return (argument, parameter.Type, call.Address, $"{target} 实参 {parameter.Pieces[0].Register}");
                        }
                    }
                    break;
            }
    }
}
