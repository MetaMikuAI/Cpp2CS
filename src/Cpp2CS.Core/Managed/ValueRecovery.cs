using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

/// <summary>
/// 从方法签名、字段布局和已知调用传播值类型。内存读取保留在原定义处，使用处只引用局部值，避免移动副作用。
/// 不能确定的值返回 null，并保留原因；不把机器地址或未知位型伪装为托管对象。
/// </summary>
public sealed partial class ValueRecovery
{
    private readonly RecoverySession session;
    private readonly PreparedMethod method;
    private readonly ManagedTypes types;
    private readonly Dictionary<Storage, ArgumentValue> arguments = new();
    private readonly Dictionary<Variable, (TypeRef Type, int Width)> locals = new();
    public IReadOnlyDictionary<Variable, (TypeRef Type, int Width)> Locals => locals;
    public string? SignatureProblem { get; }

    public ValueRecovery(RecoverySession session, PreparedMethod method)
    {
        this.session = session;
        this.method = method;
        types = session.Types;
        var signature = session.Abi.Classify(method.Method, out var problem);
        SignatureProblem = problem;
        if (signature is not null)
        {
            if (signature.This is { } self) Bind(self, -1, "this");
            for (var i = 0; i < signature.Parameters.Length; i++) Bind(signature.Parameters[i], i, method.Method.Method.Parameters[i].Name);
        }
        foreach (var call in method.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>())
        {
            if (Target(call) is not { } target || session.Abi.Classify(target, out _)?.Return is not
                { Passing: Passing.Registers, Pieces: [var piece] } result) continue;
            var index = Array.IndexOf(call.Results, piece.Register);
            if (index >= 0 && index < call.Defines.Length && call.Defines[index] is { } variable)
                locals[variable] = (result.Type, piece.Width);
        }
        Infer();
    }

    private void Bind(AbiValue value, int index, string name)
    {
        if (value is not { Passing: Passing.Registers, Pieces: [var piece] } || piece.Offset != 0) return;
        arguments[piece.Register] = new ArgumentValue(index, name, value.Type, piece.Width);
    }

    private ManagedValue? Variable(Variable variable, int width, out string? problem)
    {
        ManagedValue? value = variable.Version == 0
            ? arguments.GetValueOrDefault(variable.Storage)
            : locals.TryGetValue(variable, out var local) ? new LocalValue(variable, local.Type, local.Width) : null;
        if (value is null) return Fail($"未确定变量 {variable}", out problem);
        if (width == value.Width) { problem = null; return value; }
        if (width < value.Width && Numeric(value.Type) && Integer(width) is { } integer)
        {
            problem = null;
            return new ConversionValue(ConvKind.Truncate, value, integer, width);
        }
        if (width > value.Width && width <= variable.Width && Numeric(value.Type) && Integer(width) is { } wide
            && ZeroHigh(variable, value.Width))
        {
            problem = null;
            return new ConversionValue(ConvKind.ZeroExtend, value, wide, width);
        }
        return Fail($"变量 {variable} 的有效位宽 {value.Width} 与读取 {width} 不符", out problem);
    }

    public ManagedValue? Recover(Expr expression, out string? problem)
    {
        problem = null;
        switch (expression)
        {
            case Use use: return Variable(use.Variable, use.Width, out problem);
            case Const constant when Integer(constant.Width) is { } type:
                return new ConstantValue(constant.Value, type, constant.Width);
            case Load load: return Location(load.Address, load.Width, out problem);
            case Ir.Convert conversion:
            {
                if (Recover(conversion.Operand, out problem) is not { } operand) return null;
                var target = NumericResult(conversion);
                if (target is null || !Numeric(operand.Type)) return Fail("未支持的位型转换", out problem);
                return new ConversionValue(conversion.Kind, operand, target, conversion.Width);
            }
            case Binary binary:
            {
                if (Recover(binary.Left, out problem) is not { } left || Recover(binary.Right, out problem) is not { } right) return null;
                if (!Numeric(left.Type) || !Numeric(right.Type)) return Fail("对象地址运算尚未还原", out problem);
                var type = NumericResult(binary);
                if (type is null) return Fail("未支持的运算位宽", out problem);
                return new BinaryValue(binary.Op, left, right, type, binary.Width);
            }
            case Unary unary:
            {
                if (Recover(unary.Operand, out problem) is not { } operand) return null;
                if (!Numeric(operand.Type)) return Fail("非数值一元运算", out problem);
                var type = NumericResult(unary);
                return type is null ? Fail("未支持的一元运算位宽", out problem) : new UnaryValue(unary.Op, operand, type, unary.Width);
            }
            case Compare compare:
            {
                if (Recover(compare.Left, out problem) is not { } left || Recover(compare.Right, out problem) is not { } right) return null;
                if (!Numeric(left.Type) || !Numeric(right.Type))
                {
                    if (compare.Cond is not (Cond.Eq or Cond.Ne)) return Fail("非数值关系比较", out problem);
                    if (ManagedTypes.IsReferenceType(left.Type) && right is ConstantValue { Bits: 0 })
                        right = new ConstantValue(0, left.Type, 64);
                    else if (ManagedTypes.IsReferenceType(right.Type) && left is ConstantValue { Bits: 0 })
                        left = new ConstantValue(0, right.Type, 64);
                    else if (!ManagedTypes.IsReferenceType(left.Type) || !ManagedTypes.IsReferenceType(right.Type))
                        return Fail("无法比较的类型", out problem);
                }
                return new ComparisonValue(compare.Cond, left, right, types.Boolean);
            }
            case Select select:
            {
                if (Recover(select.Condition, out problem) is not { } condition || Recover(select.True, out problem) is not { } yes
                    || Recover(select.False, out problem) is not { } no) return null;
                if (yes.Type != no.Type) return Fail("条件值类型尚未合并", out problem);
                return new ChoiceValue(condition, yes, no, yes.Type, select.Width);
            }
            case Logical logical:
            {
                if (Recover(logical.Left, out problem) is not { } left || Recover(logical.Right, out problem) is not { } right) return null;
                return new BooleanValue(logical.IsAnd, left, right, types.Boolean);
            }
            case Not not:
            {
                return Recover(not.Operand, out problem) is { } operand ? new NegatedValue(operand, types.Boolean) : null;
            }
            case Unknown unknown: return Fail($"未知机器值: {unknown.Reason}", out problem);
            case FrameAddress: return Fail("栈对象尚未还原", out problem);
            default: return Fail($"未支持表达式 {expression.GetType().Name}", out problem);
        }
    }

    /// <summary>把内存位置恢复为实例字段或托管引用解引用，可用于读取和写入。</summary>
    public ManagedValue? Location(Expr address, int width, out string? problem)
    {
        long offset = 0;
        if (address is Binary { Op: BinOp.Add, Right: Const c } add)
        {
            offset = c.Signed;
            address = add.Left;
        }
        if (Recover(address, out problem) is not { } receiver) return null;
        var type = receiver.Type;
        if (type is ByRefRef byRef)
        {
            type = byRef.Element;
            if (offset == 0 && types.Size(type) * 8 == width && types.Kind(type) != ValueKind.Struct)
                return new IndirectValue(receiver, type, width);
        }
        else if (!ManagedTypes.IsReferenceType(type)) return Fail("内存基址没有对象或托管引用类型", out problem);
        if (offset is < 0 or > int.MaxValue || width <= 0 || width % 8 != 0
            || types.FieldPath(type, (int)offset, width / 8) is not { } path) return Fail($"字段位置未匹配 {type}+{offset}:{width}", out problem);
        foreach (var field in path) receiver = new FieldValue(receiver, field.Field, field.Type, types.Size(field.Type) * 8);
        return receiver;
    }

    private MethodRef? Target(Call call) => session.Resolver.Resolve(call) is ManagedCallee { Owners: [var owner] } ? owner.Method : null;

    public ManagedInvocation? Invocation(Call call, out string? problem)
    {
        problem = null;
        if (Target(call) is not { } target) { problem = "调用目标不是唯一托管方法"; return null; }
        if (session.Abi.Classify(target, out problem) is not { } signature) return null;
        ManagedValue? self = null;
        if (signature.This is { } receiver)
        {
            self = Argument(receiver, call, out problem);
            if (self is null) return null;
        }
        var values = new List<ManagedValue>();
        foreach (var parameter in signature.Parameters)
        {
            if (Argument(parameter, call, out problem) is not { } value) return null;
            values.Add(value);
        }
        return new ManagedInvocation(target, self, values);
    }

    private ManagedValue? Argument(AbiValue argument, Call call, out string? problem)
    {
        if (argument is not { Passing: Passing.Registers, Pieces: [var piece] }) return Fail("聚合或栈调用参数尚未还原", out problem);
        var index = Array.IndexOf(call.Sources, piece.Register);
        if (index < 0 || index >= call.Arguments.Length) return Fail("调用参数缺少来源", out problem);
        var native = Fold.Convert(ConvKind.Truncate, call.Arguments[index], piece.Width);
        return RecoverAs(native, argument.Type, out problem);
    }

    public ManagedValue? RecoverAs(Expr native, TypeRef expected, out string? problem)
    {
        if (native is Use use && ManagedTypes.IsReferenceType(expected) && IsZero(use.Variable))
        {
            problem = null;
            return new ConstantValue(0, expected, 64);
        }
        if (Recover(native, out problem) is not { } value) return null;
        if (value.Type == expected) return value;
        if (Numeric(value.Type) && Numeric(expected) && types.Size(expected) * 8 == value.Width)
            return new ConversionValue(ConvKind.Bitcast, value, expected, value.Width);
        if (value is ConstantValue { Bits: 0 } && ManagedTypes.IsReferenceType(expected)) return new ConstantValue(0, expected, 64);
        if (types.IsAssignable(value.Type, expected)) return value;
        return Fail($"值类型不符 {value.Type} → {expected}", out problem);
    }

    private bool Numeric(TypeRef type) => types.Kind(type) is ValueKind.Bool or ValueKind.Int or ValueKind.Float or ValueKind.Double;
    private TypeRef? Integer(int width, bool signed = false) => width == 1 ? types.Boolean : width is 8 or 16 or 32 or 64 ? types.Integer(width, signed) : null;
    private TypeRef? Float(int width) => width == 32 ? types.Single : width == 64 ? types.Double : null;
    private static ManagedValue? Fail(string message, out string? problem) { problem = message; return null; }
}
