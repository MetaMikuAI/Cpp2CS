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
    private readonly Dictionary<Storage, ManagedValue> arguments = new();
    private readonly Dictionary<Variable, ManagedValue> projections = new();
    private readonly Dictionary<Call, LocalValue> callResults = new();
    private readonly Dictionary<Call, Expr> callDestinations = new();
    private readonly Dictionary<Call, MethodRef?> callTargets = new();
    private int nextTemp;
    private readonly AggregateValues aggregates;
    private readonly Dictionary<Variable, (TypeRef Type, int Width)> locals = new();
    public IReadOnlyDictionary<Variable, (TypeRef Type, int Width)> Locals => locals;
    public string? SignatureProblem { get; }
    public StackObjects Stack { get; }
    public LocalValue? ReturnValue { get; }
    public IReadOnlyList<RecoveryProblem> BufferProblems { get; }
    public MetadataReferences Metadata { get; }

    public ValueRecovery(RecoverySession session, PreparedMethod method)
    {
        this.session = session;
        this.method = method;
        types = session.Types;
        Metadata = new MetadataReferences(session.Model, method.Function);
        aggregates = new AggregateValues(types);
        Stack = new StackObjects(method.Function, types, MemorySignature);
        BufferProblems = BufferInitialization.Check(method.Function, method.Return, types, MemorySignature);
        var signature = session.Abi.Classify(method.Method, out var problem);
        SignatureProblem = problem;
        if (signature is not null)
        {
            if (signature.This is { } self) Bind(self, -1, "this");
            for (var i = 0; i < signature.Parameters.Length; i++) Bind(signature.Parameters[i], i, method.Method.Method.Parameters[i].Name);
        }
        var statements = method.Function.Blocks.SelectMany(b => b.Statements).ToArray();
        var variables = statements.SelectMany(s => s switch
        {
            Define d => new[] { d.Target }, Phi p => p.Sources.Append(p.Target), Call c => c.Defines, _ => [],
        }).Concat(statements.SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable));
        nextTemp = variables.Where(v => v.Storage.Bank == Bank.Temp).Select(v => v.Storage.Index).DefaultIfEmpty(-1).Max() + 1;
        if (method.Return is { Passing: Passing.Indirect, Pieces: [var pointer] } returned)
        {
            ReturnValue = Temporary(returned.Type);
            arguments[pointer.Register] = new AddressValue(ReturnValue, new ByRefRef(returned.Type));
        }
        foreach (var call in statements.OfType<Call>())
        {
            if (HelperResultType(call) is { } helperType && call.Defines is [var helperResult])
            {
                locals[helperResult] = (helperType, 64);
                callResults.Add(call, new(helperResult, helperType, 64));
                continue;
            }
            if (Target(call) is not { } target || session.Abi.Classify(target, out _)?.Return is not { Pieces.Length: > 0 } result) continue;
            if (result is { Passing: Passing.Indirect, Pieces: [var output] })
            {
                var index = Array.IndexOf(call.Sources, output.Register);
                if (index >= 0 && index < call.Arguments.Length)
                {
                    callResults.Add(call, Temporary(result.Type));
                    callDestinations.Add(call, call.Arguments[index]);
                }
                continue;
            }
            if (result.Passing != Passing.Registers) continue;
            if (result.Pieces is [var piece])
            {
                var index = Array.IndexOf(call.Results, piece.Register);
                if (index < 0 || index >= call.Defines.Length) continue;
                var variable = call.Defines[index];
                locals[variable] = (result.Type, piece.Width);
                callResults.Add(call, new(variable, result.Type, piece.Width));
            }
            else if (types.Kind(result.Type) == ValueKind.Struct)
            {
                var local = new LocalValue(new Variable(Storage.Temp(nextTemp++), 1), result.Type, types.Size(result.Type) * 8);
                callResults.Add(call, local);
                foreach (var part in result.Pieces)
                {
                    var index = Array.IndexOf(call.Results, part.Register);
                    if (index >= 0 && index < call.Defines.Length && aggregates.Project(local, part.Offset, part.Width) is { } projected)
                        projections.Add(call.Defines[index], projected);
                }
            }
        }
        Infer();
    }

    private void Bind(AbiValue value, int index, string name)
    {
        var argument = new ArgumentValue(index, name, value.Type, types.Size(value.Type) * 8);
        if (value is { Passing: Passing.Indirect, Pieces: [var pointer] })
        {
            arguments[pointer.Register] = new AddressValue(argument, new ByRefRef(value.Type));
            return;
        }
        if (value.Passing != Passing.Registers) return;
        foreach (var piece in value.Pieces)
            if (piece.Offset == 0 && piece.Width == argument.Width) arguments[piece.Register] = argument;
            else if (types.Kind(value.Type) == ValueKind.Struct && aggregates.Project(argument, piece.Offset, piece.Width) is { } projected)
                arguments[piece.Register] = projected;
    }

    public LocalValue? CallResult(Call call) => callResults.GetValueOrDefault(call);
    public Expr? CallDestination(Call call) => callDestinations.GetValueOrDefault(call);
    public LocalValue Temporary(TypeRef type) => new(new Variable(Storage.Temp(nextTemp++), 1), type, types.Size(type) * 8);

    private ManagedValue? Variable(Variable variable, int width, out string? problem)
    {
        ManagedValue? value = variable.Version == 0
            ? arguments.GetValueOrDefault(variable.Storage)
            : projections.TryGetValue(variable, out var projected) ? projected
            : locals.TryGetValue(variable, out var local) ? new LocalValue(variable, local.Type, local.Width) : null;
        if (value is null) return Fail($"未确定变量 {variable}", out problem);
        if (width == value.Width) { problem = null; return value; }
        if (width < value.Width && types.Kind(value.Type) == ValueKind.Struct && aggregates.Project(value, 0, width) is { } part)
        { problem = null; return part; }
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
            case Load load:
                if (Metadata.Usage(load) is { Kind: UsageKind.StringLiteral, Value: string text }) return new StringValue(text, types.String);
                if (ArrayLength(load) is { } length) return length;
                return Location(load.Address, load.Width, out problem);
            case Ir.Convert conversion:
            {
                if (Recover(conversion.Operand, out problem) is not { } operand) return null;
                var target = NumericResult(conversion);
                if (types.Kind(operand.Type) == ValueKind.Struct && aggregates.Bits(operand) is { } bits) operand = bits;
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
                if (condition.Width != 1 || yes.Width != select.Width || no.Width != select.Width) return Fail("条件值位宽不一致", out problem);
                if (yes.Type == no.Type) return new ChoiceValue(condition, yes, no, yes.Type, select.Width);
                if (Numeric(yes.Type) && Numeric(no.Type) && Integer(select.Width) is { } integer)
                    return new ChoiceValue(condition, new ConversionValue(ConvKind.Bitcast, yes, integer, select.Width),
                        new ConversionValue(ConvKind.Bitcast, no, integer, select.Width), integer, select.Width);
                bool Zero(Expr native, ManagedValue value) => value is ConstantValue { Bits: 0 } || native is Use use && IsZero(use.Variable);
                if (ManagedTypes.IsReferenceType(yes.Type) && Zero(select.False, no)) no = new ConstantValue(0, yes.Type, 64);
                else if (ManagedTypes.IsReferenceType(no.Type) && Zero(select.True, yes)) yes = new ConstantValue(0, no.Type, 64);
                if (!ManagedTypes.IsReferenceType(yes.Type) || !ManagedTypes.IsReferenceType(no.Type)) return Fail("条件值类型尚未合并", out problem);
                return new ChoiceValue(condition, yes, no, CommonReference([yes.Type, no.Type]), select.Width);
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
            case FrameAddress frame: return Stack.Address(frame.Offset) ?? Fail("栈对象尚未还原", out problem);
            default: return Fail($"未支持表达式 {expression.GetType().Name}", out problem);
        }
    }

    /// <summary>把内存位置恢复为静态字段、实例字段或托管引用解引用，可用于读取和写入。</summary>
    public ManagedValue? Location(Expr address, int width, out string? problem, bool whole = false)
    {
        problem = null;
        if (Metadata.StaticAddress(address) is { } storage)
        {
            if (width <= 0 || width % 8 != 0 || types.StaticFieldPath(storage.Type, storage.Offset, width / 8) is not { Count: > 0 } fields)
                return Fail($"静态字段位置未匹配 {storage.Type}+{storage.Offset}:{width}", out problem);
            ManagedValue location = new StaticFieldValue(fields[0].Field, fields[0].Type, types.Size(fields[0].Type) * 8);
            foreach (var field in fields.Skip(1)) location = new FieldValue(location, field.Field, field.Type, types.Size(field.Type) * 8);
            return location;
        }
        if (ArrayElement(address, width) is { } element) return element;
        if (address is FrameAddress frame)
        {
            problem = null;
            return Stack.Location(frame.Offset, width) ?? Fail("栈位置尚未还原", out problem);
        }
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
            if (offset == 0 && types.Size(type) * 8 == width && (whole || types.Kind(type) != ValueKind.Struct))
                return new IndirectValue(receiver, type, width);
        }
        else if (!ManagedTypes.IsReferenceType(type)) return Fail("内存基址没有对象或托管引用类型", out problem);
        if (offset is < 0 or > int.MaxValue || width <= 0 || width % 8 != 0
            || types.FieldPath(type, (int)offset, width / 8) is not { } path) return Fail($"字段位置未匹配 {type}+{offset}:{width}", out problem);
        foreach (var field in path) receiver = new FieldValue(receiver, field.Field, field.Type, types.Size(field.Type) * 8);
        return receiver;
    }

    private MethodRef? Target(Call call)
    {
        if (callTargets.TryGetValue(call, out var cached)) return cached;
        return callTargets[call] = session.Resolver.Resolve(call) is ManagedCallee managed
            ? CallTargets.Resolve(call, managed, session.Abi, Metadata) : null;
    }

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
        if (argument is { Passing: Passing.Indirect, Pieces: [var pointer] })
        {
            var source = Array.IndexOf(call.Sources, pointer.Register);
            if (source < 0 || source >= call.Arguments.Length) return Fail("间接参数缺少来源", out problem);
            var value = Location(call.Arguments[source], types.Size(argument.Type) * 8, out problem, whole: true);
            return value?.Type == argument.Type ? value : Fail("间接参数类型尚未确认", out problem);
        }
        if (argument.Passing != Passing.Registers || argument.Pieces.Length == 0) return Fail("间接或栈调用参数尚未还原", out problem);
        if (argument.Pieces.Length > 1)
        {
            var parts = new List<ReturnPiece>();
            foreach (var part in argument.Pieces)
            {
                var source = Array.IndexOf(call.Sources, part.Register);
                if (source < 0 || source >= call.Arguments.Length) return Fail("调用参数缺少来源", out problem);
                parts.Add(new(part.Offset, Fold.Convert(ConvKind.Truncate, call.Arguments[source], part.Width)));
            }
            return Aggregate(argument.Type, parts, out problem);
        }
        var piece = argument.Pieces[0];
        var index = Array.IndexOf(call.Sources, piece.Register);
        if (index < 0 || index >= call.Arguments.Length) return Fail("调用参数缺少来源", out problem);
        var native = Fold.Convert(ConvKind.Truncate, call.Arguments[index], piece.Width);
        return RecoverAs(native, argument.Type, out problem);
    }

    public ManagedValue? RecoverAs(Expr native, TypeRef expected, out string? problem)
    {
        if (expected is ByRefRef staticReference && Metadata.StaticAddress(native) is not null)
        {
            var location = Location(native, types.Size(staticReference.Element) * 8, out problem, whole: true);
            return location?.Type == staticReference.Element ? new AddressValue(location, staticReference)
                : Fail("静态字段引用类型不符", out problem);
        }
        if (native is FrameAddress frame && expected is ByRefRef byRef)
        {
            problem = null;
            return Stack.Address(frame.Offset, byRef.Element) ?? Fail("栈引用类型不符", out problem);
        }
        if (native is Use use && ManagedTypes.IsReferenceType(expected) && IsZero(use.Variable))
        {
            problem = null;
            return new ConstantValue(0, expected, 64);
        }
        if (Recover(native, out problem) is not { } value) return null;
        if (value.Type == expected) return value;
        if (types.Kind(expected) == ValueKind.Struct && aggregates.Assemble(expected, [(0, value)]) is { } aggregate) return aggregate;
        if (Numeric(value.Type) && Numeric(expected) && types.Size(expected) * 8 == value.Width)
            return new ConversionValue(ConvKind.Bitcast, value, expected, value.Width);
        if (value is ConstantValue { Bits: 0 } && ManagedTypes.IsReferenceType(expected)) return new ConstantValue(0, expected, 64);
        if (types.IsAssignable(value.Type, expected)) return value;
        return Fail($"值类型不符 {value.Type} → {expected}", out problem);
    }

    public ManagedValue? Aggregate(TypeRef type, IReadOnlyList<ReturnPiece> pieces, out string? problem)
    {
        var recovered = new List<(int Offset, ManagedValue Value)>();
        foreach (var piece in pieces)
        {
            if (Recover(piece.Value, out problem) is not { } value) return null;
            recovered.Add((piece.Offset, value));
        }
        problem = null;
        return aggregates.Assemble(type, recovered) ?? Fail("聚合分量与字段布局不符", out problem);
    }

    private bool Numeric(TypeRef type) => types.Kind(type) is ValueKind.Bool or ValueKind.Int or ValueKind.Float or ValueKind.Double;
    private TypeRef? Integer(int width, bool signed = false) => width == 1 ? types.Boolean : width is 8 or 16 or 32 or 64 ? types.Integer(width, signed) : null;
    private TypeRef? Float(int width) => width == 32 ? types.Single : width == 64 ? types.Double : null;
    private static ManagedValue? Fail(string message, out string? problem) { problem = message; return null; }
}
