using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>
/// 托管方法体的类型代换：把一个泛型实例的方法体换成同一定义的另一个实例（如 Awaiter&lt;X&gt;.get_IsCompleted → Awaiter&lt;bool&gt;）。
/// 值、局部变量、字段与方法引用中的类型逐一代换；方法体的托管语义与类型实参无关时（字段按名访问、调用按方法身份），两者等价。
/// </summary>
public static class ManagedTypeMap
{
    /// <summary>把类型中出现的 from 结构地换成 to。</summary>
    public static TypeRef Replace(TypeRef type, TypeRef from, TypeRef to) => type.Equals(from) ? to : type switch
    {
        DefinitionRef d when d.Arguments.Count > 0 => d with { Arguments = d.Arguments.Select(a => Replace(a, from, to)).ToArray() },
        ArrayRef a => a with { Element = Replace(a.Element, from, to) },
        ByRefRef r => r with { Element = Replace(r.Element, from, to) },
        _ => type,
    };

    /// <summary>widthOf 给出代换后类型的值位宽（结构体为 0）；类型变化的值按它重算位宽。</summary>
    public static ManagedBody Map(ManagedBody body, Func<TypeRef, TypeRef> rename, Func<TypeRef, int>? widthOf = null)
    {
        TypeRef map(TypeRef t) => rename(t);
        int W(TypeRef before, TypeRef after, int width) => widthOf is not null && !before.Equals(after) ? widthOf(after) : width;
        FieldRef Field(FieldRef f) => f with { DeclaringType = map(f.DeclaringType) };
        MethodRef Method(MethodRef m) => m with { TypeArguments = m.TypeArguments.Select(map).ToArray(), MethodArguments = m.MethodArguments.Select(map).ToArray() };
        LocalValue Local(LocalValue l) => l with { Type = map(l.Type), Width = W(l.Type, map(l.Type), l.Width) };
        ManagedValue Value(ManagedValue value) => value switch
        {
            ArgumentValue v => v with { Type = map(v.Type), Width = W(v.Type, map(v.Type), v.Width) },
            LocalValue v => Local(v),
            ConstantValue v => v with { Type = map(v.Type), Width = W(v.Type, map(v.Type), v.Width) },
            StringValue v => v,
            TypeHandleValue v => v with { Target = map(v.Target) },
            NewArrayValue v => new NewArrayValue((ArrayRef)map(v.ArrayType), Value(v.Length)),
            NewObjectValue v => new NewObjectValue(Method(v.Constructor), v.Arguments.Select(Value).ToArray()) { Transparent = v.Transparent },
            DelegateValue v => new DelegateValue((DefinitionRef)map(v.DelegateType), Value(v.Target), Method(v.Method), v.Binding),
            BoxValue v => new BoxValue(Value(v.Operand), map(v.Boxed), map(v.ObjectType)),
            UnboxAddressValue v => new UnboxAddressValue(Value(v.Operand), map(v.Target)),
            UnboxValue v => new UnboxValue(Value(v.Operand), map(v.Target), W(v.Type, map(v.Target), v.Width)),
            IsInstValue v => new IsInstValue(Value(v.Operand), map(v.Target), v.BoxedType is { } boxed ? map(boxed) : null),
            CheckedCastValue v => new CheckedCastValue(Value(v.Operand), map(v.Target)),
            ArrayLengthValue v => v with { Array = Value(v.Array), Type = map(v.Type) },
            ArrayElementValue v => v with { Array = Value(v.Array), Index = Value(v.Index), Type = map(v.Type), Width = W(v.Type, map(v.Type), v.Width) },
            FieldValue v => v with { Receiver = Value(v.Receiver), Field = Field(v.Field), Type = map(v.Type), Width = W(v.Type, map(v.Type), v.Width), Accessor = null },
            AddressValue v => new AddressValue(Value(v.Target)),
            ComposedValue v => new ComposedValue(map(v.StructType), v.Leaves.Select(l => ((IReadOnlyList<FieldRef>)l.Path.Select(Field).ToArray(), Value(l.Value))).ToArray()),
            // 结构体换成基元后，整体读取 *&x 就是 x 本身。
            IndirectValue { Address: AddressValue a } v when widthOf is not null && widthOf(map(v.Type)) != 0 => Value(a.Target),
            IndirectValue v => new IndirectValue(Value(v.Address), map(v.Type), widthOf?.Invoke(map(v.Type)) ?? v.Width),
            StaticFieldValue v => v with { Field = Field(v.Field), Type = map(v.Type), Width = W(v.Type, map(v.Type), v.Width), Accessor = null },
            BinaryValue v => v with { Left = Value(v.Left), Right = Value(v.Right), Type = map(v.Type) },
            UnaryValue v => v with { Operand = Value(v.Operand), Type = map(v.Type) },
            ConversionValue v => v with { Operand = Value(v.Operand), Type = map(v.Type) },
            ComparisonValue v => v with { Left = Value(v.Left), Right = Value(v.Right), Type = map(v.Type) },
            ChoiceValue v => v with { Condition = Value(v.Condition), True = Value(v.True), False = Value(v.False), Type = map(v.Type) },
            BooleanValue v => v with { Left = Value(v.Left), Right = Value(v.Right), Type = map(v.Type) },
            NegatedValue v => v with { Operand = Value(v.Operand), Type = map(v.Type) },
            HoleValue v => v with { Type = map(v.Type) },
            AsyncResultValue v => v with { Value = v.Value is { } result ? Value(result) : null, Type = map(v.Type) },
            _ => throw new NotSupportedException(value.ToString()),
        };
        ManagedEdge Edge(ManagedEdge e) => e with { Copies = e.Copies.Select(c => new ManagedCopy(Local(c.Target), Value(c.Value))).ToArray() };
        ManagedStatement Statement(ManagedStatement statement) => statement switch
        {
            ManagedAssignment a => a with { Target = Local(a.Target), Value = Value(a.Value) },
            ManagedStore s => s with { Target = Value(s.Target), Value = Value(s.Value) },
            ManagedCall c => c with
            {
                Invocation = c.Invocation with
                {
                    Method = Method(c.Invocation.Method),
                    Constraint = c.Invocation.Constraint is { } constraint ? map(constraint) : null,
                    Receiver = c.Invocation.Receiver is { } receiver ? Value(receiver) : null,
                    Arguments = c.Invocation.Arguments.Select(Value).ToArray(),
                },
                Result = c.Result is { } result ? Local(result) : null,
            },
            ManagedReturn r => r with { Value = r.Value is { } returned ? Value(returned) : null },
            ManagedJump j => j with { Edge = Edge(j.Edge) },
            ManagedBranch b => b with { Condition = Value(b.Condition), Taken = Edge(b.Taken), Fallthrough = Edge(b.Fallthrough) },
            ManagedSwitch w => w with { Index = Value(w.Index), Cases = w.Cases.Select(Edge).ToArray() },
            ManagedThrow t => t with { Exception = Value(t.Exception) },
            ManagedCheck c => c with { Condition = Value(c.Condition), Exception = Method(c.Exception) },
            ManagedAwait a => a with { Task = Value(a.Task), Result = a.Result is { } awaited ? Local(awaited) : null },
            ManagedRethrow or ManagedEndFault or ManagedHole => statement,
            _ => throw new NotSupportedException(statement.ToString()),
        };
        return new ManagedBody(Method(body.Method), body.Blocks.Select(b => b with { Statements = b.Statements.Select(Statement).ToArray() }).ToArray())
        {
            Regions = body.Regions.Select(r => r with { Exception = r.Exception is { } e ? Local(e) : null,
                CatchType = r.CatchType is { } caught ? map(caught) : null }).ToArray(),
        };
    }
}
