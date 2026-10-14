using Cpp2CS.IR;

namespace Cpp2CS.Native;

// 普通方法与状态机投影共用的 SSA 到源码表达式转换，不读取机器指令。
public sealed class ManagedExpressionBuilder(SsaSemantics semantics, ManagedNames managed, HeaderLayout layouts,
    Symbols symbols, Action<string> problem, Action<string> proof, NativeMethod? currentMethod = null)
{
    public Dictionary<string, string> Results { get; } = [];
    public HashSet<string> BooleanResults { get; } = [];
    public Func<SemanticTerm, Expression?>? Bind { get; set; }
    private readonly Dictionary<string, (ulong Address, SemanticTerm Value)> reads = [];
    public IReadOnlySet<string> ReadNames => reads.Keys.ToHashSet();

    public void CaptureFieldReads(Func<SemanticTerm, bool> include)
    {
        foreach (var load in semantics.Program.Values.Where(v => v.Operation == "load"))
        {
            var value = semantics.Resolve(load.Id);
            if (value.Kind == "field" && value.ReadIdentity == load.Id && include(value)) reads.Add(load.Id, (load.Address, value));
        }
    }
    public List<Statement> ReadStatements(ulong address) => reads.Where(r => r.Value.Address == address)
        .Select(r => (Statement)new AssignStatement(address, r.Key, FieldValue(r.Value.Value), r.Value.Value.Type!)).ToList();

    public Expression Call(SsaManagedCall call, List<Statement> before)
    {
        var target = semantics.TargetMethod(call.Value);
        if (target is null) return Unknown("调用签名未绑定：" + call.Value);
        if (target.Parameters.Length != call.Arguments.Length) return Unknown("调用参数数目与签名不一致：" + call.Value);
        var split = target.Name.Split("$$"); var owner = split[0]; var name = split[1];
        if (name is ".ctor" or ".cctor") return Unknown("构造调用需要先归约对象分配：" + call.Value);
        var instance = target.Parameters.FirstOrDefault()?.Name == "__this";
        var signature = managed.SignatureOf(owner, name);
        var arguments = new List<Expression>();
        for (var index = instance ? 1 : 0; index < target.Parameters.Length; index++)
        {
            var parameter = target.Parameters[index];
            if (parameter.Name == "method" && parameter.Type.Contains("MethodInfo")) continue;
            var type = signature?.ParameterTypes.ElementAtOrDefault(index - (instance ? 1 : 0));
            arguments.Add(TypedValue(call.Arguments[index], parameter.Type, type));
        }
        if (!instance && call.Arguments.LastOrDefault() is { Kind: "metadata" } info && info.Name.StartsWith("Method$"))
        {
            var full = info.Name[7..].Split('(')[0]; var dot = ManagedNames.LastTopLevelDot(full);
            if (dot > 0) owner = full[..dot];
        }
        Expression? receiver = null;
        if (instance && SsaSemantics.AddressParts(call.Arguments[0]).Root.Kind == "stack" && managed.BaseTypeOf(owner) == "System.ValueType")
        {
            var stored = semantics.ReadCallStorage(call.Value, call.Arguments[0], layouts.Size(target.Parameters[0].Type.TrimEnd('*')) * 8);
            var local = "receiver_" + call.Address.ToString("x");
            before.Add(new AssignStatement(call.Address, local, Value(stored), owner));
            receiver = new NameExpression(local);
            proof($"0x{call.Address:x}: value-type receiver copied from pre-call storage; later writes do not reuse the snapshot");
        }
        else if (instance) receiver = Value(call.Arguments[0]);
        var property = name.StartsWith("get_") && managed.IsPropertyGetter(owner, name);
        return new InvocationExpression(instance ? name : owner + "." + name, receiver, arguments.ToArray(), property);
    }

    public Expression TypedValue(SemanticTerm value, string nativeType, string? logicalType = null)
    {
        logicalType ??= symbols.Display(nativeType);
        if (ConstantValue(nativeType, logicalType, value) is { } aggregate) return aggregate;
        if (value.Kind == "constant")
        {
            if (nativeType is "float" or "double")
                return new OperationExpression(ValueOperation.BitCast, nativeType, [new ConstantExpression(value.Offset)]);
            if (value.Offset == 0 && nativeType.EndsWith('*')) return new NameExpression("null");
            if (nativeType == "bool" || logicalType == "System.Boolean")
                return new NameExpression(value.Offset == 0 ? "false" : "true");
        }
        var expression = Value(value);
        if (IntegerProjection.Width(nativeType) > 0 && (Boolean(expression, value) || BooleanCondition(value) is not null))
            expression = new OperationExpression(ValueOperation.Select, nativeType, [expression, new ConstantExpression(1), new ConstantExpression(0)]);
        return managed.BaseTypeOf(logicalType) == "System.Enum" ? new CastExpression(logicalType, expression) : expression;
    }

    public Expression Value(SemanticTerm value)
    {
        if (Bind?.Invoke(value) is { } binding) return binding;
        if (value.ReadIdentity is { } read && reads.ContainsKey(read)) return new NameExpression(read);
        if (value.Kind == "metadata" && symbols.Metadata.GetValueOrDefault(unchecked((ulong)value.Offset)) is { Kind: "ScriptString" } literal)
            return new MetadataExpression(literal, false);
        if (value.Kind == "parameter") return new NameExpression(value.Name == "__this" ? "this" : value.Name);
        if (value.Kind == "call-result" && Results.TryGetValue(value.Name, out var result)) return new NameExpression(result);
        if (value.Kind == "phi")
        {
            var items = value.Inputs.Select(Value).DistinctBy(SemanticWriter.Expression).ToArray();
            return items.Length == 1 ? items[0] : Unknown("业务 Phi 未按前驱归约：" + value.Name);
        }
        if (value.Kind is "slice" or "zero-extend" or "sign-extend" or "abi-extend" && value.Offset == 0)
        {
            var input = value.Inputs[0];
            if (input.Width == value.Width || input.Type is "bool" or "System.Boolean" ||
                value.Kind == "slice" && input.Type is { } type && layouts.Size(type) * 8 == value.Width) return Value(input);
            if (value.Width >= 8 && Boolean(Value(input), input)) return Value(input);
            if (value.Kind is "zero-extend" or "sign-extend" && input.Width == 32 && value.Width == 64)
                return new OperationExpression(value.Kind == "zero-extend" ? ValueOperation.ZeroExtendWord : ValueOperation.IntegerCast, "long", [Value(input)]);
            if (value.Kind == "slice" && input.Width <= 64 && value.Width == 32 && input.Type is "int64_t" or "uint64_t")
                return new OperationExpression(ValueOperation.IntegerCast, "int", [Value(input)]);
            return Unknown("位宽转换尚未投影：" + value.Kind + ":" + input.Width + "->" + value.Width);
        }
        if (value.Kind == "field") return FieldValue(value);
        if (value.Kind == "constant") return new ConstantExpression(value.Width == 32 ? unchecked((int)value.Offset) : value.Offset);
        if (value.Kind is "zero" or "nonzero")
        {
            var input = value.Inputs[0];
            var left = Value(input);
            Expression right = Boolean(left, input) ? new NameExpression("false") :
                input.Type?.EndsWith('*') == true ? new NameExpression("null") : new ConstantExpression(0);
            return new BinaryExpression(value.Kind == "zero" ? "==" : "!=", left, right);
        }
        if (value.Kind.StartsWith("b."))
        {
            if (Condition(value) is { } condition) return condition;
            return Unknown("整数条件的类型或位宽未确定：" + value.Kind);
        }
        if (value.Kind == "and" && value.Inputs[1] is { Kind: "constant", Offset: 1 })
        {
            var input = Value(value.Inputs[0]);
            if (Boolean(input, value.Inputs[0])) return input;
        }
        if (BooleanCondition(value) is { } boolean) return boolean;
        if (value.Kind is "condition-value" or "select" && Integer(value) is { } integer) return integer.Expression;
        return Unknown("C# 表达式未归约：" + value.Kind + ":" + value.Name);
    }
    private Expression? Condition(SemanticTerm value)
    {
        if (value.Inputs is not [{ Kind: "compare" or "compare-add" or "compare-and" } flags] || flags.Inputs.Length != 2) return null;
        if (Integer(flags.Inputs[0]) is { } left && Integer(flags.Inputs[1]) is { } right)
            return IntegerConditions.Project(flags.Kind, checked((int)value.Offset), left, right);
        if (flags.Kind == "compare" && value.Offset is 1 or 2 && Reference(flags.Inputs[0]) is { } a && Reference(flags.Inputs[1]) is { } b &&
            NativeValues.ReferenceEqual(a, b) is { } equal) return value.Offset == 1 ? equal : new BinaryExpression("==", equal, new NameExpression("false"));
        return null;
    }
    private NativeValue? Reference(SemanticTerm value) => value.Width != 64 ? null :
        value is { Kind: "constant", Offset: 0 } ? new(BitOps.Constant(0, 64), "int64_t", new ConstantExpression(0)) :
        value.Type is { } type && NativeValues.IsManagedReference(type) ? new(new InputBits("ssa:" + value.Name, 64), type, Value(value)) : null;
    private Expression? BooleanCondition(SemanticTerm value) => value.Kind == "condition-value" && value.Offset == 2 &&
        value.Inputs is [{ Kind: "compare", Inputs: [var tested, { Kind: "constant", Offset: 0 }] }] ? BooleanBits(tested) : null;
    private Expression? BooleanBits(SemanticTerm value)
    {
        if (value.Kind == "zero-extend") return BooleanBits(value.Inputs[0]);
        if (value.Kind == "and" && value.Inputs[1] is { Kind: "constant", Offset: 1 })
        {
            var input = value.Inputs[0];
            while (input.Kind is "abi-extend" or "zero-extend" || input.Kind == "slice" && input.Offset == 0 && input.Width >= 8) input = input.Inputs[0];
            return BooleanBits(input);
        }
        if (value.Width != 8) return null;
        if (value.Kind == "phi")
        {
            var incoming = value.Inputs.Select(BooleanBits).ToArray();
            return incoming.Length > 0 && incoming.All(v => v is not null) && incoming.Select(v => SemanticWriter.Expression(v!)).Distinct().Count() == 1 ? incoming[0] : null;
        }
        if (Bind?.Invoke(value) is { } bound && Boolean(bound, value)) return bound;
        return value.Type == "bool" ? Value(value) : null;
    }
    private NativeValue? Integer(SemanticTerm value)
    {
        var width = value.Width;
        if (width is <= 0 or > 64) return null;
        var type = width <= 32 ? "uint32_t" : "uint64_t";
        if (value.Kind == "constant")
        {
            var bits = BitOps.Constant(value.Offset, width);
            return new(bits, type, new ConstantExpression(width == 64 ? value.Offset : (long)((ulong)value.Offset & ((1UL << width) - 1))));
        }
        if (BooleanBits(value) is { } boolean)
            return new(new InputBits("ssa:" + value.Name, width), width <= 8 ? "uint8_t" : type,
                new OperationExpression(ValueOperation.Select, width <= 8 ? "uint8_t" : type, [boolean, new ConstantExpression(1), new ConstantExpression(0)]));
        if (value.Kind is "parameter" or "field" or "call-result" && IntegerProjection.Width(value.Type ?? "") == width)
            return new(new InputBits("ssa:" + value.Name, width), value.Type!, Value(value));
        if (value.Kind is "slice" or "zero-extend" or "sign-extend" or "abi-extend" && Integer(value.Inputs[0]) is { } input)
        {
            if (value.Kind == "slice") return NativeValues.Slice(input, checked((int)value.Offset), width);
            if (width < input.Bits.Width) return null;
            if (width == input.Bits.Width) return input;
            if (value.Kind == "sign-extend")
                return width is 32 or 64 && IntegerProjection.Bits(input) is { } signedInput ?
                    new(new InputBits("ssa:" + value.Name, width), "int" + width + "_t",
                        new OperationExpression(ValueOperation.SignExtend, "int" + width + "_t", [signedInput, new ConstantExpression(input.Bits.Width)])) : null;
            Bits high = value.Kind == "zero-extend" ? BitOps.Constant(0, width - input.Bits.Width) : new UnknownBits("ssa-upper", "ABI", width - input.Bits.Width);
            return input with { Bits = BitOps.Concat([input.Bits, high]) };
        }
        if (value.Kind == "condition-value" && Condition(value) is { } condition)
            return new(new InputBits("ssa:" + value.Name, width), "int" + Math.Max(32, width) + "_t", new OperationExpression(ValueOperation.Select, "int" + Math.Max(32, width) + "_t",
                [condition, new ConstantExpression(1), new ConstantExpression(0)]));
        if (value.Kind == "select" && Condition(value.Inputs[0]) is { } selected &&
            Integer(value.Inputs[1]) is { } left && Integer(value.Inputs[2]) is { } right &&
            IntegerProjection.Bits(left) is { } a && IntegerProjection.Bits(right) is { } b && width is 32 or 64)
            return new(new InputBits("ssa:" + value.Name, width), "int" + width + "_t", new OperationExpression(ValueOperation.Select, "int" + width + "_t", [selected, a, b]));
        return null;
    }
    private bool Boolean(Expression expression, SemanticTerm value) =>
        value.Type is "bool" or "System.Boolean" || expression is NameExpression name && BooleanResults.Contains(name.Name) ||
        expression is BinaryExpression { Operator: "==" or "!=" or "<" or "<=" or ">" or ">=" } ||
        expression is SourceMemberExpression { Type: "bool" or "System.Boolean" };
    private Expression Unknown(string reason) { problem(reason); return new UnknownExpression(reason); }

    private Expression FieldValue(SemanticTerm value)
    {
        if (value.Type is null || layouts.Size(value.Type) * 8 != value.Width) return Unknown("部分字段读取尚未投影：" + value.Name);
        var expression = Value(value.Inputs[0]);
        var owner = value.Inputs[0].Type is { } nativeType ? symbols.Display(nativeType) : "";
        foreach (var part in (value.FieldPath.Length == 0 ? [value.Name] : value.FieldPath).Where(p => p != "fields"))
        {
            if (managed.SourceMember(owner, part) is not { } member) return Unknown("托管字段身份未绑定：" + owner + "." + part);
            // 访问器自身不能把后备字段再投影成同一个属性调用。
            var name = currentMethod?.Name == owner + "$$get_" + member.Name || currentMethod?.Name == owner + "$$set_" + member.Name ? part : member.Name;
            expression = new SourceMemberExpression(expression, name, member.Type);
            owner = member.Type;
        }
        return managed.BaseTypeOf(owner) == "System.Enum" ? new CastExpression("int", expression) : expression;
    }

    private Expression? ConstantValue(string nativeType, string logicalType, SemanticTerm value)
    {
        if (nativeType.EndsWith('*') || layouts.Shape(nativeType).Kind is not (Cpp2CS.Abi.ShapeKind.Composite or Cpp2CS.Abi.ShapeKind.HomogeneousFloat) ||
            !managed.HasDefaultValueConstruction(logicalType) || value.Width != layouts.Size(nativeType) * 8) return null;
        byte[]? Bytes(SemanticTerm v) => v.Kind == "constant" && v.Width <= 64 ? Enumerable.Range(0, v.Width / 8).Select(i => (byte)((ulong)v.Offset >> (i * 8))).ToArray() :
            v.Kind == "compose" && v.Inputs.All(p => p.Kind == "constant" && p.Width <= 64) ? v.Inputs.SelectMany(p => Bytes(p)!).ToArray() : null;
        var bytes = Bytes(value);
        if (bytes is null) return null;
        if (bytes.All(b => b == 0)) return new ObjectValueExpression(logicalType, []);
        var fields = new List<(string, Expression)>();
        foreach (var field in layouts.Flatten(nativeType, 0))
        {
            if (managed.MutableField(logicalType, field.Name, true) is not { } name || field.Type is not ("float" or "double" or "int32_t" or "int64_t" or "bool")) return null;
            var size = field.Type is "double" or "int64_t" ? 8 : field.Type == "bool" ? 1 : 4;
            if (field.Size != size || field.Offset < 0 || field.Offset + size > bytes.Length) return null;
            var bits = bytes.Skip(field.Offset).Take(size).Select((b, i) => (ulong)b << (i * 8)).Aggregate(0UL, (a, b) => a | b);
            if (field.Type == "bool" && bits > 1) return null;
            Expression fieldValue = field.Type switch
            {
                "float" or "double" => new OperationExpression(ValueOperation.BitCast, field.Type, [new ConstantExpression(unchecked((long)bits))]),
                "bool" => new NameExpression(bits == 0 ? "false" : "true"),
                "int32_t" => new ConstantExpression(unchecked((int)bits)),
                _ => new CastExpression("long", new ConstantExpression(unchecked((long)bits)))
            };
            fields.Add((name, fieldValue));
        }
        return fields.Count == 0 ? null : new ObjectValueExpression(logicalType, fields.ToArray());
    }
}
