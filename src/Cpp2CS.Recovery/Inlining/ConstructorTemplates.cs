using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>同一前端与全局事实按需完整恢复；递归截断不提供模板。</summary>
public interface IMethodTemplateSource
{
    ManagedBody? GetBody(MethodDef method);
    Reason? GetFailure(MethodDef method) => null;
}

public sealed record ConstructorField(FieldRef Field, ManagedValue Value, bool AfterCall = false);
public sealed record ConstructorInvocation(MethodRef Method, IReadOnlyList<ManagedValue> Arguments);
public sealed record ConstructorTemplate(IReadOnlyList<ConstructorField> Fields, int Overwritten, ConstructorInvocation? Call = null);
public sealed record ConstructorTemplateResult(ConstructorTemplate? Template, Reason? Failure);

/// <summary>从完整开放恢复体读出直线构造模板；保留构造调用及两侧写入，匹配时决定展开或配对。</summary>
public sealed class ConstructorTemplates(IMethodTemplateSource source, ManagedTypes types)
{
    private readonly object gate = new();
    private readonly Dictionary<MethodDef, ConstructorTemplateResult> cache = [];
    private readonly HashSet<MethodDef> active = [];
    public bool IsEmpty(MethodDef method) => Alternatives(MethodRef.Open(method)).Any(t => t is { Call: null, Fields.Count: 0 });
    public ConstructorTemplateResult Get(MethodDef method)
    {
        lock (gate)
        {
            if (cache.TryGetValue(method, out var result)) return result;
            if (!active.Add(method)) return No("Recursive", "构造模板的完整恢复依赖成环。");
            var chain = new HashSet<TypeDef>();
            TypeRef? ancestor = MethodRef.Open(method).DeclaringType;
            while (ancestor is DefinitionRef type && chain.Add(type.Definition)) ancestor = Parent(ancestor);
            result = method.Owner.IsValueType ? No("ValueType", "值类型构造函数不提供直线模板。")
                : ancestor is not null ? No("Inheritance", "构造类型的继承链成环或未完整解析。")
                : source.GetBody(method) is { } body ? Read(body)
                : No("Incomplete", "候选未能完整恢复。", source.GetFailure(method));
            active.Remove(method);
            cache.Add(method, result);
            return result;
        }
    }
    private static ConstructorTemplateResult No(string kind, string message, Reason? cause = null) =>
        new(null, new("inline.Constructor.NotStraight", kind + "：" + message, cause));
    private ConstructorTemplateResult Read(ManagedBody body)
    {
        var method = body.Method.Method;
        if (method is not { Name: ".ctor", IsStatic: false, Owner.IsValueType: false } || method.GenericParameters.Count != 0)
            return No("Signature", "只接受引用类型的实例构造函数。");
        if (MethodTemplateStatements.Read(body, out var why) is not { } statements) return No(why!, "模板含非直线控制流。");
        var fields = new Dictionary<(FieldRef Field, bool After), ManagedValue>(); int overwritten = 0, calls = 0;
        ConstructorInvocation? constructor = null;
        void Write(FieldRef field, ManagedValue value)
        {
            var key = (field, constructor is not null);
            if (fields.ContainsKey(key)) overwritten++;
            fields[key] = value;
        }
        for (int i = 0; i < statements.Count; i++)
        {
            var statement = statements[i];
            if (statement is ManagedReturn { Value: null } && i == statements.Count - 1) continue;
            if (statement is ManagedStore { Target: FieldValue { Receiver: ArgumentValue { Index: -1 } fieldSelf } target } store
                && fieldSelf.Type.Equals(body.Method.DeclaringType) && !target.Field.Field.IsStatic
                && types.IsAssignable(body.Method.DeclaringType, target.Field.DeclaringType))
            {
                var value = LiteralOrParameter(store.Value);
                if (value is null) return No(statement.GetType().Name + "." + store.Value.GetType().Name, "字段写入值不是形参、常量、字面量实体或默认值。");
                Write(target.Field, value); continue;
            }
            if (statement is ManagedCall { Result: null, Invocation: { Virtual: false, Receiver: ArgumentValue { Index: -1 } self } invocation }
                && ++calls == 1 && self.Type.Equals(body.Method.DeclaringType)
                && invocation.Method.Method is { Name: ".ctor", IsStatic: false, Owner.IsValueType: false }
                && (invocation.Method.DeclaringType.Equals(body.Method.DeclaringType) || invocation.Method.DeclaringType.Equals(Parent(body.Method.DeclaringType)))
                && invocation.Arguments.Count == invocation.Method.Method.Parameters.Count)
            {
                var arguments = invocation.Arguments.Select(LiteralOrParameter).ToArray();
                if (arguments.Any(v => v is null)) return No("ManagedCall.Arguments", "构造调用实参不是形参、常量或字面量实体。");
                constructor = new(invocation.Method, arguments.Select(v => v!).ToArray());
                continue;
            }
            return No(statement.GetType().Name, "第一条不满足直线模板条件的语句。");
        }
        if (statements.LastOrDefault() is not ManagedReturn { Value: null }) return No("Return", "缺少无值返回。");
        if (calls == 0 && !(method.Owner.BaseType is null && body.Method.DeclaringType.Equals(types.Object)))
            return No("Initialization", "有基类的构造函数缺少 this 初始化调用。");
        return new(new(fields.Select(p => new ConstructorField(p.Key.Field, p.Value, p.Key.After)).ToArray(), overwritten, constructor), null);
    }
    /// <summary>每层可保留一次真实调用；继续展开时把内层值替换为最外层形参。成环只终止展开。</summary>
    public IEnumerable<ConstructorTemplate> Alternatives(MethodRef method)
    {
        var active = new HashSet<MethodDef>();
        var before = new List<ConstructorField>(); var after = new List<ConstructorField>();
        IReadOnlyList<ManagedValue>? arguments = null; int overwritten = 0;
        while (active.Add(method.Method) && Get(method.Method).Template is { } template)
        {
            ManagedValue Map(ManagedValue value)
            {
                var concrete = Substitute(value, method);
                return concrete is ArgumentValue parameter && arguments is not null ? arguments[parameter.Index] : concrete;
            }
            ConstructorField Field(ConstructorField field) => new(field.Field with { DeclaringType = method.Concrete(field.Field.DeclaringType) }, Map(field.Value), field.AfterCall);
            before.AddRange(template.Fields.Where(f => !f.AfterCall).Select(Field));
            after.InsertRange(0, template.Fields.Where(f => f.AfterCall).Select(Field));
            overwritten += template.Overwritten;
            var call = template.Call is { } nested ? new ConstructorInvocation(
                new(nested.Method.Method, nested.Method.TypeArguments.Select(method.Concrete).ToArray(), nested.Method.MethodArguments.Select(method.Concrete).ToArray()),
                nested.Arguments.Select(Map).ToArray()) : null;
            var fields = new Dictionary<(FieldRef, bool), ConstructorField>(); int replaced = 0;
            foreach (var field in before.Select(f => f with { AfterCall = false }).Concat(after.Select(f => f with { AfterCall = call is not null })))
            {
                var key = (field.Field, field.AfterCall);
                if (fields.ContainsKey(key)) replaced++;
                fields[key] = field;
            }
            yield return new(fields.Values.ToArray(), overwritten + replaced, call);
            if (call is null) yield break;
            method = call.Method; arguments = call.Arguments;
        }
    }
    private ManagedValue? LiteralOrParameter(ManagedValue value)
    {
        value = Normalize(value, types);
        return value is ArgumentValue { Index: >= 0 } or ConstantValue or StringValue or TypeHandleValue or FieldHandleValue or MethodHandleValue
            ? value : value is ComposedValue { Leaves.Count: 0 } ? value : null;
    }
    /// <summary>只消去托管类型与有效位均未改变的表示转换；常量截断到目标存储宽度。</summary>
    public static ManagedValue Normalize(ManagedValue value, ManagedTypes types)
    {
        if (value is ComposedValue { Leaves.Count: 0 } composed)
            return composed with { Leaves = Array.Empty<(IReadOnlyList<FieldRef>, ManagedValue)>() };
        if (value is not ConversionValue c) return Identity(value, types);
        var operand = Normalize(c.Operand, types);
        if (c.Kind == ConversionKind.Bitcast && operand is ConstantValue raw && c.Width == raw.Width)
            return new ConstantValue(raw.Bits, c.Type, c.Width);
        if (c.Kind is ConversionKind.SignExtend or ConversionKind.ZeroExtend or ConversionKind.Truncate)
        {
            if (operand is ConstantValue k)
            {
                int bits = Math.Min(c.Width, types.StorageBits(c.Type));
                if (bits is > 0 and <= 64 && k.Width is > 0 and <= 64)
                {
                    var table = new TermTable();
                    var term = table.Constant(k.Bits & (ulong.MaxValue >> (64 - k.Width)), k.Width);
                    term = bits <= k.Width ? table.Slice(term, 0, bits)
                        : table.Apply(new CoreOperator(c.Kind == ConversionKind.SignExtend ? CoreOperation.SignExtend : CoreOperation.ZeroExtend), bits, term);
                    return new ConstantValue((ulong)term.ConstantValue!.Value, c.Type, bits);
                }
            }
            if (c.Type.Equals(operand.Type) && c.Width >= types.StorageBits(c.Type)) return operand;
        }
        return Identity(c with { Operand = operand }, types);
    }
    private sealed record ScalarIdentity(ManagedValue Value) : AtomIdentity
    {
        public override string StableText => "constructor-scalar:" + Value;
    }
    /// <summary>窄标量的掩码与扩展只交给公共项规范化；比较字段的完整有效位，不增加相等规则。</summary>
    private static ManagedValue Identity(ManagedValue value, ManagedTypes types)
    {
        var leaves = ManagedValues.Walk(value).Where(v => v is ArgumentValue or LocalValue).Distinct().ToArray();
        if (leaves is not [var leaf] || !value.Type.Equals(leaf.Type)) return value;
        int bits = types.StorageBits(value.Type);
        if (bits <= 0 || bits > leaf.Width || bits > value.Width) return value;
        var table = new TermTable();
        Term? Read(ManagedValue v)
        {
            if (v.Equals(leaf)) return table.Atom(new ScalarIdentity(leaf), leaf.Width);
            if (v is ConstantValue k && k.Width is > 0 and <= 64)
                return table.Constant(k.Bits & (ulong.MaxValue >> (64 - k.Width)), k.Width);
            if (v is ConversionValue conversion && Read(conversion.Operand) is { } input)
            {
                if (conversion.Kind == ConversionKind.Bitcast && input.Width == conversion.Width) return input;
                if (conversion.Kind is not (ConversionKind.SignExtend or ConversionKind.ZeroExtend or ConversionKind.Truncate)) return null;
                return conversion.Width <= input.Width ? table.Slice(input, 0, conversion.Width)
                    : table.Apply(new CoreOperator(conversion.Kind == ConversionKind.SignExtend ? CoreOperation.SignExtend : CoreOperation.ZeroExtend), conversion.Width, input);
            }
            if (v is BinaryValue binary && Read(binary.Left) is { } left && Read(binary.Right) is { } right)
            {
                CoreOperation? operation = binary.Op switch
                {
                    BinaryOperator.And => CoreOperation.And, BinaryOperator.ShiftLeft => CoreOperation.ShiftLeft,
                    BinaryOperator.ShiftRightSigned => CoreOperation.ArithmeticShiftRight,
                    BinaryOperator.ShiftRightUnsigned => CoreOperation.LogicalShiftRight, _ => null,
                };
                if (operation is not null && left.Width == binary.Width
                    && (operation is CoreOperation.ShiftLeft or CoreOperation.ArithmeticShiftRight or CoreOperation.LogicalShiftRight || right.Width == binary.Width))
                    return table.Apply(new CoreOperator(operation.Value), binary.Width, left, right);
            }
            return null;
        }
        var actual = Read(value); var expected = Read(leaf)!;
        return actual is not null && table.Slice(actual, 0, bits) == table.Slice(expected, 0, bits) ? leaf : value;
    }
    public static ManagedValue Substitute(ManagedValue value, MethodRef method)
    {
        var body = new ManagedBody(MethodRef.Open(method.Method), [new(0, [new ManagedReturn(0, value)])]);
        return ((ManagedReturn)ManagedTypeMap.Map(body, method.Concrete).Blocks[0].Statements[0]).Value!;
    }
    public static TypeRef? Parent(TypeRef type) => type is DefinitionRef d ? d.Definition.BaseType?.Substitute(d.Arguments, []) : null;
}
