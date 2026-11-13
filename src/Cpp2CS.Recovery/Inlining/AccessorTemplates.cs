using System.Collections.Concurrent;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Inlining;

public enum AccessorKind { Getter, Setter }
public sealed record AccessorTemplate(AccessorKind Kind, FieldRef Field)
{
    public ManagedValue? Expression { get; init; }
    public IReadOnlyList<ManagedStore> Stores { get; init; } = [];
    public IReadOnlyList<FieldRef> Fields { get; init; } = [];
    public bool SingleField { get; init; }
}
public enum AccessorTemplateStatus { Complete, Incomplete, NotTemplate }
public sealed record AccessorTemplateResult(AccessorTemplateStatus Status, AccessorTemplate? Template = null, Reason? Failure = null);

/// <summary>只提供关闭内联逆后完整恢复的方法体摘要；实现须按方法缓存并可并发取用。</summary>
public interface IAccessorTemplateSource
{
    AccessorTemplateResult Get(MethodDef method);
}

/// <summary>直线返回表达式或字段赋值；局部只展开单定义，读取不能跨越模板自身的写入。</summary>
public static class AccessorTemplates
{
    private static AccessorTemplateResult No(string shape, string message) =>
        new(AccessorTemplateStatus.NotTemplate, Failure: new("inline.Accessor.None", "候选的方法体不是模板：" + shape + "；" + message));
    public static AccessorTemplateResult Read(ManagedBody body)
    {
        var all = body.Blocks.SelectMany(b => b.Statements).ToArray();
        if (all.Count(s => s is ManagedReturn) > 1) return No("MultipleReturns", "含多个返回");
        if (all.Any(s => s is ManagedBranch or ManagedSwitch)) return No("Branch", "含分支或循环");
        if (MethodTemplateStatements.Read(body, out var why) is not { } statements)
            return No(why ?? "ControlFlow", "含分支、循环或异常区域");
        if (statements.Count(s => s is ManagedReturn) != 1 || statements.LastOrDefault() is not ManagedReturn returned)
            return No("Return", "缺少唯一的末尾返回");
        if (statements.Any(s => s is ManagedCall) || statements.SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk).Any(v => v is StaticCallValue or NewObjectValue)) return No("Call", "含调用");
        var locals = new Dictionary<LocalId, ManagedValue>();
        ManagedValue Normalize(ManagedValue value)
        {
            if (value is LocalValue local && locals.TryGetValue(local.Id, out var source)) return source;
            var result = ManagedValues.Map(value, Normalize);
            return result is ConversionValue c && c.Type.Equals(c.Operand.Type) && c.Width == c.Operand.Width
                && c.Kind is ConversionKind.ZeroExtend or ConversionKind.SignExtend or ConversionKind.Truncate ? c.Operand : result;
        }
        bool Pure(ManagedValue value) => ManagedValues.Walk(value).All(v => v.Width is > 0 and <= 64 && (v switch
        {
            ArgumentValue a => a.Index >= -1 && a.Index < body.Method.Method.Parameters.Count && (a.Index >= 0 || !body.Method.Method.IsStatic),
            ConstantValue or FieldValue or StaticFieldValue => true,
            BinaryValue b => b.Op is BinaryOperator.Add or BinaryOperator.Subtract or BinaryOperator.Multiply
                or BinaryOperator.And or BinaryOperator.Or or BinaryOperator.Xor
                or BinaryOperator.ShiftLeft or BinaryOperator.ShiftRightSigned or BinaryOperator.ShiftRightUnsigned,
            UnaryValue u => u.Op is UnaryOperator.Negate or UnaryOperator.Not,
            ComparisonValue c => (int)c.Condition <= (int)ComparisonKind.UnsignedGreaterOrEqual,
            ConversionValue c => c.Kind is ConversionKind.ZeroExtend or ConversionKind.SignExtend or ConversionKind.Truncate,
            _ => false,
        }));
        var stores = new List<ManagedStore>();
        var written = new HashSet<FieldRef>();
        foreach (var statement in statements.SkipLast(1))
        {
            if (statement is ManagedAssignment a)
            {
                if (a.ExceptionArrival || locals.ContainsKey(a.Target.Id)
                    || ManagedValues.Walk(a.Value).OfType<LocalValue>().Any(v => !locals.ContainsKey(v.Id)))
                    return No("Local", "局部不是已定义值的单次赋值");
                var value = Normalize(a.Value);
                if (!Pure(value) || ManagedValues.Walk(a.Value).Select(FieldAccessor.FieldOf).OfType<FieldRef>().Any(written.Contains))
                    return No("Local.ReadAfterWrite", "局部含未支持的表达式或写入后的读取");
                locals.Add(a.Target.Id, value);
            }
            else if (statement is ManagedStore store)
            {
                var target = Normalize(store.Target); var value = Normalize(store.Value);
                if (target is not (FieldValue { Receiver: ArgumentValue } or StaticFieldValue)
                    || FieldAccessor.FieldOf(target) is not { } field || !written.Add(field))
                    return No("Store", "目标不是单个接收者的字段或字段重复写入");
                if (!Pure(value)) return No("Store.Value", "写入值不是纯整数表达式");
                if (ManagedValues.Walk(store.Value).Select(FieldAccessor.FieldOf).OfType<FieldRef>().Any(f => !f.Equals(field) && written.Contains(f)))
                    return No("Store.ReadAfterWrite", "写入之后又读取字段");
                stores.Add(store with { Target = target, Value = value });
            }
            else return No(statement.GetType().Name, "含非直线语句");
        }
        var method = body.Method.Method;
        if (stores.Count == 0 && returned.Value is { } expression && !ManagedTypes.IsVoid(method.ReturnType))
        {
            expression = Normalize(expression);
            if (!Pure(expression)) return No("Expression", "返回值不是纯整数或字段表达式");
            var fields = ManagedValues.Walk(expression).Select(FieldAccessor.FieldOf).OfType<FieldRef>().Distinct().ToArray();
            if (fields.Length == 0) return No("NoField", "表达式没有字段锚点");
            bool single = method.Parameters.Count == 0 && expression is FieldValue { Receiver: ArgumentValue { Index: -1 } } or StaticFieldValue
                && method.ReturnType.Equals(fields[0].Field.Type);
            return new(AccessorTemplateStatus.Complete, new(AccessorKind.Getter, fields[0])
            { Expression = expression, Fields = fields, SingleField = single });
        }
        if (stores.Count != 0 && returned.Value is null && ManagedTypes.IsVoid(method.ReturnType))
        {
            var roots = stores.Select(s => (s.Target as FieldValue)?.Receiver).Distinct().ToArray();
            if (roots.Length != 1) return No("Store.Receiver", "写入不属于同一个接收者");
            var fields = stores.Select(s => FieldAccessor.FieldOf(s.Target)!).ToArray();
            bool single = stores is [var one] && method.Parameters is [var parameter]
                && one.Value is ArgumentValue { Index: 0 } argument && parameter.Type.Equals(fields[0].Field.Type)
                && argument.Type.Equals(parameter.Type)
                && one.Target is FieldValue { Receiver: ArgumentValue { Index: -1 } } or StaticFieldValue;
            return new(AccessorTemplateStatus.Complete, new(AccessorKind.Setter, fields[0])
            { Stores = stores, Fields = fields, SingleField = single });
        }
        return No("Effects", "返回值与字段写入不能组成纯取值或无返回赋值模板");
    }
}

/// <summary>Lazy 的执行发布保证同一方法至多恢复一次，失败也缓存。</summary>
public sealed class CachedAccessorTemplates(Func<MethodDef, ManagedBody?> recover) : IAccessorTemplateSource
{
    private readonly ConcurrentDictionary<MethodDef, Lazy<AccessorTemplateResult>> templates = [];
    public AccessorTemplateResult Get(MethodDef method) => templates.GetOrAdd(method, m => new(() =>
        recover(m) is { } body ? AccessorTemplates.Read(body) : new(AccessorTemplateStatus.Incomplete))).Value;
}
