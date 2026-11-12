using System.Collections.Concurrent;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Inlining;

public enum AccessorKind { Getter, Setter }
public sealed record AccessorTemplate(AccessorKind Kind, FieldRef Field);
public enum AccessorTemplateStatus { Complete, Incomplete, NotTemplate }
public sealed record AccessorTemplateResult(AccessorTemplateStatus Status, AccessorTemplate? Template = null, Reason? Failure = null);

/// <summary>只提供关闭内联逆后完整恢复的方法体摘要；实现须按方法缓存并可并发取用。</summary>
public interface IAccessorTemplateSource
{
    AccessorTemplateResult Get(MethodDef method);
}

/// <summary>直线访问器；只消去相邻块的空跳转、单定义单使用局部与同类型同位宽的恒等转换。</summary>
public static class AccessorTemplates
{
    public static AccessorTemplateResult Read(ManagedBody body)
    {
        var missing = new AccessorTemplateResult(AccessorTemplateStatus.NotTemplate);
        if (MethodTemplateStatements.Read(body) is not { } statements) return missing;
        if (statements.LastOrDefault() is not ManagedReturn returned) return missing;
        var uses = statements.SelectMany(s => s is ManagedAssignment a ? [a.Value] : ManagedValues.Of(s))
            .SelectMany(ManagedValues.Walk).OfType<LocalValue>().GroupBy(v => v.Id).ToDictionary(g => g.Key, g => g.Count());
        var locals = new Dictionary<LocalId, ManagedValue>();
        ManagedValue Normalize(ManagedValue value)
        {
            if (value is LocalValue local && locals.TryGetValue(local.Id, out var source)) return source;
            var result = ManagedValues.Map(value, Normalize);
            return result is ConversionValue c && c.Type.Equals(c.Operand.Type) && c.Width == c.Operand.Width
                && c.Kind is ConversionKind.ZeroExtend or ConversionKind.SignExtend or ConversionKind.Truncate
                ? c.Operand : result;
        }
        var operations = new List<ManagedStatement>();
        foreach (var statement in statements.SkipLast(1))
        {
            if (statement is ManagedAssignment a)
            {
                if (a.ExceptionArrival || locals.ContainsKey(a.Target.Id) || uses.GetValueOrDefault(a.Target.Id) != 1
                    || !a.Target.Type.Equals(a.Value.Type) || a.Target.Width != a.Value.Width
                    || ManagedValues.Walk(a.Value).OfType<LocalValue>().Any(v => !locals.ContainsKey(v.Id))) return missing;
                locals.Add(a.Target.Id, Normalize(a.Value));
            }
            else if (statement is ManagedStore store) operations.Add(store with { Target = Normalize(store.Target), Value = Normalize(store.Value) });
            else return missing;
        }
        FieldRef? Field(ManagedValue value) => value switch
        {
            FieldValue { Receiver: ArgumentValue { Index: -1 } } f
                when !body.Method.Method.IsStatic && !f.Field.Field.IsStatic
                    && f.Receiver.Type.Equals(body.Method.Method.Owner.IsValueType ? new ByRefRef(body.Method.DeclaringType) : body.Method.DeclaringType)
                    && f.Type.Equals(f.Field.Field.Type) => f.Field,
            StaticFieldValue f when body.Method.Method.IsStatic && f.Field.Field.IsStatic && f.Type.Equals(f.Field.Field.Type) => f.Field,
            _ => null,
        };
        var method = body.Method.Method;
        if (operations.Count == 0 && returned.Value is { } read && method.Parameters.Count == 0
            && Field(Normalize(read)) is { } getter && method.ReturnType.Equals(getter.Field.Type))
            return new(AccessorTemplateStatus.Complete, new(AccessorKind.Getter, getter));
        if (operations is [ManagedStore write] && returned.Value is null && ManagedTypes.IsVoid(method.ReturnType)
            && method.Parameters is [var parameter] && Field(write.Target) is { } setter
            && parameter.Type.Equals(setter.Field.Type) && write.Value is ArgumentValue { Index: 0 } argument
            && argument.Type.Equals(parameter.Type))
            return new(AccessorTemplateStatus.Complete, new(AccessorKind.Setter, setter));
        return missing;
    }
}

/// <summary>Lazy 的执行发布保证同一方法至多恢复一次，失败也缓存。</summary>
public sealed class CachedAccessorTemplates(Func<MethodDef, ManagedBody?> recover) : IAccessorTemplateSource
{
    private readonly ConcurrentDictionary<MethodDef, Lazy<AccessorTemplateResult>> templates = [];
    public AccessorTemplateResult Get(MethodDef method) => templates.GetOrAdd(method, m => new(() =>
        recover(m) is { } body ? AccessorTemplates.Read(body) : new(AccessorTemplateStatus.Incomplete))).Value;
}
