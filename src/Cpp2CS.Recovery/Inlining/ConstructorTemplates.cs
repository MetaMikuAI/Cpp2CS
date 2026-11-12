using Cpp2CS.Managed;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>同一前端与全局事实按需完整恢复；递归截断不提供模板。</summary>
public interface IMethodTemplateSource
{
    ManagedBody? GetBody(MethodDef method);
}

/// <summary>只接受无操作的根对象构造，或唯一一次对 this 的空基类构造调用。</summary>
public sealed class ConstructorTemplates(IMethodTemplateSource source, ManagedTypes types)
{
    private readonly object gate = new();
    private readonly Dictionary<MethodDef, bool> cache = [];
    private readonly HashSet<MethodDef> active = [];
    public bool IsEmpty(MethodDef method)
    {
        lock (gate)
        {
            if (cache.TryGetValue(method, out var empty)) return empty;
            if (!active.Add(method)) return false;
            var chain = new HashSet<TypeDef>();
            TypeRef? ancestor = MethodRef.Open(method).DeclaringType;
            while (ancestor is DefinitionRef type && chain.Add(type.Definition)) ancestor = Parent(ancestor);
            var body = ancestor is null ? source.GetBody(method) : null;
            empty = body is not null && Read(body);
            active.Remove(method);
            cache.Add(method, empty);
            return empty;
        }
    }
    private bool Read(ManagedBody body)
    {
        var method = body.Method.Method;
        if (method is not { Name: ".ctor", IsStatic: false, Owner.IsValueType: false }
            || method.Parameters.Count != 0 || method.GenericParameters.Count != 0 || body.Regions.Count != 0) return false;
        if (MethodTemplateStatements.Read(body) is not { } statements) return false;
        if (statements is [ManagedReturn { Value: null }])
            return method.Owner.BaseType is null && body.Method.DeclaringType.Equals(types.Object);
        if (statements is not [ManagedCall { Result: null, Invocation: { Virtual: false, Receiver: ArgumentValue { Index: -1 } self, Arguments.Count: 0 } invocation }, ManagedReturn { Value: null }]) return false;
        var parent = Parent(body.Method.DeclaringType);
        return parent is not null && invocation.Method.DeclaringType.Equals(parent)
            && self.Type.Equals(body.Method.DeclaringType) && IsEmpty(invocation.Method.Method);
    }
    public static TypeRef? Parent(TypeRef type) => type is DefinitionRef d ? d.Definition.BaseType?.Substitute(d.Arguments, []) : null;
}
