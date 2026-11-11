using Mono.Cecil;
using Cpp2CS.Model;
namespace Cpp2CS.Tests.Execution;
/// <summary>依据 CIL 声明、显式实现和闭合签名分派；保留调用点的方法实参。</summary>
internal sealed partial class CecilModel
{
    public MethodRef Virtual(DefinitionRef type, MethodRef target)
    {
        var contract = methodDefinitions[target.Method];
        for (var current = type; current is not null; current = current.Definition.BaseType?.Substitute(current.Arguments, []) as DefinitionRef)
        {
            Fill(current.Definition);
            foreach (var candidate in current.Definition.Methods.Where(m => m.IsVirtual))
            {
                var source = methodDefinitions[candidate];
                var instance = new MethodRef(candidate, current.Arguments, target.MethodArguments);
                var explicitMatch = source.Overrides.Any(o => Method(o).Method == target.Method);
                if (explicitMatch || candidate.Name == target.Method.Name && candidate.GenericParameters.Count == target.MethodArguments.Count
                    && candidate.Parameters.Select(p => instance.Concrete(p.Type)).SequenceEqual(target.Method.Parameters.Select(p => target.Concrete(p.Type)))
                    && (contract.DeclaringType.IsInterface || VirtualRoot(instance).Equals(VirtualRoot(target)))) return instance;
            }
        }
        throw new Unsupported($"{type} 中无法分派 {target}");
    }

    private MethodRef VirtualRoot(MethodRef method)
    {
        var source = methodDefinitions[method.Method];
        var declaration = source.Overrides.FirstOrDefault(o => !o.DeclaringType.Resolve().IsInterface);
        if (declaration is not null) return VirtualRoot(InContext(method).Method(declaration));
        if (source.IsNewSlot) return method;
        for (var parent = method.Method.Owner.BaseType?.Substitute(method.TypeArguments, []) as DefinitionRef;
            parent is not null; parent = parent.Definition.BaseType?.Substitute(parent.Arguments, []) as DefinitionRef)
        {
            Fill(parent.Definition);
            foreach (var candidate in parent.Definition.Methods.Where(m => m.IsVirtual && m.Name == method.Method.Name
                && m.GenericParameters.Count == method.MethodArguments.Count))
            {
                var instance = new MethodRef(candidate, parent.Arguments, method.MethodArguments);
                if (candidate.Parameters.Select(p => instance.Concrete(p.Type)).SequenceEqual(method.Method.Parameters.Select(p => method.Concrete(p.Type))))
                    return VirtualRoot(instance);
            }
        }
        throw new Unsupported($"找不到虚方法声明槽：{method}");
    }
}
