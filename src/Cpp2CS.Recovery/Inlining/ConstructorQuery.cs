using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Inlining;

public enum ConstructorAnchor { Base, Allocation }
public sealed record ConstructorAccess(MethodRef Caller, ulong Position, TypeRef Type, ConstructorAnchor Anchor);
public sealed record ConstructorAnswer(MethodRef? Method, Reason? Failure);
public sealed record ConstructorAttempt(ConstructorAccess Access, ConstructorAnswer Answer);

/// <summary>声明的实例构造必须唯一、无参、可访问，并由完整恢复体证明为空。</summary>
public sealed class ConstructorQuery(ManagedTypes types, ConstructorTemplates templates, Action<ConstructorAttempt>? observe = null)
{
    public ConstructorAnswer Resolve(ConstructorAccess access)
    {
        var answer = Find(access);
        observe?.Invoke(new(access, answer));
        return answer;
    }
    public void Reject(ConstructorAccess access, Reason reason) => observe?.Invoke(new(access, new(null, reason)));
    private ConstructorAnswer Find(ConstructorAccess access)
    {
        bool baseCall = access.Anchor == ConstructorAnchor.Base;
        string prefix = "inline.Constructor." + (baseCall ? "Base" : "");
        ConstructorAnswer No(string suffix, string message) => new(null, new(prefix + suffix, message));
        if (access.Type is not DefinitionRef type || type.Definition.IsValueType)
            return No("Template", "构造类型没有引用类型定义。");
        var candidates = type.Definition.Methods.Where(m => m is { Name: ".ctor", IsStatic: false }).ToArray();
        if (candidates.Length > 1) return No("Ambiguous", $"类型声明了 {candidates.Length} 个实例构造函数，不能区分被内联的目标。");
        if (candidates is not [var candidate]) return No("Template", "类型没有实例构造函数定义。");
        var selected = new MethodRef(candidate, type.Arguments, []);
        if (candidate.Parameters.Count != 0 || candidate.GenericParameters.Count != 0
            || !templates.IsEmpty(candidate)
            || !ManagedAccess.Method(types, access.Caller.Method.Owner, selected, baseCall ? access.Caller.DeclaringType : access.Type))
            return No("Template", "唯一构造函数有形参、不可访问、未能恢复或模板不为空。");
        return new(selected, null);
    }

    /// <summary>只对完全没有 this 初始化候选的构造补调用；非直接接收者与多个见证保持原洞。</summary>
    public ConstructorAnswer Initialization(MethodRef caller, IReadOnlyList<ManagedBlock> blocks)
    {
        var parent = ConstructorTemplates.Parent(caller.DeclaringType);
        var witness = InitializationWitness(caller, blocks);
        if (witness == 1) return new(null, null);
        if (witness != 0) return new(null, new("lowering.ConstructorInitialization", "引用类型构造函数没有唯一的直接 this 初始化调用见证。"));
        if (parent is null && caller.DeclaringType.Equals(types.Object)) return new(null, null);
        var access = new ConstructorAccess(caller, 0, parent ?? caller.DeclaringType, ConstructorAnchor.Base);
        var answer = Find(access);
        if (answer.Method is not null && blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Any(c =>
            c.Invocation.Method.Method is { Name: ".ctor", IsStatic: false, Owner.IsValueType: false }
            && types.IsAssignable(caller.DeclaringType, c.Invocation.Method.DeclaringType)))
            answer = new(null, new("lowering.ConstructorInitialization", "仍有可能初始化 this 的祖先构造调用，不能重复补入基类调用。"));
        observe?.Invoke(new(access, answer));
        return answer;
    }
    public static int InitializationWitness(MethodRef caller, IEnumerable<ManagedBlock> blocks)
    {
        var parent = ConstructorTemplates.Parent(caller.DeclaringType);
        var calls = blocks.SelectMany(b => b.Statements).OfType<ManagedCall>()
            .Where(c => c.Invocation.Method.Method is { Name: ".ctor", IsStatic: false }).ToArray();
        var candidates = calls.Where(c => !c.Invocation.Virtual
            && (c.Invocation.Method.DeclaringType.Equals(caller.DeclaringType) || c.Invocation.Method.DeclaringType.Equals(parent))).ToArray();
        return candidates is [{ Invocation.Receiver: ArgumentValue { Index: -1 } }] ? 1 : candidates.Length == 0 ? 0 : -1;
    }

}
