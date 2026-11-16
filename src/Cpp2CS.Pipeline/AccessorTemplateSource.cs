using System.Collections.Concurrent;
using Cpp2CS.Input;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Runtime;

namespace Cpp2CS.Pipeline;

/// <summary>候选用同一全局事实和前端独立恢复；关闭内联逆，深度固定为一。</summary>
public sealed class AccessorTemplateSource : IAccessorTemplateSource
{
    private readonly CachedAccessorTemplates templates;
    private readonly MethodTemplateSource source;
    private readonly IReadOnlyDictionary<MethodDef, CodeEntry[]> entries;
    private readonly DefinitionRef objectType;
    private readonly ConcurrentDictionary<MethodRef, Lazy<AccessorTemplateResult>> closed = [];

    public AccessorTemplateSource(GlobalFacts facts, IMethodStage<CodeEntry, NativeFunction> frontend)
    {
        source = new MethodTemplateSource(facts, frontend, constructors: false);
        templates = new(source.GetBody);
        entries = facts.CodeMap.Entries.Where(e => e.Kind == EntryKind.GenericMethod && e.Method is not null)
            .GroupBy(e => e.Method!.Method).ToDictionary(g => g.Key, g => g.ToArray());
        objectType = new(facts.Model.Types.Single(t => t.Assembly == "mscorlib.dll" && t.FullName == "System.Object"), []);
    }

    public AccessorTemplateResult Get(MethodDef method)
    {
        var result = templates.Get(method);
        return result.Status == AccessorTemplateStatus.Incomplete ? result with { Failure = source.GetFailure(method) } : result;
    }

    public AccessorTemplateResult Get(MethodRef method)
    {
        if (!AccessorTemplates.UsesClosedWitness(method.Method)) return Get(method.Method);
        if (!ManagedCSignatureBuilder.IsClosed(method) || method.TypeArguments.Concat(method.MethodArguments).Any(ManagedCSignatureBuilder.FullyShared))
            return new(AccessorTemplateStatus.Incomplete, Failure: new("inline.Accessor.Witness.Open", "现场没有完整的封闭类型实例"));
        var normalized = method with { TypeArguments = method.TypeArguments.Select(CanonicalReference).ToArray(),
            MethodArguments = method.MethodArguments.Select(CanonicalReference).ToArray() };
        var available = entries.GetValueOrDefault(method.Method) ?? [];
        var usable = available.Where(e => ManagedCSignatureBuilder.IsClosed(e.Method!)
            && !e.Method!.TypeArguments.Concat(e.Method.MethodArguments).Any(ManagedCSignatureBuilder.FullyShared)).ToArray();
        var entry = usable.Where(e => e.Method == normalized).OrderBy(e => e.Address).ThenBy(e => e.Index).FirstOrDefault()
            ?? usable.OrderBy(e => PrimitiveValues(e.Method!) ? 0 : GenericWitness.IsCanonical(e.Method!) ? 1 : 2)
                .ThenBy(e => e.Address).ThenBy(e => e.Index).FirstOrDefault();
        if (entry?.Method is not { } witness)
            return new(AccessorTemplateStatus.Incomplete, Failure: available.Length == 0
                ? new("inline.Accessor.Witness.NoEntry", "候选没有泛型实例入口")
                : new("inline.Accessor.Witness.FullyShared", "候选没有非完全共享的封闭实例入口"));
        bool borrowed = witness != normalized;
        var evidence = new Reason(borrowed ? "inline.Accessor.Witness.Assumption" : "inline.Accessor.Witness",
            (borrowed ? "借用封闭见证 " : "现场对应的封闭见证 ") + witness
                + (borrowed ? "；依赖泛型代码不按具体的类型实参分支" : ""));
        var result = closed.GetOrAdd(witness, m => new(() => source.GetBody(m) is { } body
            ? AccessorTemplates.ReadSingleField(body)
            : new(AccessorTemplateStatus.Incomplete, Failure: source.GetFailure(m)))).Value;
        return result with { Witness = evidence, Failure = result.Failure is { } failure
            ? failure with { Cause = evidence with { Cause = failure.Cause } } : null };
    }

    private TypeRef CanonicalReference(TypeRef type) => ManagedTypes.IsReferenceType(type) ? objectType : type;
    private static bool PrimitiveValues(MethodRef method) => GenericWitness.IsValueInstance(method)
        && method.TypeArguments.Concat(method.MethodArguments).Where(t => t is DefinitionRef { Definition.IsValueType: true })
            .All(t => ManagedTypes.PrimitiveName(t) is not null);
}
