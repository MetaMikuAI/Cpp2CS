using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Runtime;

namespace Cpp2CS.Pipeline;

/// <summary>访问器和结构体构造共用的封闭见证选择；不改变开放定义的入口。</summary>
internal sealed class ClosedTemplateWitnesses
{
    private readonly IReadOnlyDictionary<MethodDef, CodeEntry[]> entries;
    private readonly Lazy<DefinitionRef> objectType;
    public ClosedTemplateWitnesses(GlobalFacts facts, IReadOnlyDictionary<MethodDef, CodeEntry[]>? entries = null)
    {
        this.entries = entries ?? facts.CodeMap.Entries.Where(e => e.Kind == EntryKind.GenericMethod && e.Method is not null)
            .GroupBy(e => e.Method!.Method).ToDictionary(g => g.Key, g => g.ToArray());
        objectType = new(() => new(facts.Model.Types.Single(t => t.Assembly == "mscorlib.dll" && t.FullName == "System.Object"), []));
    }
    public MethodTemplateWitness Select(MethodRef method, string code)
    {
        if (!ManagedCSignatureBuilder.IsClosed(method) || method.TypeArguments.Concat(method.MethodArguments).Any(ManagedCSignatureBuilder.FullyShared))
            return new(null, Failure: new(code + ".Open", "现场没有完整的封闭类型实例"));
        var normalized = method with { TypeArguments = method.TypeArguments.Select(CanonicalReference).ToArray(),
            MethodArguments = method.MethodArguments.Select(CanonicalReference).ToArray() };
        var available = (entries.GetValueOrDefault(method.Method) ?? []).Where(e => e.Kind == EntryKind.GenericMethod).ToArray();
        var usable = available.Where(e => ManagedCSignatureBuilder.IsClosed(e.Method!)
            && !e.Method!.TypeArguments.Concat(e.Method.MethodArguments).Any(ManagedCSignatureBuilder.FullyShared)).ToArray();
        var entry = usable.Where(e => e.Method == normalized).OrderBy(e => e.Address).ThenBy(e => e.Index).FirstOrDefault()
            ?? usable.OrderBy(e => PrimitiveValues(e.Method!) ? 0 : GenericWitness.IsCanonical(e.Method!) ? 1 : 2)
                .ThenBy(e => e.Address).ThenBy(e => e.Index).FirstOrDefault();
        if (entry?.Method is not { } witness)
            return new(null, Failure: available.Length == 0
                ? new(code + ".NoEntry", "候选没有泛型实例入口")
                : new(code + ".FullyShared", "候选没有非完全共享的封闭实例入口"));
        bool borrowed = witness != normalized;
        var evidence = new Reason(code + (borrowed ? ".Assumption" : ""),
            (borrowed ? "借用封闭见证 " : "现场对应的封闭见证 ") + witness
                + (borrowed ? "；依赖泛型代码不按具体的类型实参分支" : ""));
        return new(witness, evidence, Borrowed: borrowed);
    }
    private TypeRef CanonicalReference(TypeRef type) => ManagedTypes.IsReferenceType(type) ? objectType.Value : type;
    private static bool PrimitiveValues(MethodRef method) => GenericWitness.IsValueInstance(method)
        && method.TypeArguments.Concat(method.MethodArguments).Where(t => t is DefinitionRef { Definition.IsValueType: true })
            .All(t => ManagedTypes.PrimitiveName(t) is not null);
}
