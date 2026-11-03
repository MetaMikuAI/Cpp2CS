using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>新对象的基类构造已下降，分配类型的构造仍待模板证明。</summary>
internal sealed record PendingConstruction(ulong Address, DefinitionRef Allocated, MethodRef Base);

internal sealed record TemplateResult(ManagedBody Body, IReadOnlyList<RecoveryHole> Holes);

/// <summary>依据其他方法的托管恢复体证明内联；不读取机器状态或类型求解器。</summary>
internal sealed partial class TemplateRecovery(ManagedTypes types, MethodRef caller,
    Func<MethodRef, MethodRecoveryResult?> summaries, FieldAccessModel fields)
{
    private readonly List<RecoveryHole> holes = [];
    private int nextLocal;

    public TemplateResult Run(ManagedBody body, IReadOnlyDictionary<Variable, PendingConstruction> constructions, int firstLocal)
    {
        holes.Clear();
        inlineFailures.Clear();
        constructionFailures.Clear();
        pendingConstructions = constructions;
        nextLocal = firstLocal;
        var recovered = InlineInverse(body);
        return new(recovered, holes.ToArray());
    }

    private int Width(TypeRef type) => types.ValueWidth(type);
    private LocalValue NewLocal(TypeRef type) => new(new Variable(Storage.Temp(1000 + nextLocal++), 1), type, Width(type));
}
