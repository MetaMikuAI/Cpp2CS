using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>新对象的基类构造已下降，分配类型的构造仍待模板证明。</summary>
internal sealed record PendingConstruction(ulong Address, DefinitionRef Allocated, MethodRef Base);

internal sealed record TemplateResult(ManagedBody Body, IReadOnlyList<RecoveryHole> Holes, IReadOnlyList<Cpp2CS.Diagnostics.RuleTrace> Unfolded);

/// <summary>依据其他方法的托管恢复体证明内联；不读取机器状态或类型求解器。</summary>
internal sealed partial class TemplateRecovery(ManagedTypes types, MethodRef caller,
    Func<MethodRef, MethodRecoveryResult?> summaries, InlineEvidence fields)
{
    private readonly List<RecoveryHole> holes = [];
    private readonly List<Cpp2CS.Diagnostics.RuleTrace> unfolded = [];
    private int nextLocal;

    public TemplateResult Run(ManagedBody body, IReadOnlyDictionary<Variable, PendingConstruction> constructions, int firstLocal)
    {
        holes.Clear();
        unfolded.Clear();
        inlineFailures.Clear();
        constructionFailures.Clear();
        pendingConstructions = constructions;
        nextLocal = firstLocal;
        var recovered = InlineInverse(body);
        return new(recovered, holes.ToArray(), unfolded.ToArray());
    }

    /// <summary>
    /// 作模板的方法恢复体。调用方自身不作模板：它的恢复体就是这段原生代码，整段与自己比对总能成立，折回成对自己的调用会无限递归。
    /// 按原生代码直接写出了未证明访问（inline.unfolded）的同程序集方法也不作模板：它自己的访问还会去找模板，
    /// 两个方法体相同的方法会互相折回成调用；调用方本来也能按原生代码写出这些访问。别的程序集的方法可以作模板，
    /// 程序集引用无环，它不会折回成对调用方的调用。
    /// </summary>
    private MethodRecoveryResult? Template(MethodRef method) =>
        method.Method == caller.Method || summaries(method) is not { } summary
        || method.Method.Owner.Assembly == caller.Method.Owner.Assembly && summary.Rules.Any(r => r.Rule == UnfoldedRule) ? null : summary;

    internal const string UnfoldedRule = "inline.unfolded";

    /// <summary>
    /// 泛型定义的方法体取自共享实例，类型里可能还留着共享实参 object，没有代回类型形参。按原生代码直接写出的访问不经过证明，
    /// 类型必须和调用方的泛型上下文一致：调用方有类型形参，而字段所在的类型（或组成的结构体）以 object 作类型实参时不直接写出。
    /// 字段自身声明的类型里的 object 是源码写的（如 Action&lt;object&gt;），不看。
    /// </summary>
    internal static bool SharedArgument(MethodRef caller, params TypeRef[] types)
    {
        if (caller.Method.Owner.GenericParameters.Count == 0 && caller.Method.GenericParameters.Count == 0) return false;
        static bool Mentions(TypeRef type) => type switch
        {
            DefinitionRef d => d.Arguments.Any(a => a is DefinitionRef { Definition.FullName: "System.Object" } || Mentions(a)),
            ArrayRef a => Mentions(a.Element),
            ByRefRef r => Mentions(r.Element),
            PointerRef p => Mentions(p.Element),
            _ => false,
        };
        return types.Any(Mentions);
    }

    private int Width(TypeRef type) => types.ValueWidth(type);
    private LocalValue NewLocal(TypeRef type) => new(new Variable(Storage.Temp(1000 + nextLocal++), 1), type, Width(type));
}
