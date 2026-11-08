using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>新对象的基类构造已下降，分配类型的构造仍待模板证明。</summary>
internal sealed record PendingConstruction(ulong Address, DefinitionRef Allocated, MethodRef Base);

/// <summary>模板证明的结果；Rules 是按原生代码直接写出的访问（inline.unfolded）与成立的内联证明（inline.proof）。</summary>
internal sealed record TemplateResult(ManagedBody Body, IReadOnlyList<RecoveryHole> Holes, IReadOnlyList<Cpp2CS.Diagnostics.RuleTrace> Rules);

/// <summary>依据其他方法的托管恢复体证明内联；不读取机器状态或类型求解器。</summary>
internal sealed partial class TemplateRecovery(ManagedTypes types, MethodRef caller,
    Func<MethodRef, MethodRecoveryResult?> summaries, InlineEvidence fields)
{
    private readonly List<RecoveryHole> holes = [];
    private readonly List<Cpp2CS.Diagnostics.RuleTrace> rules = [];
    private int nextLocal;

    public TemplateResult Run(ManagedBody body, IReadOnlyDictionary<Variable, PendingConstruction> constructions, int firstLocal)
    {
        holes.Clear();
        rules.Clear();
        inlineFailures.Clear();
        constructionFailures.Clear();
        pendingConstructions = constructions;
        nextLocal = firstLocal;
        var recovered = InlineInverse(body);
        return new(recovered, holes.ToArray(), rules.ToArray());
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
    /// 成立并采用的内联证明：Code 是出口的形式（exit、return、branch、uses）加上证明用到的比较形式，Detail 是模板方法。
    /// 只作诊断与按形式抽样，不影响写出。
    /// </summary>
    internal const string ProofRule = "inline.proof";

    /// <summary>采用一次替换，记下它的证明。</summary>
    private ManagedBody Adopt(InlineReplacement replaced, ManagedBody applied)
    {
        if (replaced.Proof is { } proof) rules.Add(proof);
        return applied;
    }

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
