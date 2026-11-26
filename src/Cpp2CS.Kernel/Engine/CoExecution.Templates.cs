using System.Collections.Immutable;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Kernel.Sources;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Kernel.Engine;

/// <summary>
/// 两张模板效果图的等价（设计第 15 节的 IL 对照）：恢复出的 IL 与真实 IL 都按目录展开，由同一个引擎共同执行。
/// 两侧的形参取同一组值；事件逐个同种、同操作数，事件与结局处双方写过的位置内容相同。
/// </summary>
public sealed partial class CoExecution
{
    private FlowGraph<TemplateEffect>? leftTemplate;
    private PlacedGraph? leftGraph;

    private CoExecution(FlowGraph<TemplateEffect> left, FlowGraph<TemplateEffect> right, MethodBody body, INativeFacts facts, int budget)
    {
        if (!ReferenceEquals(left.Terms, right.Terms)) throw new ArgumentException("两侧须共用一个项池");
        if (left.Graph == right.Graph) throw new ArgumentException("两张图的图号须不同");
        native = null!;
        nativeGraph = null!;
        stackPointer = null!;
        leftTemplate = left;
        leftGraph = new PlacedGraph(left);
        template = right;
        templateGraph = new PlacedGraph(right);
        this.body = body;
        this.facts = facts;
        this.budget = budget;
        terms = left.Terms;
    }

    /// <summary>
    /// 核对两张按目录展开的效果图是否等价。两张图须建在同一个项池里，图号不同；body 给出它们共同的签名
    /// （以及这个方法是不是类型初始化器）。
    /// </summary>
    public static ProofResult Equivalent(FlowGraph<TemplateEffect> left, FlowGraph<TemplateEffect> right, MethodBody body, INativeFacts facts,
        int budget = 200_000)
    {
        var engine = new CoExecution(left, right, body, facts, budget);
        try
        {
            engine.RunTemplates();
            return new(Verdict.Proved, "", engine.paths, engine.steps, [.. engine.assumptions]);
        }
        catch (Refuted refuted)
        {
            return new(refuted.Verdict, refuted.Message, engine.paths, engine.steps, [.. engine.assumptions]);
        }
    }

    private void RunTemplates()
    {
        var method = body.Method;
        var conditions = PathConditions.Empty(terms);
        ImmutableDictionary<Term, Term> leftEnv = ImmutableDictionary<Term, Term>.Empty, rightEnv = leftEnv;
        foreach (var parameter in template.EntryParameters)
        {
            int index = parameter.Slot.Index;
            Term value = leftTemplate!.EntryParameters.First(p => p.Slot.Index == index);
            if (value.Width != parameter.Width) throw new Refuted(Verdict.Insufficient, $"两侧第 {index} 个形参的位宽不同");
            // 入口事实（设计 7.7）：C++ 的 bool 只取 0 与 1；实例方法的 this 非空。
            if (method.Parameters[index].TwoValued)
            {
                var two = terms.ZeroExtend(terms.Slice(value, 0, 1), value.Width);
                leftEnv = leftEnv.SetItem(value, two);
                value = two;
            }
            rightEnv = rightEnv.SetItem(parameter, value);
            if (index == 0 && method.HasThis) conditions = conditions.With(terms.Eq(value, terms.Zero(value.Width)), false)!;
        }
        if (body.InitializerOf is { } initialized) conditions = conditions.WithInitialized(initialized);
        var none = ImmutableDictionary<int, int>.Empty;
        Explore(new State(new Side(leftTemplate!.Entry, 0, leftEnv, none), new Side(template.Entry, 0, rightEnv, none),
            conditions, Epoch: 1, Serial: 0, FrameGeneration: 0, [], [], ImmutableDictionary<long, Term>.Empty));
    }

    /// <summary>左侧的模板走到它的下一个事件：与右侧是同一段推进逻辑，两侧的位置与写入对调后执行。</summary>
    private Event Left(ref State state)
    {
        (template, templateGraph, leftTemplate, leftGraph) = (leftTemplate!, leftGraph!, template, templateGraph);
        var swapped = state with { Native = state.Template, Template = state.Native, NativeWrites = state.TemplateWrites, TemplateWrites = state.NativeWrites };
        var reached = Template(ref swapped);
        state = swapped with { Native = swapped.Template, Template = swapped.Native, NativeWrites = swapped.TemplateWrites, TemplateWrites = swapped.NativeWrites };
        (template, templateGraph, leftTemplate, leftGraph) = (leftTemplate!, leftGraph!, template, templateGraph);
        return reached;
    }

    private void ExploreTemplates(State state)
    {
        var onLeft = Left(ref state);
        if (onLeft.Kind == EventKind.Vacuous) { paths++; return; }
        if (onLeft.Kind == EventKind.Fork) { Fork(state, onLeft, native: true); return; }
        var onRight = Template(ref state);
        if (onRight.Kind == EventKind.Vacuous) { paths++; return; }
        if (onRight.Kind == EventKind.Fork) { Fork(state, onRight, native: false); return; }
        var conditions = state.Conditions;
        switch (onLeft.Kind, onRight.Kind)
        {
            case (EventKind.Throw, EventKind.Throw) when onLeft.Exception == onRight.Exception:
                CompareWrites(state);
                paths++;
                return;
            case (EventKind.Return, EventKind.Return) when onLeft.Values.Length == onRight.Values.Length:
                for (int i = 0; i < onLeft.Values.Length; i++)
                    if (!conditions.Same(onLeft.Values[i], onRight.Values[i]))
                        throw new Refuted(Verdict.Insufficient,
                            $"返回值不同：左 {conditions.Evaluate(onLeft.Values[i])}，右 {conditions.Evaluate(onRight.Values[i])}");
                CompareWrites(state);
                paths++;
                return;
            case (EventKind.Call, EventKind.Call):
            {
                var (mine, theirs) = (onLeft.Effect!, onRight.Effect!);
                if (mine.Entity != theirs.Entity || mine.Indirect != theirs.Indirect || onLeft.Values.Length != onRight.Values.Length)
                    throw new Refuted(Verdict.Insufficient, $"调用不同：左 {mine.Entity}，右 {theirs.Entity}");
                for (int i = 0; i < onLeft.Values.Length; i++)
                    if (!conditions.Same(onLeft.Values[i], onRight.Values[i]))
                        throw new Refuted(Verdict.Insufficient,
                            $"调用 {mine.Entity} 的第 {i} 个操作数不同：左 {conditions.Evaluate(onLeft.Values[i])}，右 {conditions.Evaluate(onRight.Values[i])}");
                CompareWrites(state);
                // 同一个事件：双方的结果相互绑定。此后是新的历元。
                var (leftResults, rightResults) = (leftGraph!.Results(onLeft.Occurrence), templateGraph.Results(onRight.Occurrence));
                var (leftEnv, rightEnv) = (onLeft.After!.Env, onRight.After!.Env);
                for (int k = 0; k < leftResults.Length; k++)
                {
                    var result = EventResult(state.Serial, k, leftResults[k].Width);
                    leftEnv = leftEnv.SetItem(leftResults[k], result);
                    rightEnv = rightEnv.SetItem(rightResults[k], result);
                }
                Explore(state with
                {
                    Native = onLeft.After with { Env = leftEnv }, Template = onRight.After with { Env = rightEnv },
                    Epoch = state.Epoch + 1, Serial = state.Serial + 1, NativeWrites = [], TemplateWrites = [],
                });
                return;
            }
            case (EventKind.Initialize, EventKind.Initialize) when onLeft.Effect!.Entity == onRight.Effect!.Entity:
                CompareWrites(state);
                Explore(state with
                {
                    Native = onLeft.After!, Template = onRight.After!, Conditions = conditions.WithInitialized(onLeft.Effect.Entity!.Value),
                    Epoch = state.Epoch + 1, Serial = state.Serial + 1, NativeWrites = [], TemplateWrites = [],
                });
                return;
            default:
                throw new Refuted(Verdict.Insufficient, $"事件不同：左 {Name(onLeft)}，右 {Name(onRight)}");
        }
    }
}
