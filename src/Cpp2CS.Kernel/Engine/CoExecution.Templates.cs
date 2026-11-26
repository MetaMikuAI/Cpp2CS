using System.Collections.Immutable;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Kernel.Sources;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Kernel.Engine;

/// <summary>
/// 两张模板效果图的等价（设计第 15 节的 IL 对照）：恢复出的 IL 与真实 IL 都按目录展开，由同一个引擎共同执行。
/// 两侧的形参取同一组值；事件逐个同种、同操作数，事件与结局处双方写过的位置内容相同。
/// 调用有两种读法，取法与原生一侧的正向核对相同（设计 9.1、9.3）：双方调用同一个方法时它是同一个事件；
/// 否则，目标唯一的调用按“展开”读（设计 6.2），换成被调方法的效果图。
/// </summary>
public sealed partial class CoExecution
{
    /// <summary>展开的嵌套层数的上限：递归的方法在这里停下。</summary>
    private const int ExpansionDepth = 8;

    /// <summary>
    /// 一侧正在展开的一次调用的外层：调用所在的效果图、这一侧在调用之后的位置、代表调用结果的项，以及更外层的调用。
    /// </summary>
    private sealed record Caller(FlowGraph<TemplateEffect> Graph, PlacedGraph Placed, Side Continue, ImmutableArray<Term> Results, Caller? Outer)
    {
        public int Depth => Outer is null ? 1 : Outer.Depth + 1;
    }

    // 左右两侧当前所在的效果图（右侧用 template、templateGraph），以及各自外层的调用。
    // 它们随路径变化：换图之后的探索回来时恢复原值（见 Continue）。
    private FlowGraph<TemplateEffect>? leftTemplate;
    private PlacedGraph? leftGraph;
    private Caller? leftCaller, rightCaller;

    private readonly Func<EntityRef, int, FlowGraph<TemplateEffect>?>? callees;
    private readonly Dictionary<EntityRef, (FlowGraph<TemplateEffect>? Graph, PlacedGraph? Placed, string Reason)>? expansions;
    private int nextGraph;

    private CoExecution(FlowGraph<TemplateEffect> left, FlowGraph<TemplateEffect> right, MethodBody body, INativeFacts facts,
        Func<EntityRef, int, FlowGraph<TemplateEffect>?>? callees, int budget)
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
        this.callees = callees;
        expansions = [];
        nextGraph = Math.Max(left.Graph, right.Graph) + 1;
        terms = left.Terms;
    }

    /// <summary>
    /// 核对两张按目录展开的效果图是否等价。两张图须建在同一个项池里，图号不同；body 给出它们共同的签名
    /// （以及这个方法是不是类型初始化器）。
    /// callees 按方法给出它自己的方法体按目录展开的效果图，建在同一个项池里，图号用传入的那一个；
    /// 调用的含义不全在方法体里的方法（没有 IL 方法体，或调用还带加锁）给空，方法体不能展开时抛出 <see cref="ExpansionException"/>。
    /// 没有 callees 时不展开调用。
    /// </summary>
    public static ProofResult Equivalent(FlowGraph<TemplateEffect> left, FlowGraph<TemplateEffect> right, MethodBody body, INativeFacts facts,
        Func<EntityRef, int, FlowGraph<TemplateEffect>?>? callees = null, int budget = 200_000)
    {
        var engine = new CoExecution(left, right, body, facts, callees, budget);
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
        if (onLeft.Kind == EventKind.Return && leftCaller is not null) { Resume(state, onLeft, left: true); return; }
        var onRight = Template(ref state);
        if (onRight.Kind == EventKind.Vacuous) { paths++; return; }
        if (onRight.Kind == EventKind.Fork) { Fork(state, onRight, native: false); return; }
        if (onRight.Kind == EventKind.Return && rightCaller is not null) { Resume(state, onRight, left: false); return; }
        var conditions = state.Conditions;
        switch (onLeft.Kind, onRight.Kind)
        {
            case (EventKind.Throw, EventKind.Throw) when onLeft.Exception == onRight.Exception && onLeft.Values.Length == onRight.Values.Length:
                // 抛出异常对象时，双方抛出的须是同一个对象。
                for (int i = 0; i < onLeft.Values.Length; i++)
                    if (!conditions.Same(onLeft.Values[i], onRight.Values[i]))
                        throw new Refuted(Verdict.Insufficient,
                            $"抛出的异常对象不同：左 {conditions.Evaluate(onLeft.Values[i])}，右 {conditions.Evaluate(onRight.Values[i])}");
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
            case (EventKind.Call, EventKind.Call) when SameMethod(onLeft, onRight):
            {
                // 双方调用同一个方法：这是同一个事件，操作数须逐个相同。
                for (int i = 0; i < onLeft.Values.Length; i++)
                    if (!conditions.Same(onLeft.Values[i], onRight.Values[i]))
                        throw new Refuted(Verdict.Insufficient,
                            $"调用 {onLeft.Effect!.Entity} 的第 {i} 个操作数不同：左 {conditions.Evaluate(onLeft.Values[i])}，右 {conditions.Evaluate(onRight.Values[i])}");
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
            case (EventKind.Allocate, EventKind.Allocate) when onLeft.Effect!.Entity == onRight.Effect!.Entity:
            {
                // 新对象：同一个事件，双方的结果是同一个新引用，非空；该类的初始化已触发。此后是新的历元。
                CompareWrites(state);
                var (mine, theirs) = (leftGraph!.Results(onLeft.Occurrence)[0], templateGraph.Results(onRight.Occurrence)[0]);
                var created = EventResult(state.Serial, 0, mine.Width);
                Explore(state with
                {
                    Native = onLeft.After! with { Env = onLeft.After.Env.SetItem(mine, created) },
                    Template = onRight.After! with { Env = onRight.After.Env.SetItem(theirs, created) },
                    Conditions = conditions.WithInitialized(onLeft.Effect.Entity!.Value).With(terms.Eq(created, terms.Zero(created.Width)), false)!,
                    Epoch = state.Epoch + 1, Serial = state.Serial + 1, NativeWrites = [], TemplateWrites = [],
                });
                return;
            }
        }
        // 不是同一个事件。其中一侧是调用时按“展开”读它，再对照；两侧都不能展开才是不同。
        var reasons = new List<string>();
        if (ExpandCall(state, onLeft, left: true, reasons) || ExpandCall(state, onRight, left: false, reasons)) return;
        string difference = onLeft.Kind == EventKind.Call && onRight.Kind == EventKind.Call
            ? $"调用不同：左 {onLeft.Effect!.Entity}，右 {onRight.Effect!.Entity}"
            : $"事件不同：左 {Name(onLeft)}，右 {Name(onRight)}";
        throw new Refuted(Verdict.Insufficient, reasons.Count == 0 ? difference : $"{difference}（{string.Join("；", reasons)}）");
    }

    /// <summary>两次调用的是同一个方法（间接调用时，方法操作数相同，目标是操作数之一）。</summary>
    private static bool SameMethod(Event onLeft, Event onRight)
    {
        var (mine, theirs) = (onLeft.Effect!, onRight.Effect!);
        return mine.Entity == theirs.Entity && mine.Indirect == theirs.Indirect && onLeft.Values.Length == onRight.Values.Length;
    }

    /// <summary>
    /// 把一侧的一次调用读成被调方法的效果图（设计 6.2 的“展开”）。成立的条件（设计 9.1）：目标唯一，即调用的不是一个值；
    /// 被调方法有按目录展开的方法体。形参绑定到调用的操作数，它的读写记在这一侧，它抛出的异常就是这一侧抛出的异常；
    /// 它返回时见 <see cref="Resume"/>。调用点的类初始化是调用之前的另一个效果，不随展开消失，仍须与另一侧对上。
    /// 不能展开时返回假，原因记入 reasons。
    /// </summary>
    private bool ExpandCall(State state, Event call, bool left, List<string> reasons)
    {
        if (call.Kind != EventKind.Call) return false;
        var effect = call.Effect!;
        string side = left ? "左" : "右";
        if (effect.Indirect)
        {
            reasons.Add($"{side}侧调用的目标不唯一，不能展开");
            return false;
        }
        var method = effect.Entity!.Value;
        var (graph, placed, reason) = CalleeGraph(method);
        if (graph is null)
        {
            reasons.Add($"{side}侧的 {method} 不能展开：{reason}");
            return false;
        }
        var outer = left ? leftCaller : rightCaller;
        if (outer is { Depth: >= ExpansionDepth }) throw new Refuted(Verdict.Insufficient, $"展开 {method} 时嵌套超过 {ExpansionDepth} 层");
        var parameters = graph.EntryParameters;
        var env = ImmutableDictionary<Term, Term>.Empty;
        bool fits = parameters.Length == call.Values.Length;
        foreach (var parameter in parameters)
        {
            int index = parameter.Slot.Index;
            if (!fits || index >= call.Values.Length || call.Values[index].Width != parameter.Width) { fits = false; break; }
            env = env.SetItem(parameter, call.Values[index]);
        }
        if (!fits)
        {
            reasons.Add($"{side}侧的 {method} 不能展开：方法体的形参与调用的操作数不符");
            return false;
        }
        var caller = left
            ? new Caller(leftTemplate!, leftGraph!, call.After!, leftGraph!.Results(call.Occurrence), outer)
            : new Caller(template, templateGraph, call.After!, templateGraph.Results(call.Occurrence), outer);
        Continue(state with { Inlines = state.Inlines + 1 }, left, graph, placed!, caller,
            new Side(graph.Entry, 0, env, ImmutableDictionary<int, int>.Empty));
        return true;
    }

    /// <summary>被展开的方法返回：返回值绑定到调用的结果，这一侧回到调用所在的效果图，从调用之后继续。</summary>
    private void Resume(State state, Event returned, bool left)
    {
        var caller = (left ? leftCaller : rightCaller)!;
        if (returned.Values.Length != caller.Results.Length) throw new Refuted(Verdict.Insufficient, "被展开方法的返回值与调用的结果个数不同");
        var env = caller.Continue.Env;
        for (int k = 0; k < caller.Results.Length; k++)
        {
            if (returned.Values[k].Width != caller.Results[k].Width) throw new Refuted(Verdict.Insufficient, "被展开方法的返回值与调用的结果位宽不同");
            env = env.SetItem(caller.Results[k], returned.Values[k]);
        }
        Continue(state, left, caller.Graph, caller.Placed, caller.Outer, caller.Continue with { Env = env });
    }

    /// <summary>一侧换到另一张效果图的某个位置之后继续探索；回来时恢复两侧的图与外层调用，同一个分叉的其余路径不受影响。</summary>
    private void Continue(State state, bool left, FlowGraph<TemplateEffect> graph, PlacedGraph placed, Caller? caller, Side side)
    {
        var saved = (leftTemplate, leftGraph, leftCaller, template, templateGraph, rightCaller);
        if (left)
        {
            (leftTemplate, leftGraph, leftCaller) = (graph, placed, caller);
            state = state with { Native = side };
        }
        else
        {
            (template, templateGraph, rightCaller) = (graph, placed, caller);
            state = state with { Template = side };
        }
        Explore(state);
        (leftTemplate, leftGraph, leftCaller, template, templateGraph, rightCaller) = saved;
    }

    /// <summary>被调方法按目录展开的效果图；每个方法只取一次。不能展开时图为空，附原因。</summary>
    private (FlowGraph<TemplateEffect>? Graph, PlacedGraph? Placed, string Reason) CalleeGraph(EntityRef method)
    {
        if (expansions!.TryGetValue(method, out var known)) return known;
        FlowGraph<TemplateEffect>? graph = null;
        string reason = "没有它的方法体";
        if (callees is not null)
        {
            int number = nextGraph++;
            try
            {
                graph = callees(method, number);
            }
            catch (ExpansionException e)
            {
                reason = e.Message;
            }
            if (graph is not null && (!ReferenceEquals(graph.Terms, terms) || graph.Graph != number))
                throw new ArgumentException("被调方法的效果图须建在同一个项池里，图号用传入的那一个");
        }
        known = graph is null ? (null, null, reason) : (graph, new PlacedGraph(graph), "");
        expansions.Add(method, known);
        return known;
    }
}
