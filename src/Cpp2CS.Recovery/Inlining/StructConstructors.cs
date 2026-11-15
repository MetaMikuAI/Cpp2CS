using System.Collections.Concurrent;
using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Native;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Locations;

namespace Cpp2CS.Recovery.Inlining;

public sealed record StructConstructorTemplate(DefinitionRef Type, IReadOnlyList<(ValueProjection Projection, ManagedValue Value)> Leaves);
public sealed record StructConstructorTemplateResult(StructConstructorTemplate? Template, Reason? Failure);

/// <summary>只接受写入 this 的无事件模板；this 链在同一摘要内展开，未写叶子保持零。</summary>
public sealed class StructConstructorTemplates(ManagedTypes types, IMethodTemplateSource source)
{
    private readonly ConcurrentDictionary<MethodDef, StructConstructorTemplateResult> cache = [];
    public StructConstructorTemplateResult Get(MethodDef method) => cache.GetOrAdd(method, m => Read(m, []));
    private static StructConstructorTemplateResult No(string code, string text, Reason? cause = null) =>
        new(null, new("inline.StructConstructor." + code, text, cause));
    private StructConstructorTemplateResult Read(MethodDef method, HashSet<MethodDef> active)
    {
        if (!active.Add(method)) return No("Recursive", "this 构造链成环。");
        var body = source.GetBody(method);
        if (body is null) return No("Incomplete", "构造函数没有完整模板。", source.GetFailure(method));
        if (method is not { Name: ".ctor", IsStatic: false, Owner.IsValueType: true } || method.GenericParameters.Count != 0)
            return No("Signature", "候选不是值类型的实例构造函数。");
        if (body.Method.DeclaringType is not DefinitionRef type || type.Arguments.Any(ContainsParameter))
            return No("Generic", "含类型参数的结构体不提供构造模板。");
        if (MethodTemplateStatements.Read(body) is not { } statements || statements.LastOrDefault() is not ManagedReturn { Value: null })
            return No("Events", "构造模板含分支、异常区域或非直线返回。");
        var projections = types.Projections(type).OrderBy(p => p.Bit).ToArray();
        if (projections.Zip(projections.Skip(1)).Any(p => p.First.Bit + p.First.Width > p.Second.Bit)) return No("Incomplete", "构造模板布局含重叠叶子。");
        var leaves = projections.ToDictionary(p => p.Bit, p => (ManagedValue)new ConstantValue(0, p.Type, types.ValueWidth(p.Type)));
        var locals = new Dictionary<LocalId, ManagedValue>();
        ManagedValue Expand(ManagedValue value)
        {
            if (value is LocalValue local && locals.TryGetValue(local.Id, out var saved)) return saved;
            var expanded = ManagedValues.Map(value, Expand);
            return expanded is ConversionValue ? ConstructorTemplates.Normalize(expanded, types) : expanded;
        }
        foreach (var statement in statements.SkipLast(1))
        {
            if (statement is ManagedAssignment assignment && !assignment.ExceptionArrival && !locals.ContainsKey(assignment.Target.Id))
            {
                var value = Expand(assignment.Value);
                if (!Pure(body.Method, value)) return No("Events", "构造局部含读取、调用或非纯项。");
                locals.Add(assignment.Target.Id, value); continue;
            }
            if (statement is ManagedCall { Result: null, Invocation: { Virtual: false, Receiver: ArgumentValue { Index: -1 } } call }
                && call.Method.Method.Name == ".ctor" && call.Method.DeclaringType.Equals(type))
            {
                var arguments = call.Arguments.Select(Expand).ToArray();
                if (arguments.Any(a => !Pure(body.Method, a))) return No("Events", "this 链的实参含读取或事件。");
                var nested = Read(call.Method.Method, new(active));
                if (nested.Template is null) return nested;
                ManagedValue Replace(ManagedValue v) => v is ArgumentValue { Index: >= 0 } a ? arguments[a.Index] : ManagedValues.Map(v, Replace);
                foreach (var leaf in nested.Template.Leaves) leaves[leaf.Projection.Bit] = Replace(leaf.Value);
                continue;
            }
            if (statement is not ManagedStore store) return No("Events", "构造模板含调用、读取或其他事件。");
            var target = Expand(store.Target); var input = Expand(store.Value);
            var path = Path(target, out var root);
            if (root is not ArgumentValue { Index: -1 } || (path.Count == 0 ? !target.Type.Equals(type) : types.Project(type, path) is null))
                return No("Events", "构造模板写入 this 之外的位置。");
            foreach (var leaf in projections.Where(p => p.Path.Take(path.Count).SequenceEqual(path)))
            {
                ManagedValue scalar;
                if (leaf.Path.Count == path.Count) scalar = input;
                else if (input.Type is DefinitionRef nested && types.Project(nested, leaf.Path.Skip(path.Count).ToArray()) is { } projection
                    && ManagedProjections.Project(types, input, projection, f => f) is { } projected) scalar = projected.Value;
                else return No("Incomplete", "结构体字段写入不能逐叶子投影。");
                if (!Pure(body.Method, scalar)) return No("Events", "构造写入值含引用读取、调用或非纯项。");
                leaves[leaf.Bit] = scalar;
            }
        }
        return new(new(type, projections.Select(p => (p, leaves[p.Bit])).ToArray()), null);
    }
    internal static bool ContainsParameter(TypeRef type) => type switch
    {
        GenericParameterRef => true, DefinitionRef d => d.Arguments.Any(ContainsParameter) || d.Arguments.Count != d.Definition.GenericParameters.Count,
        ArrayRef a => ContainsParameter(a.Element), ByRefRef b => ContainsParameter(b.Element), PointerRef p => ContainsParameter(p.Element), _ => false,
    };
    internal static IReadOnlyList<FieldRef> Path(ManagedValue value, out ManagedValue root)
    {
        var fields = new List<FieldRef>();
        while (true)
        {
            if (value is FieldValue field) { fields.Insert(0, field.Field); value = field.Receiver; }
            else if (value is AddressValue address) value = address.Target;
            else if (value is IndirectValue indirect) value = indirect.Address;
            else break;
        }
        root = value; return fields;
    }
    internal bool Pure(MethodRef method, ManagedValue value)
    {
        if (value is ComposedValue composed) return composed.Leaves.All(leaf => Pure(method, leaf.Value));
        bool valid = true;
        ManagedValue Scalar(ManagedValue v)
        {
            if (v is FieldValue)
            {
                var path = Path(v, out var root);
                if (root is ArgumentValue { Index: >= 0 } a && a.Type is DefinitionRef type && types.Kind(type) == TypeKind.Struct
                    && types.Project(type, path) is not null) return new ArgumentValue(a.Index, v.Type, v.Width);
                valid = false; return v;
            }
            return ManagedValues.Map(v, Scalar);
        }
        if (value is ArgumentValue { Index: >= 0 } argument && types.Kind(argument.Type) == TypeKind.Struct) return true;
        var scalar = Scalar(value);
        return valid && !ManagedValues.Walk(scalar).Any(v => v is FieldValue or StaticFieldValue or ArgumentValue { Index: -1 })
            && AccessorTemplates.IsPure(method, scalar);
    }
}

public sealed record StructConstructorArgument(BoundSource Source, TypeRef Type, Point Point)
{
    public StructOrigin? Origin { get; init; }
}
public sealed record StructConstructorAnswer(MethodRef? Method, IReadOnlyList<StructConstructorArgument> Arguments, Reason? Failure);
public readonly record struct StructConstructorRequest(MethodRef Caller, DefinitionRef Type, ImmutableArray<StructLeaf> Leaves, Point Point);

/// <summary>实参只取现场项及其子项；每种代入逐叶子用公共纯项解释器复核，并保留所有成立的解。</summary>
public sealed class StructConstructorQuery(ManagedTypes types, StructConstructorTemplates templates, StateQueries state,
    IReadOnlyList<StructOrigin> origins) : Query<StructConstructorRequest, StructConstructorAnswer>
{
    private readonly SourceRangeQuery ranges = new(state);
    private readonly FlowQueries flow = new();
    public override Outcome<StructConstructorAnswer> Compute(QueryContext c, StructConstructorRequest key)
    {
        Outcome<StructConstructorAnswer> No(Reason? why) => Outcome<StructConstructorAnswer>.Success(new(null, [], why));
        if (StructConstructorTemplates.ContainsParameter(key.Type)) return No(new("inline.StructConstructor.Generic", "含类型参数的结构体不作候选。"));
        var pool = SnapshotRewrite.Dependencies(key.Leaves.Select(l => l.Value)).Where(t => t.Width <= 64 && !t.ContainsUndefined).ToArray();
        var matches = new List<StructConstructorAnswer>(); Reason? failure = null; int validTemplates = 0;
        foreach (var method in key.Type.Definition.Methods.Where(m => m is { Name: ".ctor", IsStatic: false }))
        {
            var selected = new MethodRef(method, key.Type.Arguments, []);
            if (!ManagedAccess.Method(types, key.Caller.Method.Owner, selected, key.Type)) continue;
            if (method.Parameters.Any(p => types.Kind(selected.Concrete(p.Type)) == TypeKind.Struct
                ? !origins.Any(o => o.Type.Equals(selected.Concrete(p.Type)))
                : !pool.Any(t => t.Width == types.StorageBits(selected.Concrete(p.Type))))) continue;
            var result = templates.Get(method);
            if (result.Template is not { } template) { failure ??= result.Failure; continue; }
            // 模板来源按定义提供；封闭泛型只有来源已给出同一封闭体时才能使用。
            if (!template.Type.Equals(key.Type)) { failure ??= new("inline.StructConstructor.Generic", "模板来源只提供开放定义，缺少封闭构造体。"); continue; }
            var used = template.Leaves.SelectMany(l => ManagedValues.Walk(l.Value)).OfType<ArgumentValue>().Select(a => a.Index).ToHashSet();
            if (Enumerable.Range(0, method.Parameters.Count).Any(i => !used.Contains(i))) continue;
            validTemplates++;
            var bindings = new StructConstructorArgument?[method.Parameters.Count];
            Term? Parameter(int i)
            {
                if (bindings[i] is not { } bound || types.Kind(bound.Type) == TypeKind.Struct) return null;
                return c.Get(ranges, new(bound.Source, bound.Point, 0, types.StorageBits(bound.Type))) is { IsSuccess: true } value ? value.Value : null;
            }
            Term? Projection(ManagedValue value)
            {
                if (value is not FieldValue) return null;
                var path = StructConstructorTemplates.Path(value, out var root);
                if (root is not ArgumentValue { Index: >= 0 } a || bindings[a.Index] is not { Type: DefinitionRef type } bound
                    || types.Kind(type) != TypeKind.Struct || types.Project(type, path) is not { } projection) return null;
                return c.Get(ranges, new(bound.Source, bound.Point, projection.Bit, projection.Width)) is { IsSuccess: true } part ? part.Value : null;
            }
            var interpreter = new AccessorTerms(c.Snapshot.Terms, Parameter, (_, _) => null, projection: Projection);
            bool Equal(bool complete)
            {
                foreach (var leaf in template.Leaves)
                {
                    var actual = key.Leaves.SingleOrDefault(l => l.Projection.Bit == leaf.Projection.Bit && l.Projection.Width == leaf.Projection.Width);
                    if (actual is null) return false;
                    var expected = interpreter.Read(leaf.Value);
                    if (expected is null) { if (complete) return false; continue; }
                    if (interpreter.Resize(expected, leaf.Projection.Width) != actual.Value) return false;
                }
                return true;
            }
            Reason? budget = null;
            void Bind(int i)
            {
                if (budget is not null) return;
                if (c.Step() is { } exhausted) { budget = exhausted; return; }
                if (i == bindings.Length)
                {
                    if (Equal(true)) matches.Add(new(selected, bindings.Select(b => b!).ToArray(), null));
                    return;
                }
                var type = selected.Concrete(method.Parameters[i].Type);
                IEnumerable<StructConstructorArgument> choices = types.Kind(type) == TypeKind.Struct
                    ? origins.Where(o => o.Type.Equals(type) && (o.Point == key.Point || c.Get(flow.PointDominates, new(o.Point, key.Point)) is { IsSuccess: true, Value: true }))
                        .Select(o => new StructConstructorArgument(o.Source, type, o.Parameter is not null ? key.Point : o.Point) { Origin = o })
                    : pool.Where(t => t.Width == types.StorageBits(type)).Select(t => new StructConstructorArgument(new TermSource(t), type, key.Point));
                foreach (var choice in choices.Distinct())
                {
                    bindings[i] = choice;
                    if (Equal(false)) Bind(i + 1);
                    bindings[i] = null;
                }
            }
            Bind(0);
            if (budget is not null) return Outcome<StructConstructorAnswer>.Failure(budget);
        }
        if (matches.Count > 1) return No(new("inline.StructConstructor.Ambiguous", $"{matches.Count} 个构造函数与实参代入成立。"));
        return matches.Count == 1 ? Outcome<StructConstructorAnswer>.Success(matches[0])
            : No(validTemplates > 0 ? new("inline.StructConstructor.NoMatch", $"{validTemplates} 个纯写入模板均不能由现场项代入成立。") : failure);
    }
}
