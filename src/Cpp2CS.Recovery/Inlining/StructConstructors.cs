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

public sealed record StructConstructorTemplate(DefinitionRef Type, IReadOnlyList<(ValueProjection Projection, ManagedValue Value)> Leaves)
{
    public IReadOnlySet<int> RepresentationDependent { get; init; } = new HashSet<int>();
}
public sealed record StructConstructorTemplateResult(StructConstructorTemplate? Template, Reason? Failure)
{
    public Reason? Witness { get; init; }
}

/// <summary>只接受写入 this 的无事件模板；this 链在同一摘要内展开，未写叶子保持零。</summary>
public sealed partial class StructConstructorTemplates(ManagedTypes types, IMethodTemplateSource source)
{
    private readonly ConcurrentDictionary<MethodRef, StructConstructorTemplateResult> cache = [];
    public StructConstructorTemplateResult Get(MethodDef method) => cache.GetOrAdd(MethodRef.Open(method), m => Read(m, []));
    public StructConstructorTemplateResult Get(MethodRef method) => ContainsParameter(method.DeclaringType) ? Get(method.Method)
        : cache.GetOrAdd(method, m => Read(m, []));
    private static StructConstructorTemplateResult No(string code, string text, Reason? cause = null) =>
        new(null, new("inline.StructConstructor." + code, text, cause));
    private static Reason AppendWitness(Reason proof, Reason? tail) => proof with
    { Cause = proof.Cause is { } cause ? AppendWitness(cause, tail) : tail };
    private StructConstructorTemplateResult Read(MethodRef requested, HashSet<MethodRef> active)
    {
        var selected = ContainsParameter(requested.DeclaringType) ? new MethodTemplateWitness(requested) : source.GetWitness(requested);
        var result = selected.Method is { } witness ? ReadBody(witness, active)
            : No("Incomplete", "构造函数没有封闭模板见证。", selected.Failure);
        if (result.Template is { } template && !template.Type.Equals(requested.DeclaringType))
            result = Reproject(template, requested, selected.Borrowed);
        if (selected.Evidence is not { } evidence) return result;
        return result with { Witness = evidence with { Cause = result.Witness }, Failure = result.Failure is { } failure
            ? failure with { Cause = evidence with { Cause = failure.Cause } } : null };
    }
    private StructConstructorTemplateResult ReadBody(MethodRef method, HashSet<MethodRef> active)
    {
        if (!active.Add(method)) return No("Recursive", "结构体构造依赖成环。");
        var body = source.GetBody(method);
        if (body is null) return No("Incomplete", "构造函数没有完整模板。",
            new("inline.candidate", "候选 " + method.Method.Owner.FullName + "." + method.Method.Name, source.GetFailure(method)));
        if (method.Method is not { Name: ".ctor", IsStatic: false, Owner.IsValueType: true } || method.Method.GenericParameters.Count != 0)
            return No("Signature", "候选不是值类型的实例构造函数。");
        if (body.Method.DeclaringType is not DefinitionRef type || type.Arguments.Any(ContainsParameter))
            return No("Generic", "含类型参数的结构体不提供构造模板。");
        if (MethodTemplateStatements.Read(body) is not { } statements || statements.LastOrDefault() is not ManagedReturn { Value: null })
            return No("Events", "构造模板含分支、异常区域或非直线返回。");
        var projections = types.Projections(type).OrderBy(p => p.Bit).ToArray();
        if (projections.Zip(projections.Skip(1)).Any(p => p.First.Bit + p.First.Width > p.Second.Bit)) return No("Incomplete", "构造模板布局含重叠叶子。");
        var leaves = projections.ToDictionary(p => p.Bit, p => (ManagedValue)new ConstantValue(0, p.Type, types.ValueWidth(p.Type)));
        var locals = new Dictionary<LocalId, ManagedValue>();
        var dependent = projections.Where(p => ContainsParameter(OpenPathType(MethodRef.Open(method.Method).DeclaringType, p.Path)))
            .Select(p => p.Bit).ToHashSet();
        Reason? expansionFailure = null, nestedEvidence = null;
        bool wroteThis = false, nestedDependent = false;
        ManagedValue Expand(ManagedValue value, bool normalize = true)
        {
            if (value is LocalValue local && locals.TryGetValue(local.Id, out var saved)) value = saved;
            if (value is NewObjectValue created && types.Kind(created.Type) == TypeKind.Struct)
            {
                var arguments = created.Arguments.Select(a => Expand(a, false)).ToArray();
                if (arguments.Any(a => !Pure(body.Method, Expand(a))))
                { expansionFailure ??= new("inline.StructConstructor.Events", "嵌套构造的实参含读取、地址用途或事件。"); return value; }
                var nested = Read(created.Constructor, new(active));
                if (nested.Template is not { } table)
                { expansionFailure ??= nested.Failure; return value; }
                if (nested.Witness is { } proof) nestedEvidence = AppendWitness(proof, nestedEvidence);
                nestedDependent |= table.RepresentationDependent.Count != 0;
                ManagedValue Replace(ManagedValue v) => v is ArgumentValue { Index: >= 0 } a ? arguments[a.Index] : ManagedValues.Map(v, Replace);
                return new ComposedValue(created.Type, table.Leaves.Select(l => (l.Projection.Path, Replace(l.Value))).ToArray());
            }
            var expanded = ManagedValues.Map(value, v => Expand(v, normalize));
            return normalize && expanded is ConversionValue ? ConstructorTemplates.Normalize(expanded, types) : expanded;
        }
        foreach (var statement in statements.SkipLast(1))
        {
            if (wroteThis && ManagedValues.Of(statement).Any(ByRefRead))
                return No("ReadAfterWrite", "按引用结构体形参的读取发生在第一次写入 this 之后。");
            if (statement is ManagedAssignment assignment && !assignment.ExceptionArrival && !locals.ContainsKey(assignment.Target.Id))
            {
                var raw = Expand(assignment.Value, false); var value = Expand(raw);
                if (expansionFailure is not null) return No("Nested", "嵌套结构体构造没有纯写入模板。", expansionFailure);
                if (!Pure(body.Method, value)) return No("Events", "构造局部含读取、调用或非纯项。");
                locals.Add(assignment.Target.Id, raw); continue;
            }
            if (statement is ManagedCall { Result: null, Invocation: { Virtual: false, Receiver: ArgumentValue { Index: -1 } } call }
                && call.Method.Method.Name == ".ctor" && call.Method.DeclaringType.Equals(type))
            {
                var rawArguments = call.Arguments.Select(a => Expand(a, false)).ToArray();
                var arguments = rawArguments.Select(a => Expand(a)).ToArray();
                if (arguments.Any(a => !Pure(body.Method, a))) return No("Events", "this 链的实参含读取或事件。");
                var nested = Read(call.Method, new(active));
                if (nested.Template is null) return nested;
                if (nested.Witness is { } proof) nestedEvidence = AppendWitness(proof, nestedEvidence);
                ManagedValue Replace(ManagedValue v) => v is ArgumentValue { Index: >= 0 } a ? arguments[a.Index] : ManagedValues.Map(v, Replace);
                ManagedValue RawReplace(ManagedValue v) => v is ArgumentValue { Index: >= 0 } a ? rawArguments[a.Index] : ManagedValues.Map(v, RawReplace);
                foreach (var leaf in nested.Template.Leaves)
                {
                    leaves[leaf.Projection.Bit] = Replace(leaf.Value);
                    if (nested.Template.RepresentationDependent.Contains(leaf.Projection.Bit)
                        || !SafeBorrow(method, RawReplace(leaf.Value), leaf.Projection.Path))
                        dependent.Add(leaf.Projection.Bit);
                    else dependent.Remove(leaf.Projection.Bit);
                }
                wroteThis = true;
                continue;
            }
            if (statement is not ManagedStore store) return No("Events", "构造模板含调用、读取或其他事件。");
            var target = Expand(store.Target); var rawInput = Expand(store.Value, false); var input = Expand(rawInput);
            if (expansionFailure is not null) return No("Nested", "嵌套结构体构造没有纯写入模板。", expansionFailure);
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
                var rawScalar = rawInput;
                if (leaf.Path.Count != path.Count && rawInput.Type is DefinitionRef rawType
                    && types.Project(rawType, leaf.Path.Skip(path.Count).ToArray()) is { } rawProjection
                    && ManagedProjections.Project(types, rawInput, rawProjection, f => f) is { } rawProjected) rawScalar = rawProjected.Value;
                if (SafeBorrow(method, rawScalar, leaf.Path)) dependent.Remove(leaf.Bit);
                else dependent.Add(leaf.Bit);
            }
            wroteThis = true;
        }
        if (nestedDependent) dependent.UnionWith(projections.Select(p => p.Bit));
        return new(new(type, projections.Select(p => (p, leaves[p.Bit])).ToArray()) { RepresentationDependent = dependent }, null) { Witness = nestedEvidence };
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
            if (v is FieldValue or IndirectValue)
            {
                var path = Path(v, out var root);
                if (root is ArgumentValue { Index: >= 0 } a && StructParameter(a.Type) is { } type
                    && (path.Count == 0 ? v.Type.Equals(type) : types.Project(type, path) is not null))
                    return new ArgumentValue(a.Index, v.Type, v.Width);
                valid = false; return v;
            }
            if (v is ArgumentValue { Type: ByRefRef }) valid = false;
            return ManagedValues.Map(v, Scalar);
        }
        if (value is ArgumentValue { Index: >= 0 } argument && types.Kind(argument.Type) == TypeKind.Struct) return true;
        if (value is IndirectValue && Path(value, out var whole) is { Count: 0 }
            && whole is ArgumentValue { Index: >= 0, Type: ByRefRef } byref
            && StructParameter(byref.Type) is { } element && value.Type.Equals(element)) return true;
        var scalar = Scalar(value);
        return valid && !ManagedValues.Walk(scalar).Any(v => v is FieldValue or StaticFieldValue or ArgumentValue { Index: -1 })
            && AccessorTemplates.IsPure(method, scalar);
    }
    internal DefinitionRef? StructParameter(TypeRef type) => (type is ByRefRef byref ? byref.Element : type) is DefinitionRef structure
        && types.Kind(structure) == TypeKind.Struct ? structure : null;
    private bool ByRefRead(ManagedValue value) => ManagedValues.Walk(value).Any(v =>
    {
        if (v is not (FieldValue or IndirectValue)) return false;
        Path(v, out var root);
        return root is ArgumentValue { Index: >= 0, Type: ByRefRef } a && StructParameter(a.Type) is not null;
    });
}

public sealed record StructConstructorArgument(BoundSource Source, TypeRef Type, Point Point)
{
    public StructOrigin? Origin { get; init; }
}
public sealed record StructConstructorAnswer(MethodRef? Method, IReadOnlyList<StructConstructorArgument> Arguments, Reason? Failure)
{
    public Reason? Witness { get; init; }
}
public readonly record struct StructConstructorRequest(MethodRef Caller, DefinitionRef Type, ImmutableArray<StructLeaf> Leaves, Point Point);

/// <summary>实参只取现场项及其子项；每种代入逐叶子用公共纯项解释器复核，并保留所有成立的解。</summary>
public sealed class StructConstructorQuery(ManagedTypes types, StructConstructorTemplates templates, StateQueries state,
    IReadOnlyList<StructOrigin> origins, StructValueQuery? structs = null) : Query<StructConstructorRequest, StructConstructorAnswer>
{
    private readonly SourceRangeQuery ranges = new(state);
    private readonly FlowQueries flow = new();
    public override Outcome<StructConstructorAnswer> Compute(QueryContext c, StructConstructorRequest key)
    {
        Outcome<StructConstructorAnswer> No(Reason? why) => Outcome<StructConstructorAnswer>.Success(new(null, [], why));
        if (StructConstructorTemplates.ContainsParameter(key.Type)) return No(new("inline.StructConstructor.Generic", "含类型参数的结构体不作候选。"));
        var dependencies = SnapshotRewrite.Dependencies(key.Leaves.Select(l => l.Value));
        var pool = dependencies.Where(t => t.Width <= 64 && !t.ContainsUndefined).ToArray();
        bool hasMemory = structs is not null && dependencies.Any(t => t.Identity is MemoryAtom or MemoryMerge);
        var matches = new List<StructConstructorAnswer>(); Reason? failure = null; int validTemplates = 0;
        foreach (var method in key.Type.Definition.Methods.Where(m => m is { Name: ".ctor", IsStatic: false }))
        {
            var selected = new MethodRef(method, key.Type.Arguments, []);
            // 一个函数的方法体里没有它自己的内联副本（设计 12.4）：正在恢复的构造函数不作自己的候选，也不为此去取自己的模板。
            if (method == key.Caller.Method && key.Type.Equals(key.Caller.DeclaringType)) continue;
            if (!ManagedAccess.Method(types, key.Caller.Method.Owner, selected, key.Type)) continue;
            if (method.Parameters.Any(p => selected.Concrete(p.Type) is ByRefRef byref && templates.StructParameter(byref) is { } element
                && !origins.Any(o => o.Type.Equals(element)) && !hasMemory))
            { failure ??= new("inline.StructConstructor.Origin", "按引用形参没有同类型的整体来源。"); continue; }
            if (method.Parameters.Any(p => templates.StructParameter(selected.Concrete(p.Type)) is { } structure
                ? !origins.Any(o => o.Type.Equals(structure)) && !(selected.Concrete(p.Type) is ByRefRef && hasMemory)
                : !pool.Any(t => t.Width == types.StorageBits(selected.Concrete(p.Type))))) continue;
            var result = templates.Get(selected);
            if (result.Template is not { } template) { failure ??= result.Failure; continue; }
            if (!template.Type.Equals(key.Type)) { failure ??= new("inline.StructConstructor.Generic", "模板来源只提供开放定义，缺少封闭构造体。"); continue; }
            var used = template.Leaves.SelectMany(l => ManagedValues.Walk(l.Value)).OfType<ArgumentValue>().Select(a => a.Index).ToHashSet();
            if (Enumerable.Range(0, method.Parameters.Count).Any(i => !used.Contains(i))) continue;
            validTemplates++;
            var bindings = new StructConstructorArgument?[method.Parameters.Count];
            var copies = new StructConstructorArgument?[method.Parameters.Count];
            for (int i = 0; hasMemory && i < copies.Length; i++)
            {
                if (selected.Concrete(method.Parameters[i].Type) is not ByRefRef byref || templates.StructParameter(byref) is not { } structure
                    || CopySource(template, i, structure, key.Leaves) is not { } copy) continue;
                var plan = c.Get(structs!, new(structure, copy, key.Point));
                if (plan.IsSuccess && plan.Value.Location is not null) copies[i] = new(copy, structure, key.Point);
            }
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
                    if (Equal(true)) matches.Add(new(selected, bindings.Select(b => b!).ToArray(), null) { Witness = result.Witness });
                    return;
                }
                var parameter = selected.Concrete(method.Parameters[i].Type);
                var type = (TypeRef?)templates.StructParameter(parameter) ?? parameter;
                IEnumerable<StructConstructorArgument> choices = types.Kind(type) == TypeKind.Struct
                    ? origins.Where(o => o.Type.Equals(type) && (o.Point == key.Point || c.Get(flow.PointDominates, new(o.Point, key.Point)) is { IsSuccess: true, Value: true }))
                        .Select(o => new StructConstructorArgument(o.Source, type, o.Parameter is not null ? key.Point : o.Point) { Origin = o })
                    : pool.Where(t => t.Width == types.StorageBits(type)).Select(t => new StructConstructorArgument(new TermSource(t), type, key.Point));
                if (copies[i] is { } copy) choices = choices.Append(copy);
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
    // 模板直接复制的各字段给出实参位片；是否来自同一托管位置、何时取快照，由整体查询证明。
    private PiecesSource? CopySource(StructConstructorTemplate template, int parameter, DefinitionRef type, ImmutableArray<StructLeaf> actual)
    {
        var pieces = new Dictionary<int, BoundPiece>();
        foreach (var (output, value) in template.Leaves)
        {
            if (value is not FieldValue) continue;
            var path = StructConstructorTemplates.Path(value, out var root);
            if (root is not ArgumentValue argument || argument.Index != parameter || types.Project(type, path) is not { } input
                || input.Bit % 8 != 0 || input.Width % 8 != 0 || input.Width != output.Width) continue;
            var leaf = actual.SingleOrDefault(l => l.Projection.Bit == output.Bit && l.Projection.Width == output.Width);
            if (leaf is null) return null;
            var piece = new BoundPiece(input.Bit / 8, input.Width / 8, new TermSource(leaf.Value));
            if (pieces.TryGetValue(input.Bit, out var prior) && prior != piece) return null;
            pieces[input.Bit] = piece;
        }
        return pieces.Count != 0 && types.Projections(type).All(p => pieces.ContainsKey(p.Bit))
            ? new PiecesSource([.. pieces.Values.OrderBy(p => p.ValueOffset)]) : null;
    }
}
