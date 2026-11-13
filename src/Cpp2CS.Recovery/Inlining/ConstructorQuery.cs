using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Inlining;

public enum ConstructorAnchor { Base, Allocation }
public sealed record ConstructorAccess(MethodRef Caller, ulong Position, TypeRef Type, ConstructorAnchor Anchor);
public sealed record ConstructorWrite(FieldRef Field, ManagedValue Value, object? Identity = null, bool AfterCall = false);
public sealed record ConstructorArgument(ManagedValue Value, object? Identity = null);
/// <summary>初始区域已核对接收者身份的真实直接构造调用。</summary>
public sealed record ConstructorActualCall(MethodRef Method, IReadOnlyList<ConstructorArgument> Arguments);
public sealed record ConstructorCandidate(MethodRef Method, ConstructorTemplateResult Template, string? Difference);
public sealed record ConstructorAnswer(MethodRef? Method, Reason? Failure)
{
    public IReadOnlyList<ManagedValue> Arguments { get; init; } = [];
    public IReadOnlyList<int> Writes { get; init; } = [];
    public bool ConsumesCall { get; init; }
    public IReadOnlyList<ConstructorCandidate> Candidates { get; init; } = [];
}
public sealed record ConstructorAttempt(ConstructorAccess Access, ConstructorAnswer Answer);

/// <summary>消费真实调用的候选优先，再取字段最多者；同一调用的两种对法成立或候选并列均为洞。</summary>
public sealed class ConstructorQuery(ManagedTypes types, ConstructorTemplates templates, Action<ConstructorAttempt>? observe = null)
{
    public ConstructorAnswer Resolve(ConstructorAccess access, IReadOnlyList<ConstructorWrite>? writes = null, ConstructorActualCall? call = null)
    {
        var answer = Find(access, writes ?? [], call);
        observe?.Invoke(new(access, answer));
        return answer;
    }
    public void Reject(ConstructorAccess access, Reason reason) => observe?.Invoke(new(access, new(null, reason)));
    private ConstructorAnswer Find(ConstructorAccess access, IReadOnlyList<ConstructorWrite> writes, ConstructorActualCall? call)
    {
        var diagnostics = new List<ConstructorCandidate>(); var matches = new List<ConstructorAnswer>();
        int nearest = -1; string? difference = null;
        ConstructorAnswer No(string code, string message) => new(null, new(code, message)) { Candidates = diagnostics };
        if (access.Type is not DefinitionRef type || type.Definition.IsValueType)
            return No("inline.Constructor.NotStraight", "Signature：构造类型没有引用类型定义。");
        foreach (var candidate in type.Definition.Methods.Where(m => m is { Name: ".ctor", IsStatic: false } && (access.Anchor != ConstructorAnchor.Base || m != access.Caller.Method)))
        {
            var selected = new MethodRef(candidate, type.Arguments, []);
            if (!ManagedAccess.Method(types, access.Caller.Method.Owner, selected,
                access.Anchor == ConstructorAnchor.Base ? access.Caller.DeclaringType : access.Type)) continue;
            var result = templates.Get(candidate);
            if (result.Template is null)
            {
                diagnostics.Add(new(selected, result, result.Failure?.Message));
                difference ??= $"{selected}：{result.Failure?.Message}"; continue;
            }
            var alternatives = new List<ConstructorAnswer>(); string? candidateFailure = null;
            foreach (var template in templates.Alternatives(selected))
            {
                var args = new ManagedValue?[candidate.Parameters.Count]; var identities = new object?[args.Length];
                var consumed = new List<int>(); string? failed = null;
                bool Bind(ManagedValue expected, ManagedValue actual, object? identity, TypeRef fullType, string where)
                {
                    actual = ConstructorTemplates.Normalize(actual, types);
                    if (expected is ArgumentValue parameter)
                    {
                        var parameterType = selected.Concrete(candidate.Parameters[parameter.Index].Type);
                        // 窄字段无法确定较宽形参；字段与调用实参使用同一完整值绑定。
                        if (!actual.Type.Equals(parameterType) || !fullType.Equals(parameterType))
                        { failed = $"形参 {parameter.Index} 的完整值不能由 {where} 确定"; return false; }
                        identity ??= actual;
                        if (args[parameter.Index] is not null && !Equals(identities[parameter.Index], identity))
                        { failed = $"形参 {parameter.Index} 在 {where} 发生绑定冲突"; return false; }
                        args[parameter.Index] = actual; identities[parameter.Index] = identity; return true;
                    }
                    if (Equals(ConstructorTemplates.Normalize(expected, types), actual)) return true;
                    failed = $"{where} 的常量不同：模板 {expected}，实际 {actual}"; return false;
                }
                if (template.Call is { } invocation)
                {
                    if (call is null || !call.Method.Equals(invocation.Method) || call.Arguments.Count != invocation.Arguments.Count)
                        failed = $"没有对 {invocation.Method} 的同对象真实直接调用";
                    else
                        for (int i = 0; i < invocation.Arguments.Count; i++)
                            if (!Bind(invocation.Arguments[i], call.Arguments[i].Value, call.Arguments[i].Identity,
                                invocation.Method.Concrete(invocation.Method.Method.Parameters[i].Type), $"构造调用实参 {i}")) break;
                }
                if (failed is null)
                    foreach (var entry in template.Fields)
                    {
                        var field = entry.Field;
                        if (access.Anchor == ConstructorAnchor.Base && field.Field.Owner == access.Caller.Method.Owner)
                        { failed = $"字段 {field} 不在祖先类型中"; break; }
                        var found = Enumerable.Range(0, writes.Count).Where(i => writes[i].Field.Equals(field) && writes[i].AfterCall == entry.AfterCall).ToArray();
                        if (found.Length != 1)
                        { failed = found.Length == 0 ? $"缺少字段 {field} 在调用{(entry.AfterCall ? "后" : "前")}的写入" : $"字段 {field} 有 {found.Length} 次写入"; break; }
                        int index = found[0];
                        if (!Bind(entry.Value, writes[index].Value, writes[index].Identity,
                            field.Field.Type.Substitute((field.DeclaringType as DefinitionRef)?.Arguments ?? [], []), $"字段 {field}")) break;
                        consumed.Add(index);
                    }
                if (failed is null && Array.FindIndex(args, a => a is null) is var unbound && unbound >= 0)
                    failed = $"形参 {unbound} 未绑定";
                if (failed is null && template.Call is not null && access.Anchor == ConstructorAnchor.Allocation
                    && Enumerable.Range(0, writes.Count).Any(i => !writes[i].AfterCall && !consumed.Contains(i)))
                    failed = "调用前仍有未消费的字段写入，不能跨调用移动对象创建";
                if (failed is not null)
                {
                    candidateFailure ??= failed;
                    if (consumed.Count >= nearest) { nearest = consumed.Count; difference = $"{selected}：{failed}"; candidateFailure = failed; }
                    continue;
                }
                alternatives.Add(new(selected, null) { Arguments = args.Select(a => a!).ToArray(), Writes = consumed, ConsumesCall = template.Call is not null });
            }
            if (alternatives.Count == 0) candidateFailure ??= "构造调用展开成环或被调方没有直线模板，且不能配对";
            diagnostics.Add(new(selected, result, alternatives.Count == 0 ? candidateFailure : null));
            if (alternatives.Count != 0)
            {
                var match = alternatives.OrderByDescending(a => a.ConsumesCall).ThenByDescending(a => a.Writes.Count).First();
                // 现场留着一次真实的构造调用时，只有消费它的对法解释了全部原生代码；展开的对法会把这次调用留成重复的祖先构造调用。
                // 恰有一种对法消费调用就取它；没有或不止一种才是歧义。
                if (alternatives.Count > 1 && alternatives.Count(a => a.ConsumesCall) != 1) match = match with
                { Failure = new("inline.Constructor.Ambiguous", $"{selected} 的构造调用有 {alternatives.Count} 种对法成立，不能确定。") };
                matches.Add(match);
            }
        }
        if (matches.Any(m => m.ConsumesCall)) matches.RemoveAll(m => !m.ConsumesCall);
        int best = matches.Count == 0 ? -1 : matches.Max(m => m.Writes.Count);
        matches.RemoveAll(m => m.Writes.Count != best);
        if (matches.Count == 1) return matches[0].Failure is { } ambiguous
            ? No(ambiguous.Code, ambiguous.Message) : matches[0] with { Candidates = diagnostics };
        if (matches.Count > 1) return No("inline.Constructor.Ambiguous", $"{matches.Count} 个候选均匹配 {best} 个字段，不能确定构造函数。");
        string code = diagnostics.Count != 0 && diagnostics.All(d => d.Template.Template is null)
            ? "inline.Constructor.NotStraight" : access.Anchor == ConstructorAnchor.Base ? "inline.Constructor.BaseTemplate" : "inline.Constructor.Template";
        return No(code, difference ?? diagnostics.LastOrDefault()?.Difference ?? "没有可访问的实例构造函数候选。");
    }

    /// <summary>直接初始化见证保留；未消费的祖先调用仍阻止补入初始化。</summary>
    public ConstructorAnswer Initialization(MethodRef caller, IReadOnlyList<ManagedBlock> blocks)
    {
        var parent = ConstructorTemplates.Parent(caller.DeclaringType);
        var witness = InitializationWitness(caller, blocks);
        if (witness == 1) return new(null, null);
        if (witness != 0) return new(null, new("lowering.ConstructorInitialization", "引用类型构造函数没有唯一的直接 this 初始化调用见证。"));
        if (parent is null && caller.DeclaringType.Equals(types.Object)) return new(null, null);
        var stores = blocks[0].Statements.TakeWhile(s => s is ManagedStore { Target: FieldValue { Receiver: ArgumentValue { Index: -1 } } } store
            && !ManagedValues.Walk(store.Value).Any(v => v is ArgumentValue { Index: -1 } or FieldValue or StaticFieldValue
                or IndirectValue or ArrayElementValue or NewObjectValue or NewArrayValue or StaticCallValue)).Cast<ManagedStore>().ToArray();
        var writes = stores.Select(s => new ConstructorWrite(((FieldValue)s.Target).Field, s.Value)).ToArray();
        return MatchInitialization(caller, writes, unconsumedAncestor: blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Any(c =>
            c.Invocation.Method.Method is { Name: ".ctor", IsStatic: false, Owner.IsValueType: false }
            && types.IsAssignable(caller.DeclaringType, c.Invocation.Method.DeclaringType)));
    }
    public ConstructorAnswer MatchInitialization(MethodRef caller, IReadOnlyList<ConstructorWrite> writes, ConstructorActualCall? call = null, bool unconsumedAncestor = false)
    {
        var parent = ConstructorTemplates.Parent(caller.DeclaringType);
        if (parent is null && caller.DeclaringType.Equals(types.Object)) return new(null, null);
        var access = new ConstructorAccess(caller, 0, parent ?? caller.DeclaringType, ConstructorAnchor.Base);
        var answer = Find(access, writes, call);
        if (answer.Method is null && answer.Failure?.Code != "inline.Constructor.Ambiguous")
        {
            var same = Find(access with { Type = caller.DeclaringType }, writes, call);
            if (same.Method is not null || same.Failure?.Code == "inline.Constructor.Ambiguous") answer = same;
        }
        if (answer.Failure?.Code != "inline.Constructor.Ambiguous" && (unconsumedAncestor || call is not null && !answer.ConsumesCall))
            answer = new(null, new("lowering.ConstructorInitialization", "仍有未被匹配模板消费的祖先构造调用，不能重复补入基类调用。")) { Candidates = answer.Candidates };
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
