using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Inlining;

public enum ConstructorAnchor { Base, Allocation }
public sealed record ConstructorAccess(MethodRef Caller, ulong Position, TypeRef Type, ConstructorAnchor Anchor);
public sealed record ConstructorWrite(FieldRef Field, ManagedValue Value, object? Identity = null);
public sealed record ConstructorCandidate(MethodRef Method, ConstructorTemplateResult Template, string? Difference);
public sealed record ConstructorAnswer(MethodRef? Method, Reason? Failure)
{
    public IReadOnlyList<ManagedValue> Arguments { get; init; } = [];
    public IReadOnlyList<int> Writes { get; init; } = [];
    public IReadOnlyList<ConstructorCandidate> Candidates { get; init; } = [];
}
public sealed record ConstructorAttempt(ConstructorAccess Access, ConstructorAnswer Answer);

/// <summary>按字段逐项绑定形参；取字段最多的可访问候选，并列保留歧义洞。</summary>
public sealed class ConstructorQuery(ManagedTypes types, ConstructorTemplates templates, Action<ConstructorAttempt>? observe = null)
{
    public ConstructorAnswer Resolve(ConstructorAccess access, IReadOnlyList<ConstructorWrite>? writes = null)
    {
        var answer = Find(access, writes ?? []);
        observe?.Invoke(new(access, answer));
        return answer;
    }
    public void Reject(ConstructorAccess access, Reason reason) => observe?.Invoke(new(access, new(null, reason)));
    private ConstructorAnswer Find(ConstructorAccess access, IReadOnlyList<ConstructorWrite> writes)
    {
        var diagnostics = new List<ConstructorCandidate>();
        var matches = new List<ConstructorAnswer>(); int best = -1, nearest = -1; string? difference = null;
        ConstructorAnswer No(string code, string message) => new(null, new(code, message)) { Candidates = diagnostics };
        if (access.Type is not DefinitionRef type || type.Definition.IsValueType)
            return No("inline.Constructor.NotStraight", "Signature：构造类型没有引用类型定义。");
        foreach (var candidate in type.Definition.Methods.Where(m => m is { Name: ".ctor", IsStatic: false } && (access.Anchor != ConstructorAnchor.Base || m != access.Caller.Method)))
        {
            var selected = new MethodRef(candidate, type.Arguments, []);
            if (!ManagedAccess.Method(types, access.Caller.Method.Owner, selected,
                access.Anchor == ConstructorAnchor.Base ? access.Caller.DeclaringType : access.Type)) continue;
            var result = templates.Get(candidate);
            if (result.Template is not { } template)
            {
                diagnostics.Add(new(selected, result, result.Failure?.Message));
                difference ??= $"{selected}：{result.Failure?.Message}"; continue;
            }
            var args = new ManagedValue?[candidate.Parameters.Count]; var identities = new object?[args.Length];
            var consumed = new List<int>(); string? failed = null;
            foreach (var entry in template.Fields)
            {
                var field = entry.Field with { DeclaringType = selected.Concrete(entry.Field.DeclaringType) };
                if (access.Anchor == ConstructorAnchor.Base && field.Field.Owner == access.Caller.Method.Owner)
                { failed = $"字段 {field} 不在祖先类型中"; break; }
                var found = Enumerable.Range(0, writes.Count).Where(i => writes[i].Field.Equals(field)).ToArray();
                if (found.Length != 1)
                { failed = found.Length == 0 ? $"缺少字段 {field} 的写入" : $"字段 {field} 有 {found.Length} 次写入"; break; }
                int index = found[0]; var actual = ConstructorTemplates.Normalize(writes[index].Value, types);
                var expected = ConstructorTemplates.Substitute(entry.Value, selected);
                if (expected is ArgumentValue parameter)
                {
                    var parameterType = selected.Concrete(candidate.Parameters[parameter.Index].Type);
                    // 窄字段无法唯一确定较宽形参；不补高位、不猜引用的向下转换。
                    if (!actual.Type.Equals(parameterType) || !field.Field.Type.Substitute((field.DeclaringType as DefinitionRef)?.Arguments ?? [], []).Equals(parameterType))
                    { failed = $"形参 {parameter.Index} 的完整值不能由字段 {field} 确定"; break; }
                    var identity = writes[index].Identity ?? actual;
                    if (args[parameter.Index] is not null && !Equals(identities[parameter.Index], identity))
                    { failed = $"形参 {parameter.Index} 在字段 {field} 发生绑定冲突"; break; }
                    args[parameter.Index] = actual; identities[parameter.Index] = identity;
                }
                else if (!Equals(ConstructorTemplates.Normalize(expected, types), actual))
                { failed = $"字段 {field} 的常量不同：模板 {expected}，写入 {actual}"; break; }
                consumed.Add(index);
            }
            if (failed is null && Array.FindIndex(args, a => a is null) is var unbound && unbound >= 0)
                failed = $"形参 {unbound} 未绑定";
            diagnostics.Add(new(selected, result, failed));
            if (failed is not null)
            {
                if (consumed.Count > nearest) { nearest = consumed.Count; difference = $"{selected}：{failed}"; }
                continue;
            }
            var match = new ConstructorAnswer(selected, null) { Arguments = args.Select(a => a!).ToArray(), Writes = consumed };
            if (template.Fields.Count > best) { best = template.Fields.Count; matches.Clear(); }
            if (template.Fields.Count == best) matches.Add(match);
        }
        if (matches.Count == 1) return matches[0] with { Candidates = diagnostics };
        if (matches.Count > 1) return No("inline.Constructor.Ambiguous", $"{matches.Count} 个候选均匹配 {best} 个字段，不能确定构造函数。");
        string code = diagnostics.Count != 0 && diagnostics.All(d => d.Template.Template is null)
            ? "inline.Constructor.NotStraight" : access.Anchor == ConstructorAnchor.Base ? "inline.Constructor.BaseTemplate" : "inline.Constructor.Template";
        return No(code, difference ?? "没有可访问的实例构造函数候选。");
    }

    /// <summary>基类候选不匹配时才考虑 this 调用；已有祖先调用的保护覆盖全部候选。</summary>
    public ConstructorAnswer Initialization(MethodRef caller, IReadOnlyList<ManagedBlock> blocks)
    {
        var parent = ConstructorTemplates.Parent(caller.DeclaringType);
        var witness = InitializationWitness(caller, blocks);
        if (witness == 1) return new(null, null);
        if (witness != 0) return new(null, new("lowering.ConstructorInitialization", "引用类型构造函数没有唯一的直接 this 初始化调用见证。"));
        if (parent is null && caller.DeclaringType.Equals(types.Object)) return new(null, null);
        if (blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Any(c =>
            c.Invocation.Method.Method is { Name: ".ctor", IsStatic: false, Owner.IsValueType: false }
            && types.IsAssignable(caller.DeclaringType, c.Invocation.Method.DeclaringType)))
            return new(null, new("lowering.ConstructorInitialization", "仍有可能初始化 this 的祖先构造调用，不能重复补入基类调用。"));
        var stores = blocks[0].Statements.TakeWhile(s => s is ManagedStore { Target: FieldValue { Receiver: ArgumentValue { Index: -1 } } } store
            && !ManagedValues.Walk(store.Value).Any(v => v is ArgumentValue { Index: -1 } or FieldValue or StaticFieldValue
                or IndirectValue or ArrayElementValue or NewObjectValue or NewArrayValue or StaticCallValue)).Cast<ManagedStore>().ToArray();
        var writes = stores.Select(s => new ConstructorWrite(((FieldValue)s.Target).Field, s.Value)).ToArray();
        return MatchInitialization(caller, writes);
    }
    public ConstructorAnswer MatchInitialization(MethodRef caller, IReadOnlyList<ConstructorWrite> writes)
    {
        var parent = ConstructorTemplates.Parent(caller.DeclaringType);
        if (parent is null && caller.DeclaringType.Equals(types.Object)) return new(null, null);
        var access = new ConstructorAccess(caller, 0, parent ?? caller.DeclaringType, ConstructorAnchor.Base);
        var answer = Find(access, writes);
        if (answer.Method is null && answer.Failure?.Code != "inline.Constructor.Ambiguous")
        {
            var same = Find(access with { Type = caller.DeclaringType }, writes);
            if (same.Method is not null || same.Failure?.Code == "inline.Constructor.Ambiguous") answer = same;
        }
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
