using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Checks;

public sealed record UncheckedUnboxEvidence(TypeRef Type, Term Class, Term Object, CallIdentity? TypeCheck = null);

/// <summary>无检查地址操作不建立类型或非空事实；凭据来自装箱结果、已使用的类型判断及共享路径事实。</summary>
public sealed class UncheckedUnboxQuery(StateQueries state, CallNamingQuery calls, ValueNamingQuery names)
    : Query<CallIdentity, UncheckedUnboxEvidence>
{
    private readonly PathFactQuery paths = new(state);
    private readonly FlowQueries flow = new();
    private readonly ReadLocationQuery reads = new(state);
    private static bool ValueType(TypeRef type) => type is DefinitionRef { Definition.IsValueType: true } d
        && d.Definition.FullName != "System.Nullable`1";
    private TypeRef? Class(QueryContext c, ClassifiedCall call, out Term? source)
    {
        source = (call.Inputs?.GetValueOrDefault("class")?.Source as TermSource)?.Term;
        return source is not null && c.Get(names, source) is { IsSuccess: true, Value.Name: EntityName { Entity: ClassEntity entity } }
            && ValueType(entity.Type) ? entity.Type : null;
    }
    private bool Same(QueryContext c, Term a, Term b) => names.SameValue(c, a, b) is { IsSuccess: true, Value: true };
    internal bool NonNull(QueryContext c, Term value, Point point)
    {
        var condition = c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.NotEqual), 1, value, c.Snapshot.Terms.Constant(0, value.Width));
        if (c.Get(paths, new(point, condition)) is { IsSuccess: true, Value: PathTruth.True }) return true;
        foreach (var block in c.Snapshot.Blocks)
        for (int i = 0; i < block.Statements.Length; i++)
        {
            if (block.Statements[i] is not Call call || c.Get(calls, call.Identity) is not { IsSuccess: true } named) continue;
            if (named.Value.Operation?.Il.Name == "NullCheck" && named.Value.Inputs?.GetValueOrDefault("value")?.Source is TermSource input
                && Same(c, input.Term, value) && (new Point(block.Identity, i + 1) == point
                    || c.Get(flow.PointDominates, new(new(block.Identity, i + 1), point)) is { IsSuccess: true, Value: true })) return true;
        }
        return false;
    }
    public override Outcome<UncheckedUnboxEvidence> Compute(QueryContext c, CallIdentity key)
    {
        Outcome<UncheckedUnboxEvidence> No(string code, string text) => Outcome<UncheckedUnboxEvidence>.Failure(new("check.unbox." + code, text));
        var indexed = c.Get(state.Index, 0); if (!indexed.IsSuccess) return indexed.Propagate<UncheckedUnboxEvidence>();
        var block = c.Snapshot.Blocks.Single(b => b.Statements.OfType<Call>().Any(x => x.Identity == key));
        int at = 0; while (block.Statements[at] is not Call found || found.Identity != key) at++;
        var point = new Point(block.Identity, at);
        var classified = c.Get(calls, key); if (!classified.IsSuccess) return classified.Propagate<UncheckedUnboxEvidence>();
        if (classified.Value.Inputs?.GetValueOrDefault("object")?.Source is not TermSource inputObject)
            return No("binding", "无检查拆箱没有完整绑定的对象输入。");
        var resolved = c.Get(state.Resolve, inputObject.Term); if (!resolved.IsSuccess) return resolved.Propagate<UncheckedUnboxEvidence>();
        var obj = resolved.Value;
        if (obj.Identity is ResultAtom { Definition: CallIdentity box } && c.Get(calls, box) is
            { IsSuccess: true, Value.Operation.Il.Name: "Box" } boxed
            && boxed.Value.Result?.Source is TermSource boxResult && Same(c, obj, boxResult.Term)
            && Class(c, boxed.Value, out var boxClass) is { } boxedType)
            return Outcome<UncheckedUnboxEvidence>.Success(new(boxedType, boxClass!, obj));
        bool sawType = false, needsNonNull = false;
        foreach (var source in c.Snapshot.Blocks)
        for (int i = 0; i < source.Statements.Length; i++)
        {
            if (source.Statements[i] is not Call check || c.Get(calls, check.Identity) is not { IsSuccess: true } named
                || named.Value.Operation?.Il.Name is not ("IsInst" or "CastClass")
                || named.Value.Inputs?.GetValueOrDefault("object")?.Source is not TermSource tested
                || named.Value.Result?.Source is not TermSource result || Class(c, named.Value, out var klass) is not { } type
                || !Same(c, obj, tested.Term) && !Same(c, obj, result.Term)) continue;
            sawType = true;
            var notNull = c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.NotEqual), 1, result.Term, c.Snapshot.Terms.Constant(0, result.Term.Width));
            bool used = c.Get(paths, new(point, notNull)) is { IsSuccess: true, Value: PathTruth.True };
            if (named.Value.Operation.Il.Name == "CastClass")
            {
                bool returnedNormally = new Point(source.Identity, i + 1) == point
                    || c.Get(flow.PointDominates, new(new(source.Identity, i + 1), point)) is { IsSuccess: true, Value: true };
                bool nonnull = NonNull(c, obj, point);
                used |= returnedNormally && nonnull;
                needsNonNull |= returnedNormally && !nonnull;
            }
            if (used) return Outcome<UncheckedUnboxEvidence>.Success(new(type, klass!, obj, check.Identity));
        }
        foreach (var source in c.Snapshot.Blocks.Where(b => b.End is Branch))
        foreach (var condition in SnapshotRewrite.Dependencies([((Branch)source.End).Condition])
            .Where(t => t.Operator is CoreOperator { Operation: CoreOperation.Equal }))
        foreach (var (actual, expected) in new[] { (condition.Operands[0], condition.Operands[1]), (condition.Operands[1], condition.Operands[0]) })
        {
            if (c.Get(names, expected) is not { IsSuccess: true, Value.Name: EntityName { Entity: ClassEntity entity } } || !ValueType(entity.Type)
                || c.Get(names, actual) is not { IsSuccess: true, Value.Name: FieldName { Field: "Il2CppObject.klass" } }
                || c.Get(reads, actual) is not { IsSuccess: true } objectClass || !Same(c, objectClass.Value.Root, obj)
                || c.Get(paths, new(point, condition)) is not { IsSuccess: true, Value: PathTruth.True }) continue;
            sawType = true;
            if (NonNull(c, obj, point)) return Outcome<UncheckedUnboxEvidence>.Success(new(entity.Type, expected, obj));
            needsNonNull = true;
        }
        return needsNonNull ? No("nonnull", "值类型判断已成立，但尚无该对象非空的凭据。")
            : sawType ? No("success", "存在同一对象的类型判断，但该路径尚未证明判断结果非空或转换正常返回。")
            : No("type", "尚无同一对象的精确值类型盒凭据；元素类相等不单独证明精确类相等。");
    }
}
