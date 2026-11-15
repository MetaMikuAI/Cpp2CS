using System.Collections.Concurrent;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Inlining;

public sealed partial class AccessorQuery
{
    private delegate IEnumerable<MethodRef> StaticCandidateLookup(FieldRef field, out Reason? failure);
    private sealed record StaticTemplate(MethodDef Method, AccessorTemplate Template);
    private readonly ConcurrentDictionary<FieldDef, Lazy<StaticTemplate[]>> staticFields = [];

    private readonly Lazy<MethodDef[]> staticGetters = new(() => types.Model.Methods.Where(m => m.IsStatic && !m.IsVirtual
        && m.Name is not (".ctor" or ".cctor") && m.Parameters.Count == 0 && m.DeclaresCilBody).ToArray());

    // 签名只筛选模板来源；字段身份与类型实参仍由完整恢复体证明。
    // 调用别的类的静态方法会触发那个类的静态构造；现场只有字段所属类的初始化，所以字段所属类之外的候选不能带静态构造函数。
    private StaticTemplate[] StaticTemplates(FieldDef field) => staticFields.GetOrAdd(field, f => new(() =>
        staticGetters.Value.Where(m => Compatible(m.ReturnType, f.Type)
            && (m.Owner == f.Owner || !m.Owner.Methods.Any(x => x.Name == ".cctor")))
        .Select(m => (Method: m, Result: templates.Get(m)))
        .Where(p => p.Result is { Status: AccessorTemplateStatus.Complete, Template: { SingleField: true,
            Kind: AccessorKind.Getter, Expression: StaticFieldValue } t } && t.Field.Field == f)
        .Select(p => new StaticTemplate(p.Method, p.Result.Template!)).ToArray())).Value;

    private static bool Compatible(TypeRef left, TypeRef right) => (left, right) switch
    {
        (GenericParameterRef, _) or (_, GenericParameterRef) => true,
        (DefinitionRef a, DefinitionRef b) => a.Definition == b.Definition && a.Arguments.Count == b.Arguments.Count
            && a.Arguments.Zip(b.Arguments).All(p => Compatible(p.First, p.Second)),
        (ArrayRef a, ArrayRef b) => a.Rank == b.Rank && a.IsVector == b.IsVector && Compatible(a.Element, b.Element),
        (PointerRef a, PointerRef b) => Compatible(a.Element, b.Element),
        (ByRefRef a, ByRefRef b) => Compatible(a.Element, b.Element),
        _ => left.Equals(right),
    };

    private IEnumerable<MethodRef> StaticCandidates(FieldRef field, out Reason? failure)
    {
        var matches = new List<MethodRef>(); failure = null;
        if (!ValidArgument(field.DeclaringType))
        { failure = new("inline.Accessor.TypeArguments", "现场字段所属类型不能构成元数据实例"); return matches; }
        foreach (var candidate in StaticTemplates(field.Field))
        {
            var typeArguments = new TypeRef?[candidate.Method.Owner.GenericParameters.Count];
            var methodArguments = new TypeRef?[candidate.Method.GenericParameters.Count];
            if (!Unify(candidate.Template.Field.DeclaringType, field.DeclaringType, typeArguments, methodArguments))
            { failure ??= new("inline.Accessor.TypeArguments", "模板字段所属类型与现场实例不能合一：" + candidate.Method); continue; }
            if (typeArguments.Concat(methodArguments).Any(t => t is null))
            { failure ??= new("inline.Accessor.TypeArguments", "字段所属类型未能唯一确定类与方法的全部泛型实参：" + candidate.Method); continue; }
            if (!typeArguments.Concat(methodArguments).OfType<TypeRef>().All(ValidArgument))
            { failure ??= new("inline.Accessor.TypeArguments", "合一所得泛型实参不能构成元数据实例：" + candidate.Method); continue; }
            var method = new MethodRef(candidate.Method, typeArguments.OfType<TypeRef>().ToArray(), methodArguments.OfType<TypeRef>().ToArray());
            if (!method.Concrete(candidate.Template.Field.DeclaringType).Equals(field.DeclaringType)) continue;
            matches.Add(method);
        }
        return matches;
    }

    private static bool Unify(TypeRef pattern, TypeRef actual, TypeRef?[] types, TypeRef?[] methods)
    {
        if (pattern is GenericParameterRef parameter)
        {
            var bindings = parameter.IsMethod ? methods : types;
            if (parameter.Position < 0 || parameter.Position >= bindings.Length) return false;
            if (bindings[parameter.Position] is { } bound) return bound.Equals(actual);
            bindings[parameter.Position] = actual; return true;
        }
        return (pattern, actual) switch
        {
            (DefinitionRef a, DefinitionRef b) => a.Definition == b.Definition && a.Arguments.Count == b.Arguments.Count
                && a.Arguments.Count == a.Definition.GenericParameters.Count
                && a.Arguments.Zip(b.Arguments).All(p => Unify(p.First, p.Second, types, methods)),
            (ArrayRef a, ArrayRef b) => a.Rank == b.Rank && a.IsVector == b.IsVector && Unify(a.Element, b.Element, types, methods),
            (PointerRef a, PointerRef b) => Unify(a.Element, b.Element, types, methods),
            (ByRefRef a, ByRefRef b) => Unify(a.Element, b.Element, types, methods),
            _ => pattern.Equals(actual),
        };
    }

    private static bool ValidArgument(TypeRef type) => type switch
    {
        GenericParameterRef p => p.Position >= 0,
        DefinitionRef d => !ManagedTypes.IsVoid(d) && ManagedTypes.PrimitiveName(d) != "TypedReference"
            && d.Arguments.Count == d.Definition.GenericParameters.Count && d.Arguments.All(ValidArgument),
        ArrayRef a => a.Rank > 0 && (!a.IsVector || a.Rank == 1) && ValidArgument(a.Element),
        _ => false,
    };

    private static Reason WithAnchor(Reason reason, AccessorAccess access) => reason.Code == "inline.anchor" ? reason
        : reason with { Cause = reason.Cause is { } cause ? WithAnchor(cause, access) : Anchor(access.Kind == AccessorKind.Setter, access.Field) };

    private static Reason Anchor(bool write, FieldRef field, Reason? cause = null) =>
        new("inline.anchor", (write ? "写入 " : "读取 ") + field.Field.Owner.FullName + "." + field.Field.Name, cause);

    /// <summary>候选全部未能完整恢复时，取名字最小的一个候选自己的失败原因，接在锚点之后。</summary>
    private static Reason? CandidateCause(IReadOnlyList<AccessorCandidateFailure> incomplete) =>
        incomplete.Where(f => f.Failure is not null).OrderBy(f => f.Method.Owner.FullName + "." + f.Method.Name, StringComparer.Ordinal).FirstOrDefault() is { } first
            ? new("inline.candidate", "候选 " + first.Method.Owner.FullName + "." + first.Method.Name, first.Failure) : null;
}
