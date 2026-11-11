using Mono.Cecil;
using Cpp2CS.Model;
using Cpp2CS.Tests.Metrics;

namespace Cpp2CS.Tests.Execution;

internal sealed partial class CecilModel
{
    private bool checking = false;
    private readonly HashSet<(TypeDef Type, bool Layout)> checkedTypes = [];

    private static string Signature(MethodDefinition method) => IlMetrics.Identity(method);
    private static string TypeSignature(TypeReference? type, ModuleDefinition module) => type is null ? "" : IlMetrics.TypeKey(type, module);
    private static string FieldSignature(FieldDefinition field) =>
        $"{field.Name}:{TypeSignature(field.FieldType, field.Module)}:{field.Attributes}:{field.Offset}:{field.Constant}:{Convert.ToHexString(field.InitialValue)}";
    private static void Different(TypeDefinition type, string kind, string left, string right) =>
        throw new Unsupported($"两侧类型元数据不对应：{type.FullName}；{kind}；参考={left}；待测={right}", ComparisonReason.TypeMismatch);

    private IEnumerable<TypeDefinition> Counterparts(TypeDefinition type)
    {
        if (!modules.Contains(type.Module)) yield break;
        foreach (var module in modules.Where(m => m != type.Module))
        {
            var other = module.GetType(type.FullName);
            if (other is null) Different(type, "类型缺失", type.FullName, "无");
            yield return other!;
        }
    }
    private void CheckType(TypeDef type, bool layout = false)
    {
        if (!checking || checkedTypes.Contains((type, layout))) return;
        var source = definitions[type];
        foreach (var other in Counterparts(source))
        {
            void Equal(string kind, string l, string r) { if (l != r) Different(source, kind, l, r); }
            Equal("类型属性", source.Attributes.ToString(), other.Attributes.ToString());
            Equal("基类", TypeSignature(source.BaseType, source.Module), TypeSignature(other.BaseType, other.Module));
            Equal("接口", string.Join(";", source.Interfaces.Select(i => TypeSignature(i.InterfaceType, source.Module))),
                string.Join(";", other.Interfaces.Select(i => TypeSignature(i.InterfaceType, other.Module))));
            Equal("泛型约束", Generics(source.GenericParameters), Generics(other.GenericParameters));
            if (layout)
            {
                Equal("布局", $"{source.PackingSize}:{source.ClassSize}", $"{other.PackingSize}:{other.ClassSize}");
                Equal("字段列表/属性/类型/次序", string.Join(";", source.Fields.Select(FieldSignature)), string.Join(";", other.Fields.Select(FieldSignature)));
            }
        }
        checkedTypes.Add((type, layout));
    }
    private static string Generics(IEnumerable<GenericParameter> parameters) => string.Join(";", parameters.Select(p =>
        $"{p.Position}:{p.Attributes}:" + string.Join(",", p.Constraints.Select(c => TypeSignature(c.ConstraintType, p.Module)))));

    private void CheckMethod(MethodDefinition method)
    {
        if (!checking) return;
        CheckType(Definition(method.DeclaringType));
        foreach (var other in Counterparts(method.DeclaringType))
        {
            var signature = Signature(method);
            var matches = other.Methods.Where(m => Signature(m) == signature).ToArray();
            if (matches.Length != 1) Different(method.DeclaringType, "方法签名", signature, $"对应数={matches.Length}");
            var candidate = matches[0];
            if (method.Attributes != candidate.Attributes || method.ImplAttributes != candidate.ImplAttributes
                || Generics(method.GenericParameters) != Generics(candidate.GenericParameters))
                Different(method.DeclaringType, "方法属性/泛型约束", method.ToString(), candidate.ToString());
        }
    }
    private void CheckDispatch(TypeDef type)
    {
        if (!checking) return;
        CheckType(type);
        var source = definitions[type];
        static string Slots(TypeDefinition t) => string.Join(";", t.Methods.Where(m => m.IsVirtual).Select(m =>
            $"{Signature(m)}:{m.Attributes}:" + string.Join(",", m.Overrides.Select(o => o.FullName))));
        foreach (var other in Counterparts(source))
            if (Slots(source) != Slots(other)) Different(source, "虚方法槽/显式实现", Slots(source), Slots(other));
    }
}
