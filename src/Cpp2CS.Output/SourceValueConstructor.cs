using System.Reflection;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

/// <summary>仅按参数和常量初始化全部字段的值类型构造。</summary>
internal sealed record SourceValueConstructor(MethodRef Method, IReadOnlyList<(FieldRef Field, ManagedValue Value)> Fields)
{
    internal static SourceValueConstructor? Create(MethodRef method, IReadOnlyList<ManagedStore> stores)
    {
        if (method.Method is not { Name: ".ctor", IsStatic: false, Owner.IsValueType: true }
            || method.DeclaringType is not DefinitionRef type
            || (type.Definition.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout
            || method.Method.Parameters.Any(p => p.Type is ByRefRef or PointerRef)) return null;
        var expected = type.Definition.Fields.Where(f => !f.IsStatic).ToHashSet();
        if (expected.Count == 0 || stores.Count != expected.Count) return null;
        var fields = new List<(FieldRef, ManagedValue)>();
        foreach (var store in stores)
        {
            if (store.Target is not FieldValue { Receiver: ArgumentValue { Index: -1 } } field
                || !field.Field.DeclaringType.Equals(type) || !expected.Remove(field.Field.Field)
                || !field.Type.Equals(store.Value.Type)) return null;
            if (store.Value is ArgumentValue argument)
            {
                if (argument.Index < 0 || argument.Index >= method.Method.Parameters.Count
                    || !argument.Type.Equals(method.Method.Parameters[argument.Index].Type.Substitute(method.TypeArguments, []))) return null;
            }
            else if (store.Value is not ConstantValue) return null;
            fields.Add((field.Field, store.Value));
        }
        return new(method, fields);
    }

    internal NewObjectValue? Build(ComposedValue value)
    {
        if (!value.Type.Equals(Method.DeclaringType) || value.Leaves.Count != Fields.Count
            || value.Leaves.Any(l => l.Path.Count != 1 || l.Value is not (LocalValue or ArgumentValue or ConstantValue))
            || value.Leaves.Select(l => l.Path[0]).Distinct().Count() != Fields.Count) return null;
        var arguments = new ManagedValue?[Method.Method.Parameters.Count];
        foreach (var (field, expected) in Fields)
        {
            var actual = value.Leaves.FirstOrDefault(l => l.Path[0].Equals(field)).Value;
            if (actual is null || !actual.Type.Equals(expected.Type)) return null;
            if (expected is ArgumentValue parameter)
            {
                if (arguments[parameter.Index] is { } bound && !bound.Equals(actual)) return null;
                arguments[parameter.Index] = actual;
            }
            else if (!expected.Equals(actual)) return null;
        }
        return arguments.Any(a => a is null) ? null : new NewObjectValue(Method, arguments!) { Transparent = true };
    }
}
