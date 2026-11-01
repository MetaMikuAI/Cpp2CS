
namespace Cpp2CS.Model;

public enum NativeBindingKind { Reference, Scalar, Aggregate, Shared }

/// <summary>一个入口的布局见证；不改变泛型参数的托管身份或元数据约束。</summary>
public sealed record NativeBinding(NativeBindingKind Kind, TypeRef? Layout = null, ulong Entry = 0);

public static class NativeBindings
{
    public static string Key(TypeRef type) => type switch
    {
        GenericParameterRef g => $"{(g.IsMethod ? "M" : "T")}{g.Position}:{g.Name}:{g.Binding?.Kind}:{g.Binding?.Entry}:{(g.Binding?.Layout is { } layout ? Key(layout) : "")}",
        DefinitionRef d => $"{d.Definition.Assembly}:{d.Definition.Index}[{string.Join(';', d.Arguments.Select(Key))}]",
        ArrayRef a => $"array:{a.Rank}:{a.IsVector}:{Key(a.Element)}",
        ByRefRef r => $"ref:{Key(r.Element)}",
        PointerRef p => $"ptr:{Key(p.Element)}",
        _ => type.ToString()!,
    };

    public static string Key(MethodRef method) => string.Join(';', method.TypeArguments.Select(Key)) + "|" + string.Join(';', method.MethodArguments.Select(Key));
}
