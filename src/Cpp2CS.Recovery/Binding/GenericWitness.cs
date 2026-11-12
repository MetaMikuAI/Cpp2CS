using Cpp2CS.Model;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Binding;

/// <summary>原生解释使用封闭实例，托管位置使用定义的类型参数；不从 object 反猜类型。</summary>
public sealed class GenericWitness(MethodRef definition, MethodRef instance, ITypeLayouts layouts) : ITypeLayouts
{
    public MethodRef Definition { get; } = definition;
    public MethodRef Instance { get; } = instance;
    public static bool IsGeneric(MethodDef method) => method.Owner.GenericParameters.Count + method.GenericParameters.Count != 0;
    public static bool IsCanonical(MethodRef instance) => ManagedCSignatureBuilder.IsClosed(instance)
        && instance.TypeArguments.Concat(instance.MethodArguments).All(t => t is DefinitionRef
            { Definition: { Assembly: "mscorlib.dll", FullName: "System.Object" }, Arguments.Count: 0 });
    public static bool IsValueInstance(MethodRef instance) => ManagedCSignatureBuilder.IsClosed(instance)
        && !instance.TypeArguments.Concat(instance.MethodArguments).Any(ManagedCSignatureBuilder.FullyShared)
        && instance.TypeArguments.Concat(instance.MethodArguments).Any(t => t is DefinitionRef { Definition.IsValueType: true });

    public bool Knows(TypeRef type) => type switch
    {
        GenericParameterRef p => Definition.TypeArguments.Concat(Definition.MethodArguments).OfType<GenericParameterRef>()
            .Any(own => own == p && (p.Parameter is null || p.Parameter == own.Parameter)),
        DefinitionRef d => d.Arguments.Count == d.Definition.GenericParameters.Count && d.Arguments.All(Knows),
        ArrayRef a => Knows(a.Element), ByRefRef r => Knows(r.Element), PointerRef p => Knows(p.Element), _ => true,
    };
    public TypeRef Close(TypeRef type) => type.Substitute(Instance.TypeArguments, Instance.MethodArguments);
    public MethodRef Close(MethodRef method) => method with
    {
        TypeArguments = method.TypeArguments.Select(Close).ToArray(),
        MethodArguments = method.MethodArguments.Select(Close).ToArray(),
    };
    public bool Knows(MethodRef method) => method.TypeArguments.Count == method.Method.Owner.GenericParameters.Count
        && method.MethodArguments.Count == method.Method.GenericParameters.Count
        && method.TypeArguments.Concat(method.MethodArguments).All(Knows);
    public TypeLayout? Of(DefinitionRef type)
    {
        if (!Knows(type) || layouts.Of((DefinitionRef)Close(type)) is not { } native) return null;
        IReadOnlyList<FieldSlot> Open(IReadOnlyList<FieldSlot> slots) => slots.Select(s => s with
            { Type = s.Field.Type.Substitute(type.Arguments, []) }).ToArray();
        return new() { Type = type, ObjectHeaderSize = native.ObjectHeaderSize, InstanceSize = native.InstanceSize,
            ActualSize = native.ActualSize, MinimumAlignment = native.MinimumAlignment, HasReferences = native.HasReferences,
            Fields = Open(native.Fields), Statics = Open(native.Statics), ThreadStatics = Open(native.ThreadStatics),
            StaticSize = native.StaticSize, FromMetadata = native.FromMetadata };
    }
    public (int Size, int Alignment)? TrySizeAndAlignment(TypeRef type) => Knows(type) ? layouts.TrySizeAndAlignment(Close(type)) : null;
    public (int Size, int Alignment) SizeAndAlignment(TypeRef type) => TrySizeAndAlignment(type)
        ?? throw new InvalidOperationException("见证不能确定布局：" + type);
}
