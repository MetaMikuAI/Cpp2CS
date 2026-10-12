using System.Collections.Immutable;

namespace Cpp2CS.Model;

public sealed record BuildId(string BinarySha256, string MetadataSha256, string Target);
public sealed record DefinitionId(BuildId Build, int Image, int Token);
public sealed record NativeAddress(BuildId Build, ulong Rva);
public enum GenericOwner { Type, Method }
public sealed record GenericParameterId(DefinitionId Owner, GenericOwner Kind, int Position);

public abstract record TypeRef;
public sealed record PrimitiveType(string Name, int Bytes, bool Floating = false) : TypeRef;
public sealed record NamedType(DefinitionId Definition, Sequence<TypeRef> Arguments) : TypeRef;
public sealed record ParameterType(GenericParameterId Parameter) : TypeRef;
public sealed record PointerType(TypeRef Element) : TypeRef;
public sealed record ByRefType(TypeRef Element) : TypeRef;
public sealed record ArrayType(TypeRef Element, int Rank) : TypeRef;

public sealed class GenericContext
{
    private readonly ImmutableDictionary<GenericParameterId, TypeRef> bindings;
    public GenericContext(IEnumerable<KeyValuePair<GenericParameterId, TypeRef>> bindings)
        => this.bindings = bindings.ToImmutableDictionary();
    public TypeRef Substitute(TypeRef type) => Substitute(type, ImmutableHashSet<GenericParameterId>.Empty);
    private TypeRef Substitute(TypeRef type, ImmutableHashSet<GenericParameterId> visiting) => type switch
    {
        ParameterType p when bindings.TryGetValue(p.Parameter, out var bound) =>
            visiting.Contains(p.Parameter) ? throw new InvalidOperationException("泛型替换形成环") :
            Substitute(bound, visiting.Add(p.Parameter)),
        NamedType n => n with { Arguments = new(n.Arguments.Select(x => Substitute(x, visiting))) },
        PointerType p => new PointerType(Substitute(p.Element, visiting)),
        ByRefType r => new ByRefType(Substitute(r.Element, visiting)),
        ArrayType a => a with { Element = Substitute(a.Element, visiting) },
        _ => type
    };
}

public sealed record MethodInstance(DefinitionId Definition, Sequence<TypeRef> TypeArguments,
    Sequence<TypeRef> MethodArguments);
public enum EvidenceKind { Metadata, Binary, Abi, Derived, Unresolved }
public sealed record Evidence(EvidenceKind Kind, string Detail, NativeAddress? Instruction = null);
public sealed record MethodBinding(NativeAddress Address, MethodInstance Method, Evidence Evidence);
public enum MetadataUse { ClassInfo, TypeDescriptor, MethodDefinition, MethodInstance, Field, String }
public abstract record MetadataTarget;
public sealed record TypeTarget(TypeRef Type) : MetadataTarget;
public sealed record MethodTarget(MethodInstance Method) : MetadataTarget;
public sealed record FieldTarget(DefinitionId Field, NamedType DeclaringType) : MetadataTarget;
public sealed record StringTarget(BuildId Build, int Index) : MetadataTarget;
public sealed record MetadataSlot(NativeAddress Address, MetadataUse Use, MetadataTarget Target, Evidence Evidence);
public enum LayoutKind { UnboxedValue, BoxedObject, ReferenceObject, StaticStorage }
public sealed record FieldLayout(DefinitionId Field, TypeRef Type, int Offset, int Size);
public sealed record TypeLayout(TypeRef Type, LayoutKind Kind, int Size, int Alignment,
    int PayloadOffset, Sequence<FieldLayout> Fields, Evidence Evidence);
public abstract record LayoutResult;
public sealed record KnownLayout(TypeLayout Layout) : LayoutResult;
public sealed record UnknownLayout(string Reason) : LayoutResult;

public sealed class ProgramFacts
{
    private readonly ImmutableDictionary<NativeAddress, Sequence<MethodBinding>> methods;
    private readonly ImmutableDictionary<(TypeRef, LayoutKind), TypeLayout> layouts;
    public ProgramFacts(IEnumerable<MethodBinding> methods, IEnumerable<TypeLayout> layouts)
    {
        this.methods = methods.GroupBy(x => x.Address).ToImmutableDictionary(g => g.Key, g => new Sequence<MethodBinding>(g));
        this.layouts = layouts.ToImmutableDictionary(x => (x.Type, x.Kind));
        foreach (var layout in this.layouts.Values)
        {
            if (layout.Size < 0 || layout.Alignment <= 0 || (layout.Alignment & (layout.Alignment - 1)) != 0 ||
                layout.PayloadOffset < 0 || layout.PayloadOffset > layout.Size ||
                layout.Fields.Any(f => f.Offset < 0 || f.Size <= 0 || (long)f.Offset + f.Size > layout.Size))
                throw new ArgumentException("无效类型布局");
        }
    }
    public Sequence<MethodBinding> MethodsAt(NativeAddress address) => methods.GetValueOrDefault(address) ?? new([]);
    public LayoutResult LayoutOf(TypeRef type, LayoutKind kind) => layouts.TryGetValue((type, kind), out var layout)
        ? new KnownLayout(layout) : new UnknownLayout("缺少该类型实例及布局类别的证据");
}
