using System.Collections.Immutable;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Pipeline;

public sealed class RuntimeMetadataSlotValidator(GlobalFacts facts) : Cpp2CS.Recovery.RuntimeFunctions.IRuntimeMetadataSlotValidator
{
    public bool IsValid(ulong imageOffset) => MetadataTokens.ReadSlot(facts.Image, facts.Model, imageOffset) is not null;
}

public sealed class MetadataSlotDecoder(GlobalFacts facts) : IMetadataSlotDecoder
{
    public Outcome<MetadataEntity> Decode(ulong imageOffset)
    {
        var usage = MetadataTokens.ReadSlot(facts.Image, facts.Model, imageOffset);
        MetadataEntity? entity = usage?.Kind switch
        {
            UsageKind.TypeInfo => new ClassEntity((Cpp2CS.Model.TypeRef)usage.Value),
            UsageKind.Il2CppType => new TypeEntity((Cpp2CS.Model.TypeRef)usage.Value),
            UsageKind.MethodDef or UsageKind.MethodRef => new MethodEntity((Cpp2CS.Model.MethodRef)usage.Value),
            UsageKind.FieldInfo => new FieldEntity((Cpp2CS.Model.FieldRef)usage.Value),
            UsageKind.StringLiteral => new StringEntity((string)usage.Value), _ => null
        };
        return entity is null ? Outcome<MetadataEntity>.Failure(new("naming.slot-decode", "已证明的槽位不含有效元数据编码或实体索引。")) : Outcome<MetadataEntity>.Success(entity);
    }
}
/// <summary>metadata/GenericMetadata.cpp::InflateRGCTXDataLocked 按定义与当前泛型实参构造实体。</summary>
public sealed class MetadataRgctxDecoder(GlobalFacts facts) : IRgctxDecoder
{
    public Outcome<MetadataEntity> Decode(MethodRef definition, bool methodContext, int index)
    {
        var token = methodContext ? definition.Method.Token : definition.Method.Owner.Token;
        if (!facts.CodeMap.Rgctx.TryGetValue((definition.Method.Owner.Assembly, token), out var entries)
            || index < 0 || index >= entries.Length)
            return Outcome<MetadataEntity>.Failure(new("naming.rgctx-index", $"定义的 RGCTX[{index}] 不存在。"));
        TypeRef Type(TypeRef type) => type.Substitute(definition.TypeArguments, methodContext ? definition.MethodArguments : []);
        var entity = entries[index] switch
        {
            { Kind: RgctxKind.Class, Value: TypeRef type } => (MetadataEntity)new ClassEntity(Type(type)),
            { Kind: RgctxKind.Type, Value: TypeRef type } => new TypeEntity(Type(type)),
            { Kind: RgctxKind.Method, Value: MethodRef method } => new MethodEntity(method with
            { TypeArguments = method.TypeArguments.Select(Type).ToArray(), MethodArguments = method.MethodArguments.Select(Type).ToArray() }),
            _ => null,
        };
        return entity is null ? Outcome<MetadataEntity>.Failure(new("naming.rgctx-kind", "泛型上下文项种类尚未支持：" + entries[index].Kind))
            : Outcome<MetadataEntity>.Success(entity);
    }
}

/// <summary>运行时函数的定位结果作为调用分类的输入；没有定位到的目标回答 null。</summary>
public sealed class RuntimeFunctionMap(Cpp2CS.Recovery.RuntimeFunctions.RuntimeFunctionLocations locations) : IRuntimeFunctionMap
{
    public Cpp2CS.Runtime.RuntimeFunction? Find(Cpp2CS.Native.CallTarget target) => locations.Find(target)?.Function;
}
public sealed class NamingCodeMap(Registrations registrations) : IBindingCodeMap
{
    public ImmutableArray<BindingEntry> At(ulong entryOffset) => registrations.ByAddress.TryGetValue(entryOffset, out var entries)
        ? entries.Select(e => new BindingEntry(e.Method, e.Kind switch
        {
            EntryKind.Method => BindingEntryKind.Ordinary,
            EntryKind.GenericMethod => BindingEntryKind.SharedGeneric,
            EntryKind.AdjustorThunk or EntryKind.GenericAdjustorThunk => BindingEntryKind.AdjustorThunk,
            EntryKind.Invoker => BindingEntryKind.Invoker, _ => BindingEntryKind.Wrapper
        }, e.Kind.ToString())).ToImmutableArray() : [];
}
