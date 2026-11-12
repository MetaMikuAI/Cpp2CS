using System.Collections.Immutable;
using Cpp2CS.Input;
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
