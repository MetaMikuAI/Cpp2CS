#nullable enable
using Cpp2CS.Model;
using Cpp2CS.Native.Images;
namespace Cpp2CS.Input;
public enum UsageKind { TypeInfo = 1, Il2CppType = 2, MethodDef = 3, FieldInfo = 4, StringLiteral = 5, MethodRef = 6 }

/// <summary>运行时元数据槽位的已解码内容。Value 为 TypeRef / MethodRef / FieldRef / string。</summary>
public sealed record Usage(UsageKind Kind, uint Index, object Value)
{
    public override string ToString() => Kind == UsageKind.StringLiteral ? $"\"{Value}\"" : $"{Kind}({Value})";
}

public static class MetadataTokens
{
    public static Usage? Decode(ProgramModel model, uint kind, uint index) => (UsageKind)kind switch
    {
        UsageKind.TypeInfo or UsageKind.Il2CppType when index < model.RuntimeTypes.Count => new((UsageKind)kind, index, model.RuntimeTypes[(int)index]),
        UsageKind.MethodDef when index < model.Methods.Count => new(UsageKind.MethodDef, index, new MethodRef(model.Methods[(int)index], [], [])),
        UsageKind.FieldInfo when index < model.FieldRefs.Count => new(UsageKind.FieldInfo, index, model.FieldRefs[(int)index]),
        UsageKind.StringLiteral when index < model.StringLiterals.Count => new(UsageKind.StringLiteral, index, model.StringLiterals[(int)index]),
        UsageKind.MethodRef when index < model.MethodSpecs.Count => new(UsageKind.MethodRef, index, model.MethodSpecs[(int)index]),
        _ => null,
    };

    // 只有调用方已证明为槽位时才能使用；可解码整数本身不是槽位证据。
    public static Usage? ReadSlot(IImage image, ProgramModel model, ulong address)
    {
        var info = image.Query(address);
        if (info.Executable || info.Storage != StorageKind.FileContent || info.AvailableBytes < (ulong)image.PointerWidth) return null;
        if (image.ReadPointer(address) is not PointerTarget.NotPointer) return null;
        var raw = image.ReadUnsigned(address, image.PointerWidth);
        if (raw > uint.MaxValue || (raw & 1) == 0) return null;
        return Decode(model, (uint)raw >> 29, ((uint)raw & 0x1fffffff) >> 1);
    }
}
