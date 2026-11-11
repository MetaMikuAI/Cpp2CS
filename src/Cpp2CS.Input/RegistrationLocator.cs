#nullable enable
using System.Buffers.Binary;
using Cpp2CS.Native.Images;
using Il2CppDumper;
namespace Cpp2CS.Input;

internal static class RegistrationLocator
{
    internal static (ulong Code, ulong Metadata) Find(RuntimeData data, Metadata metadata)
    {
        var image = data.Image;
        if (image.PointerWidth != data.Spec.Layout.Primitive("void *").Size || image.ByteOrder != ByteOrder.LittleEndian)
            throw new NotSupportedException("映像指针宽度或字节序与运行时规格不匹配。");
        var modules = metadata.imageDefs.ToDictionary(i => metadata.GetStringFromIndex(i.nameIndex),
            i => metadata.typeDefs.Skip(i.typeStart).Take((int)i.typeCount).Sum(t => (long)t.method_count));
        var codes = new List<ulong>();
        var metas = new List<ulong>();
        foreach (var range in image.Ranges.Where(r => !r.Executable && r.Storage == StorageKind.FileContent))
        {
            var bytes = new byte[checked((int)range.Length)];
            image.ReadBytes(range.Start, bytes);
            for (var i = 0; i + sizeof(uint) <= bytes.Length; i += image.PointerWidth)
            {
                var count = BinaryPrimitives.ReadUInt32LittleEndian(bytes.AsSpan(i));
                var at = range.Start + (ulong)i;
                if (count == metadata.typeDefs.Length && at >= data.Offset("Il2CppMetadataRegistration", "typeDefinitionsSizesCount"))
                {
                    var candidate = at - data.Offset("Il2CppMetadataRegistration", "typeDefinitionsSizesCount");
                    if (Fits(candidate, "Il2CppMetadataRegistration") &&
                        data.Number(candidate, "Il2CppMetadataRegistration", "fieldOffsetsCount") == count &&
                        ArrayFits(candidate, "Il2CppMetadataRegistration", "types", "typesCount", (ulong)image.PointerWidth) &&
                        ArrayFits(candidate, "Il2CppMetadataRegistration", "fieldOffsets", "fieldOffsetsCount", (ulong)image.PointerWidth) &&
                        ArrayFits(candidate, "Il2CppMetadataRegistration", "typeDefinitionsSizes", "typeDefinitionsSizesCount", (ulong)image.PointerWidth))
                        metas.Add(candidate);
                }
                if (count == modules.Count && at >= data.Offset("Il2CppCodeRegistration", "codeGenModulesCount"))
                {
                    var candidate = at - data.Offset("Il2CppCodeRegistration", "codeGenModulesCount");
                    if (!Fits(candidate, "Il2CppCodeRegistration") || !ArrayFits(candidate, "Il2CppCodeRegistration", "codeGenModules", "codeGenModulesCount", (ulong)image.PointerWidth)) continue;
                    var array = data.Pointer(candidate, "Il2CppCodeRegistration", "codeGenModules");
                    var names = new HashSet<string>();
                    var valid = true;
                    for (var k = 0u; k < count; k++)
                    {
                        if (image.ReadPointer(array + k * (ulong)image.PointerWidth) is not PointerTarget.Internal p || !Fits(p.Offset, "Il2CppCodeGenModule")) { valid = false; break; }
                        var nameSlot = p.Offset + data.Offset("Il2CppCodeGenModule", "moduleName");
                        if (image.ReadPointer(nameSlot) is not PointerTarget.Internal name || image.Query(name.Offset).Storage != StorageKind.FileContent) { valid = false; break; }
                        var text = data.CString(name.Offset);
                        if (!modules.TryGetValue(text, out var expected) || !names.Add(text) ||
                            data.Number(p.Offset, "Il2CppCodeGenModule", "methodPointerCount") != (ulong)expected) { valid = false; break; }
                    }
                    if (valid) codes.Add(candidate);
                }
            }
        }
        if (codes.Count != 1 || metas.Count != 1)
            throw new InvalidDataException($"注册表定位失败或映像与元数据不匹配：CodeRegistration 候选 {codes.Count}，MetadataRegistration 候选 {metas.Count}，均要求唯一。");
        return (codes[0], metas[0]);

        bool Fits(ulong at, string record) => image.Query(at).AvailableBytes >= data.Size(record);
        bool ArrayFits(ulong at, string record, string pointer, string count, ulong stride)
        {
            var length = data.Number(at, record, count);
            return length > 0 && length <= int.MaxValue &&
                image.ReadPointer(at + data.Offset(record, pointer)) is PointerTarget.Internal p &&
                image.Query(p.Offset).AvailableBytes / stride >= length;
        }
    }
}
