using Cpp2CS.Facts;

namespace Cpp2CS.Model;

public sealed partial class ManagedTypes
{
    /// <summary>托管值的位宽；结构体由字段表达，不使用标量位宽。</summary>
    public int ValueWidth(TypeRef type) => IsReferenceType(type) || type is ByRefRef or PointerRef ? 64
        : Kind(type) == TypeKind.Struct ? 0 : Math.Max(1, Bits(type));

    /// <summary>值类型的标量叶子字段：路径、类型与相对值起点的字节偏移。</summary>
    public IEnumerable<(IReadOnlyList<FieldRef> Path, TypeRef Type, int Offset)> Leaves(DefinitionRef structure, int at = 0)
    {
        if (Layouts.Of(structure) is not { } layout) yield break;
        foreach (var slot in layout.Fields.OrderBy(f => f.Offset))
        {
            var offset = at + slot.Offset - RuntimeLayout.ObjectHeaderSize;
            var field = new FieldRef(slot.Field, structure);
            if (Kind(slot.Type) == TypeKind.Struct && slot.Type is DefinitionRef inner)
                foreach (var (path, type, leaf) in Leaves(inner, offset)) yield return ([field, .. path], type, leaf);
            else yield return ([field], slot.Type, offset);
        }
    }

}
