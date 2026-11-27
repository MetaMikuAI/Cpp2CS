using Cpp2CS.Kernel.Engine;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Kernel.Facts;

/// <summary>共享泛型代码对方法结构、类结构与上下文表中指针字的读取（设计 18.3）。</summary>
internal static class StructureReads
{
    internal static Term? Name(Term address, int width, INativeFacts facts, TermPool terms)
    {
        var layout = facts.Layout;
        if (width != layout.PointerBits || address.Width != layout.PointerBits) return null;
        Term root = address;
        UInt128 offset = 0;
        if (address is { Kind: TermKind.Operation, Op: Op.Add } && address.Operands[1].IsConstant)
        {
            root = address.Operands[0];
            offset = address.Operands[1].Value;
        }
        if (root.Kind == TermKind.Entity)
        {
            var owner = root.Entity;
            if (owner.Kind == EntityKind.Method && offset == (uint)layout.MethodClassOffset &&
                facts.MethodClass(owner) is { } type)
                return terms.Entity(type, width);
            if (owner.Kind == EntityKind.Method && offset == (uint)layout.MethodRgctxOffset ||
                owner.Kind == EntityKind.Type && offset == (uint)layout.ClassRgctxOffset)
                return terms.Attribute(new AttributeId(KernelAttributes.RgctxTable), width, root);
        }
        if (root is { Kind: TermKind.Attribute, Attribute.Value: KernelAttributes.RgctxTable } &&
            root.Operands[0] is { Kind: TermKind.Entity } entity)
        {
            uint stride = (uint)(width / 8);
            if (offset % stride == 0 && offset / stride <= int.MaxValue &&
                facts.RgctxEntry(entity.Entity, (int)(offset / stride)) is { Kind: RgctxKind.Class or RgctxKind.Method } entry)
                return terms.Entity(entry.Entity, width);
        }
        return null;
    }
}
