using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Storage;



/// <summary>连续分片复制的物理范围在类型确定前保持完整，防止标量提升拆走聚合值的尾部。</summary>
internal static class CopySpans
{
    internal static IEnumerable<(long Offset, int Size)> Read(MachineFunction function)
    {
        var definitions = function.Blocks.SelectMany(b => b.Statements.OfType<Define>()).ToDictionary(d => d.Target, d => d.Value);
        (Expr Root, long Offset) Split(Expr address)
        {
            var form = AddressForm.Decompose(address, new() { Shape = AddressShape.LeftConstants });
            return (form.Root!, form.Offset);
        }

        foreach (var block in function.Blocks)
        {
            var pieces = new List<(Expr Root, long Origin, int At, int Size)>();
            foreach (var store in block.Statements.OfType<Store>())
            {
                if (store.Value is not Use use || !definitions.TryGetValue(use.Variable, out var value)) continue;
                var load = value switch
                {
                    Load direct => direct,
                    Ir.Convert { Kind: ConvKind.ZeroExtend, Operand: Load { Width: 8 or 16 or 32 } narrow } => narrow,
                    _ => null,
                };
                if (load is not { Width: 8 or 16 or 32 or 64 or 128 } || load.Width != use.Width) continue;
                if (store.Target is FrameAddress to && load.Address is not FrameAddress)
                {
                    var source = Split(load.Address);
                    if (source.Offset is < int.MinValue or > int.MaxValue) continue;
                    pieces.Add((source.Root, to.Offset - source.Offset, checked((int)source.Offset), load.Width / 8));
                }
                if (load.Address is FrameAddress from && store.Target is not FrameAddress)
                {
                    var target = Split(store.Target);
                    if (target.Offset is < int.MinValue or > int.MaxValue) continue;
                    pieces.Add((target.Root, from.Offset - target.Offset, checked((int)target.Offset), load.Width / 8));
                }
            }
            foreach (var group in pieces.GroupBy(p => (p.Root, p.Origin)))
            {
                var ordered = group.Distinct().OrderBy(p => p.At).ToArray();
                if (!ordered.Any(p => p.Size == 16)) continue;
                foreach (var range in ValueCoverage.Merge(ordered.Select(p => new StorageRange(p.At, p.Size))))
                    yield return (group.Key.Origin + range.Offset, range.Size);
            }
        }
    }
}
