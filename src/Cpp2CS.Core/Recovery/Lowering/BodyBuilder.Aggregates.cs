using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Lowering;

internal sealed partial class BodyBuilder
{
    private readonly HashSet<Store> aggregateStores = new(ReferenceEqualityComparer.Instance);

    /// <summary>连续写入完整覆盖同一结构体时，按布局拼回整体赋值；不跨越读取或其他副作用。</summary>
    private (Location Target, Sym Value)? AggregateStore(Block block, int index)
    {
        var first = values.Operands(block.Statements[index]);
        var origin = oracle.Decompose(first[0]);
        var parts = new List<Sym> { first[1] };
        var stores = new List<Store>();
        var width = first[1].Width;
        for (var i = index + 1; i < block.Statements.Count; i++)
        {
            var next = block.Statements[i];
            if (Reads(next).Any()) break;
            if (next is Define or Nop) continue;
            if (next is not Store store || aggregateStores.Contains(store)) break;
            var operands = values.Operands(store);
            var target = oracle.Decompose(operands[0]);
            if (width % 8 != 0 || target != origin with { Offset = origin.Offset + width / 8 }) break;
            parts.Add(operands[1]);
            stores.Add(store);
            width += operands[1].Width;
            if (oracle.Locate(first[0], width) is not { Type: DefinitionRef type } location
                || types.Kind(type) != TypeKind.Struct || types.Size(type) * 8 != width) continue;
            aggregateStores.UnionWith(stores);
            return (location, values.Syms.Concat(parts));
        }
        return null;
    }
}
