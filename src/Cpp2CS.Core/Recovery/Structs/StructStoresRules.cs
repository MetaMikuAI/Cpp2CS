using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

/// <summary>非帧结构体目标的写入下降：结构体内清零与整体赋值。</summary>
internal static class StructStoresRules
{
    /// <summary>
    /// 结构体内的清零（例如 <c>this.&lt; &gt;u__1 = default</c> 编译成两个 64 位零写入，第二个覆盖 token 与其后的填充）：
    /// 写入范围落在同一个结构体值之内、只覆盖完整的叶子与填充时，逐叶子写零。填充不是托管值（ECMA-335 I.8.2.1），对照器也不比较它。
    /// </summary>
    [Rule(RuleKind.Store, "structs.store-zero", Order = 150)]
    internal static RecoveryResult<bool> StoreStructZero(this LoweringScope ctx, Store store, List<ManagedStatement> output)
    {
        if (!ctx.Values.FrameZero(store.Value) || ctx.Values.FrameAccess(store.Target) is not null || store.Value.Width < 16)
            return false;
        var width = store.Value.Width;
        if (!ctx.Values.CopyRanges(store.Target, width).TryGet(out var ranges, out var failure))
            return failure;
        var range = ranges.OrderBy(r => ctx.types.Size(r.Type)).FirstOrDefault();
        if (range is null)
            return false;
        var leaves = ctx.Values.StructPaths(range.Type).Where(p => ctx.types.Kind(p.Type) is not (TypeKind.Struct or null) && p.Offset < range.Offset + width / 8 && range.Offset < p.Offset + ctx.types.Size(p.Type)).ToArray();
        if (leaves.Length == 0 || leaves.Any(p => p.Offset < range.Offset || p.Offset + ctx.types.Size(p.Type) > range.Offset + width / 8))
            return false;
        // 恰好是单个叶子的写入走普通路径。
        if (leaves is [var single] && single.Offset == range.Offset && ctx.types.Size(single.Type) * 8 == width)
            return false;
        // 清零恰好覆盖一个结构体位置（如状态机末尾的 <>u__1 = default）：整体 initobj，不逐叶子写私有字段。
        if (ctx.Values.WholeStructAt(range, width) is { } whole)
        {
            output.Add(new ManagedStore(store.Address, new IndirectValue(new AddressValue(whole), whole.Type), new ComposedValue(whole.Type, [])));
            return true;
        }

        foreach (var leaf in leaves)
        {
            var target = ctx.Values.PathValue(range.Root, leaf.Path);
            output.Add(new ManagedStore(store.Address, target, ctx.types.Kind(leaf.Type) == TypeKind.Reference ? new ConstantValue(0, leaf.Type, 64) : new ConstantValue(0, leaf.Type, target.Width)));
        }

        return true;
    }

    /// <summary>
    /// 写入覆盖整个结构体字段，且写入的是同类型结构体值的对应叶子（单叶子结构体，如 this._ctx = ct，CancellationToken 只有私有字段 _source）：
    /// 写成整体赋值，不逐叶子写私有字段。
    /// </summary>
    [Rule(RuleKind.StoreTarget, "structs.store-whole", Order = 50)]
    internal static bool StoreWholeStruct(this LoweringScope ctx, Store store, ManagedValue target, List<ManagedStatement> output)
    {
        // 写入目标：结构体字段本身，或结构体字段的唯一叶子；结构体大小等于写入宽度。由外向内是同大小的各层（如 <>u__1 与它的只读字段 task）。
        var candidates = new List<ManagedValue>();
        // 多叶子的写入目标（片）：各片都是同一个结构体位置的直接叶子时，从这个位置开始。
        ManagedValue? Outer(ManagedValue leaf) => leaf is FieldValue { Receiver: AddressValue { Target: var outer } } ? outer : null;
        var start = ctx.types.Kind(target.Type) == TypeKind.Struct ? target : target is Fragment pieces ? (pieces.Parts.Select(p => Outer(p.Value)).Distinct().ToArray() is [var common] ? common : null) : Outer(target);
        for (var layer = start; layer is not null && ctx.types.Kind(layer.Type) == TypeKind.Struct && ctx.types.Size(layer.Type) * 8 == store.Value.Width; layer = layer is FieldValue { Receiver: AddressValue { Target: var next } } ? next : null)
            candidates.Insert(0, layer);
        if (candidates.Count == 0)
            return false;
        var whole = candidates[0];
        // 写入零：default(T)（initobj），不写私有叶子（如状态机末尾的 <ct>5__2 = default）。
        if (ctx.Values.FrameZero(store.Value))
        {
            output.Add(new ManagedStore(store.Address, new IndirectValue(new AddressValue(whole), whole.Type), new ComposedValue(whole.Type, [])));
            return true;
        }

        if (!ctx.Values.Recover(store.Value, null).TryGet(out var source, out _))
            return false;
        if (whole.Type is DefinitionRef empty && ctx.facts.Layouts.Of(empty) is { Fields.Count: 0 } && source is Fragment { Parts.Count: 0 })
        {
            output.Add(new ManagedStore(store.Address, new IndirectValue(new AddressValue(whole), whole.Type), new ComposedValue(whole.Type, [])));
            return true;
        }
        // 写入的值：同类型结构体值的叶子（单叶子），或各片都是同一个结构体值的叶子（寄存器传递的结构体参数/结果）。
        var parts = source is Fragment fragment ? fragment.Parts.Select(p => p.Value).ToArray() : [source];
        foreach (var layer in candidates)
        {
            var roots = parts.Select(p => FrameCopiesRules.StructRootOf(p, layer.Type)).Distinct().ToArray();
            if (roots is not [{ } value])
                continue;
            output.Add(new ManagedStore(store.Address, new IndirectValue(new AddressValue(layer), layer.Type), value));
            return true;
        }

        return false;
    }
}
