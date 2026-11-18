using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;

namespace Cpp2CS.Recovery.Locations;

internal sealed record WholeWrite(LocationView Target, BoundSource Source, ImmutableArray<MemoryWrite> Writes);

/// <summary>从字段的布局取得整体位置，以状态层的重叠范围证明连续写入的每一段。</summary>
internal sealed class WholeWriteQuery(ManagedLocationQuery locations, ManagedTypes types, MethodRef method)
    : Query<Point, WholeWrite?>
{
    internal static bool RequiresWhole(FieldRef field, MethodRef method) =>
        (field.Field.Attributes & FieldAttributes.InitOnly) != 0 &&
        !(field.Field.Owner == method.Method.Owner && method.Method.Name == (field.Field.IsStatic ? ".cctor" : ".ctor"));

    public override Outcome<WholeWrite?> Compute(QueryContext c, Point key)
    {
        var state = locations.State;
        var index = c.Get(state.Index, 0);
        if (!index.IsSuccess) return index.Propagate<WholeWrite?>();
        var statements = index.Value.Blocks[key.Block].Statements;
        var first = (MemoryWrite)statements[key.Before];
        var located = c.Get(locations, new(first.Address, first.Width));
        if (!located.IsSuccess) return located.Propagate<WholeWrite?>();
        // 组可能从可写字段开始。以包含首段的值类型为候选，权限只决定是否需要整体视图。
        var seen = new HashSet<(DefinitionRef Type, int Offset)>();
        foreach (var view in located.Value.Views)
            for (int depth = 0; depth < view.Path.Length; depth++)
            {
                var field = view.Path[depth];
                if (field.DeclaringType is not DefinitionRef type || types.Kind(type) != TypeKind.Struct
                    || !type.Definition.Fields.Any(f => !f.IsStatic && RequiresWhole(new(f, type), method))) continue;
                var path = view.Path.Skip(depth).ToArray();
                var projection = types.Project(type, path);
                if (projection is null || projection.Bit % 8 != 0 || view.Offset < 0 || view.Offset >= types.Size(type)) continue;
                int offset = projection.Bit / 8 + (int)view.Offset;
                if (!seen.Add((type, offset)) || first.Width >= types.StorageBits(type)) continue;
                var baseAddress = c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.Subtract), first.Address.Width,
                    first.Address, c.Snapshot.Terms.Constant(offset, first.Address.Width));
                var target = c.Get(locations, new(baseAddress, types.StorageBits(type)));
                if (!target.IsSuccess) return target.Propagate<WholeWrite?>();
                var exact = target.Value.Views.Where(v => v.Type.Equals(type) && v.Offset == 0
                    && v.Root == view.Root && v.Index == view.Index && v.Path.SequenceEqual(view.Path.Take(depth))).ToArray();
                if (exact.Length != 1 || exact[0].Path.Any(f => RequiresWhole(f, method))) continue;
                var group = Cover(c, statements, key.Before, baseAddress, exact[0]);
                if (!group.IsSuccess || group.Value is not null) return group;
            }
        return Outcome<WholeWrite?>.Success(null);
    }

    private Outcome<WholeWrite?> Cover(QueryContext c, ImmutableArray<Statement> statements, int start,
        Term address, LocationView target)
    {
        var state = locations.State;
        Outcome<Location> Storage(Term pointer, int width)
        {
            var resolved = c.Get(state.Resolve, pointer);
            return resolved.IsSuccess ? c.Get(state.Locations, new(resolved.Value, width)) : resolved.Propagate<Location>();
        }
        var storage = Storage(address, target.Width);
        if (!storage.IsSuccess) return storage.Propagate<WholeWrite?>();
        var pieces = new List<BoundPiece>();
        var writes = ImmutableArray.CreateBuilder<MemoryWrite>();
        long bits = 0;
        for (int i = start; i < statements.Length && bits < target.Width; i++)
        {
            if (statements[i] is not MemoryWrite { Release: false } write || write.Width % 8 != 0) break;
            var part = Storage(write.Address, write.Width);
            if (!part.IsSuccess) return part.Propagate<WholeWrite?>();
            var alias = c.Get(state.Alias, new(storage.Value, part.Value));
            if (!alias.IsSuccess) return alias.Propagate<WholeWrite?>();
            if (alias.Value is not { Kind: AliasKind.Overlap, RightLow: 0 } overlap
                || overlap.Width != write.Width || overlap.LeftLow % 8 != 0) break;
            pieces.Add(new(overlap.LeftLow / 8, write.Width / 8, new TermSource(write.Value)));
            writes.Add(write);
            bits += write.Width;
        }
        var source = bits == target.Width ? WholeWriteSource.FromPieces(pieces, target.Width / 8) : null;
        return Outcome<WholeWrite?>.Success(source is null ? null : new(target, source, writes.ToImmutable()));
    }
}
