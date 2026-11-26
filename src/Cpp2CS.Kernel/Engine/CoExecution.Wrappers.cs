using Cpp2CS.Kernel.Sources;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Kernel.Engine;

public sealed partial class CoExecution
{
    /// <summary>展开包装自己的快照（设计 6.2、7.1、8）。返回被调用的入口，包装不因此取得目标的名字。</summary>
    public static ulong? WrapperTarget(MethodSnapshot snapshot, Func<ulong, Callee> named, IReadOnlyList<Slot>? abiArguments = null)
    {
        if (snapshot.Blocks.Sum(b => b.Occurrences.Count(o => o is CallOccurrence)) != 1) return null;
        var graph = new PlacedGraph(snapshot);
        var walk = new ValueSources(graph, snapshot.Terms).Walk(new([new(graph.Entry, 0)], []));
        if (walk.Status != WalkStatus.Complete || walk.Paths.Length == 0) return null;
        var equal = PathConditions.Empty(snapshot.Terms);
        Term? Entry(Slot slot) => snapshot.EntryParameters.FirstOrDefault(t => t.Slot == slot);
        ulong? target = null;
        foreach (var path in walk.Paths)
        {
            if (path.Steps.Length == 0) return null;
            var last = path.Steps[^1];
            if (snapshot[last.Occurrence] is not CallOccurrence { Target: not null } call ||
                !last.Operands[0].IsConstant) return null;
            ulong address = (ulong)last.Operands[0].Value;
            var callee = named(address);
            if (callee.Kind == CalleeKind.Managed || callee.Basis.Length == 0 || target.HasValue && target != address) return null;
            target = address;
            Term? Given(Slot slot) => call.ArgumentSlots.IndexOf(slot) is int i && i >= 0 ? last.Operands[i + 1] : null;
            bool Unchanged(Slot slot) => Given(slot) is { } actual && Entry(slot) is { } expected && equal.Same(actual, expected);
            if (callee.Operation is { Arguments: >= 0 } op)
            {
                for (int i = 0; i < op.Arguments; i++)
                    if (!Unchanged(new(SlotKind.Integer, i))) return null;
            }
            else
            {
                // 无原型只接受所有入口实参槽（含栈指针与间接结果指针）原样转交、没有其他出现的尾调用。
                if (!call.ByJump || path.Steps.Length != 1 || abiArguments is not { Count: > 0 } ||
                    abiArguments.Any(slot => !Unchanged(slot))) return null;
            }
            if (call.ByJump)
            {
                if (path.End != PathEnd.Return || path.Steps.Length != 1) return null;
                for (int k = 0; k < snapshot.ReturnSlots.Length; k++)
                {
                    var slot = snapshot.ReturnSlots[k];
                    int r = call.ResultSlots.IndexOf(slot);
                    var expected = r >= 0 ? graph.Results(last.Occurrence)[r] : Entry(slot);
                    if (expected == null || !equal.Same(path.Outcome[k], expected)) return null;
                }
            }
            else
            {
                if (path.End != PathEnd.NoReturn || callee.Operation?.Returns != false) return null;
                var sp = new Slot(SlotKind.StackPointer, 0);
                if (Entry(sp) is not { } pointer || Given(sp) is not { } stack ||
                    FrameOffset(stack, pointer) is not long bottom || bottom > 0) return null;
                // 不返回的目标没有返回行。调用前仅允许写入为本帧留出的私有区间，具名原型的实参已逐槽核对。
                foreach (var step in path.Steps.AsSpan()[..^1])
                {
                    if (snapshot[step.Occurrence] is not WriteOccurrence write ||
                        FrameOffset(step.Operands[0], pointer) is not long offset ||
                        offset < bottom || offset > -(write.Value.Width + 7L) / 8) return null;
                }
            }
        }
        return target;
    }
}
