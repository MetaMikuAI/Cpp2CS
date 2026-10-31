using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Recovery;

/// <summary>仅移除后续所有正常及异常路径均不读取、且地址未逃逸的栈快照写入。</summary>
internal static class DeadFrameStores
{
    internal static HashSet<Stmt> Find(MachineFunction function, Func<Expr, long?> frameOffset,
        Func<Call, long, int, bool> noStackRead, Func<Call, int, int?> argumentSize, Func<Call, int, bool> noCapture,
        IReadOnlySet<Stmt>? preserved = null)
    {
        var result = new HashSet<Stmt>(ReferenceEqualityComparer.Instance);
        var sites = function.Blocks.SelectMany(b => b.Statements.Select((s, i) => (Statement: s, Block: b, Index: i))).ToArray();
        foreach (var site in sites)
        {
            if (preserved?.Contains(site.Statement) == true
                || site.Statement is not Store { Target: FrameAddress { Offset: < 0 } slot, Value: Use { Width: 32 or 64 or 128 } value } store) continue;
            var end = slot.Offset + value.Width / 8;
            if (end > 0) continue;
            bool Overlaps(long at, int? size) => at < end && (size is null || slot.Offset < at + size.Value);
            bool Reads(Expr expression)
            {
                if (expression is Load load && frameOffset(load.Address) is { } at) return Overlaps(at, load.Width / 8);
                if (frameOffset(expression) is { } address) return Overlaps(address, null);
                return ExprMap.Children(expression).Any(Reads);
            }
            bool Escapes(Expr expression)
            {
                if (expression is Load) return false;
                if (frameOffset(expression) is { } address) return Overlaps(address, null);
                return ExprMap.Children(expression).Any(Escapes);
            }
            // 帧地址保存到其他位置或传给可捕获地址的调用时，后续读取可能不再带原帧地址。
            if (sites.Any(s => s.Statement is Define d && Escapes(d.Value)
                || s.Statement is Store saved && Escapes(saved.Value)
                || s.Statement is Call call && call.Arguments.Where((a, i) => frameOffset(a) is { } argument
                    ? Overlaps(argument, argumentSize(call, i)) && !noCapture(call, i) : Escapes(a)).Any())) continue;
            var pending = new Stack<(Block Block, int Index)>();
            var seen = new HashSet<(Block Block, int Index)>();
            pending.Push((site.Block, site.Index + 1));
            var safe = true;
            while (safe && pending.TryPop(out var cursor))
            {
                if (!seen.Add(cursor)) continue;
                foreach (var statement in cursor.Block.Statements.Skip(cursor.Index))
                {
                    safe = statement switch
                    {
                        Store { Target: FrameAddress } written => !Reads(written.Value),
                        Call call => noStackRead(call, slot.Offset, value.Width) && !ExprMap.Operands(call).Any(Reads),
                        Opaque or IndirectJump { Targets.Length: 0 } => false,
                        _ => !ExprMap.Operands(statement).Any(Reads),
                    };
                    if (!safe) break;
                }
                // 异常后继也可能读取保存值，不能只检查正常出口。
                foreach (var successor in cursor.Block.Successors) pending.Push((successor, 0));
            }
            if (safe) result.Add(store);
        }
        return result;
    }
}
