using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Calls;

namespace Cpp2CS.Idioms;

/// <summary>Enum.ToString 借用的栈上装箱：对象头和标量内容均有完整写入时，恢复一次托管装箱。</summary>
internal static class StackBoxingPass
{
    internal static bool StackBoxing(this IdiomState state)
    {
        var shapes = new CallShapes(state.facts, state.owner.abi, (_, _) => false);
        return Run(state.function, c => shapes.Of(c).Candidates, c => shapes.Of(c).Signature,
            e => state.defs.Expand(e), state.owner.abi.Size, state.Fresh);
    }

    internal static bool Run(MachineFunction function, Func<Call, IReadOnlyList<MethodRef>> candidates,
        Func<Call, MachineSignature?> signature, Func<Expr, Expr> expand, Func<TypeRef, int> size, Func<Variable> fresh)
    {
        static bool Consumer(MethodRef method) => method.Method is
            { IsStatic: false, Name: "ToString", Owner.FullName: "System.Enum", Parameters.Count: 0,
                ReturnType: DefinitionRef { Definition.FullName: "System.String" } };
        bool Exposes(Expr value, long offset, int bytes) => ExprMap.Walk(expand(value)).OfType<FrameAddress>().Any(f => f.Offset < offset + bytes);
        bool MayWrite(Call call, long offset, int bytes)
        {
            var shape = signature(call);
            for (var i = 0; i < call.Arguments.Length; i++)
            {
                if (!Exposes(call.Arguments[i], offset, bytes)) continue;
                if (candidates(call) is [var consumer] && Consumer(consumer) && call.Sources.ElementAtOrDefault(i) == Storage.Gpr(0)) continue;
                var value = shape?.Indirections.FirstOrDefault(v => v.Pieces[0].Register == call.Sources.ElementAtOrDefault(i));
                if (value is { Size: > 0 } && expand(call.Arguments[i]) is FrameAddress frame
                    && (frame.Offset + value.Size <= offset || frame.Offset >= offset + bytes)) continue;
                return true;
            }
            return false;
        }
        List<Expr>? Stored(Block block, int before, long offset, int bytes)
        {
            var budget = 512;
            var active = new HashSet<Block>();
            List<Expr>? Visit(Block current, int end)
            {
                if (--budget < 0 || current.IsLandingPad || !active.Add(current)) return null;
                List<Expr>? result = null;
                for (var i = end - 1; i >= 0; i--)
                {
                    if (current.Statements[i] is Call call && MayWrite(call, offset, bytes)) { active.Remove(current); return null; }
                    if (current.Statements[i] is not Store store) continue;
                    if (expand(store.Target) is not FrameAddress target) { active.Remove(current); return null; }
                    if (target.Offset >= offset + bytes || target.Offset + store.Value.Width / 8 <= offset) continue;
                    if (target.Offset <= offset && target.Offset + store.Value.Width / 8 >= offset + bytes)
                        result = [Fold.Extract(expand(store.Value), checked((int)(offset - target.Offset) * 8), bytes * 8)];
                    active.Remove(current);
                    return result;
                }
                if (current.Predecessors.Count > 0)
                {
                    result = [];
                    foreach (var predecessor in current.Predecessors)
                    {
                        var incoming = Visit(predecessor, predecessor.Statements.Count);
                        if (incoming is null) { result = null; break; }
                        result.AddRange(incoming);
                    }
                }
                active.Remove(current);
                return result;
            }
            return Visit(block, before);
        }
        var changed = false;
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call call || candidates(call) is not [var method] || !Consumer(method)
                    || call.ArgumentIndex(Storage.Gpr(0)) is var receiver && receiver < 0
                    || expand(call.Arguments[receiver]) is not FrameAddress frame) continue;
                var headers = Stored(block, i, frame.Offset, 8);
                if (headers is not [Symbol { Kind: SymbolKind.Class, Value: DefinitionRef { Definition.IsEnum: true } type }, ..]
                    || headers.Any(h => h != headers[0]) || size(type) is not (1 or 2 or 4 or 8)) continue;
                var monitors = Stored(block, i, frame.Offset + 8, 8);
                if (monitors is not { Count: > 0 } || monitors.Any(m => m is not Const { Value: ulong.MaxValue, Width: 64 })
                    || Stored(block, i, frame.Offset + RuntimeLayout.ObjectHeaderSize, size(type)) is not { Count: > 0 }) continue;
                var result = fresh();
                block.Statements.Insert(i++, new Call(call.Address, CallKind.Direct, Expr.C(0, 64))
                {
                    Op = new(OpKind.Box, type), Arguments = [headers[0], new FrameAddress(frame.Offset + RuntimeLayout.ObjectHeaderSize)],
                    Sources = [Storage.Gpr(0), Storage.Gpr(1)], Results = [result.Storage], Defines = [result],
                });
                var arguments = call.Arguments.ToArray();
                arguments[receiver] = new Use(result, 64);
                block.Statements[i] = call with { Arguments = arguments };
                changed = true;
            }
        return changed;
    }
}
