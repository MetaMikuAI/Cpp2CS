using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Recovery;

/// <summary>托管调用已定型后，用 ref 参数的完整大小区分相邻的独立栈局部。</summary>
internal static class ManagedFramePromotion
{
    public static void Run(ProgramFacts facts, MachineFunction function, ManagedAbi abi, ICallModel calls, Storage stackPointer, AbiValue? returned)
    {
        var frames = new ManagedCallFrames(facts, abi);
        var statements = function.Blocks.SelectMany(b => b.Statements).ToArray();
        var stores = statements.OfType<Store>().Where(s => s is { Target: FrameAddress, Value: Use })
            .ToLookup(s => ((Use)s.Value).Variable);
        var preserved = new List<(long Offset, int Size)>();
        preserved.AddRange(FrameCopySpans.Read(function));
        foreach (var call in statements.OfType<Call>())
            for (var i = 0; i < call.Arguments.Length; i++)
                if (call.Arguments[i] is FrameAddress frame && frames.ArgumentSize(call, i) is { } size) preserved.Add((frame.Offset, size));
        foreach (var call in statements.OfType<Call>().Where(c => c.Defines.Any(v => v is not null && stores.Contains(v))))
            // HFA 的各寄存器本来就是独立浮点值；单个分量的暂存不代表整份聚合布局。
            if (frames.Signature(call)?.Return is { Passing: Passing.Registers } result && abi.Kind(result.Type) == ValueKind.Struct && abi.Hfa(result.Type) is null)
                foreach (var piece in result.Pieces)
                {
                    var index = Array.IndexOf(call.Results, piece.Register);
                    if (index < 0 || index >= call.Defines.Length || call.Defines[index] is not { } variable) continue;
                    foreach (var store in stores[variable]) preserved.Add((((FrameAddress)store.Target).Offset - piece.Offset, abi.Size(result.Type)));
                }
        // 已定型结构体经逐片读写复制到另一段栈时，两侧都保留物理布局供后续整体恢复。
        var definitions = statements.OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        var loadedDefinitions = statements.OfType<Define>().ToDictionary(d => d.Target);
        // 自身返回签名同样要求完整布局，避免先把聚合中的引用字段拆成独立标量。
        if (returned is { Passing: Passing.Registers } && abi.Kind(returned.Type) == ValueKind.Struct)
            foreach (var statement in statements.OfType<Return>())
                if (statement.Value is { } value && FrameArgumentSpan.ReturnLoads(value, returned.Pieces, abi.Size(returned.Type),
                    loadedDefinitions, e => e is FrameAddress frame ? frame.Offset : null) is { } span)
                    preserved.Add((span.Origin, abi.Size(returned.Type)));
        // 按值传参的结构体同样需要完整布局，不能先把其中的引用字段单独提升。
        foreach (var call in statements.OfType<Call>())
        {
            if (frames.Signature(call) is not { } signature) continue;
            var registers = call.ArgumentsBySource();
            foreach (var argument in signature.Arguments.Where(a => a.Passing == Passing.Registers && abi.Kind(a.Type) == ValueKind.Struct))
            {
                var pieces = new List<(int Offset, int Width, long Frame)>();
                foreach (var piece in argument.Pieces)
                {
                    if (!registers.TryGetValue(piece.Register, out var value) || FrameArgumentSpan.Loaded(value, loadedDefinitions) is not { } read
                        || read.Load.Width != piece.Width || read.Load.Address is not FrameAddress frame) break;
                    pieces.Add((piece.Offset, piece.Width, frame.Offset));
                }
                var size = abi.Size(argument.Type);
                if (pieces.Count == argument.Pieces.Length && FrameArgumentSpan.Origin(size, pieces) is { } origin) preserved.Add((origin, size));
            }
        }
        var copies = statements.OfType<Store>().Where(s => s is { Target: FrameAddress, Value: Use })
            .Select(s => (Store: s, Value: definitions.GetValueOrDefault(((Use)s.Value).Variable)))
            .Where(p => p.Value is Load { Address: FrameAddress } load && load.Width == p.Store.Value.Width)
            .Select(p => (From: ((FrameAddress)((Load)p.Value!).Address).Offset, To: ((FrameAddress)p.Store.Target).Offset, Size: p.Store.Value.Width / 8)).ToArray();
        var ranges = preserved.ToHashSet();
        bool changed;
        do
        {
            changed = false;
            foreach (var copy in copies)
            {
                if (ranges.Any(r => r.Offset < copy.From + copy.Size && copy.From < r.Offset + r.Size)) changed |= ranges.Add((copy.To, copy.Size));
                if (ranges.Any(r => r.Offset < copy.To + copy.Size && copy.To < r.Offset + r.Size)) changed |= ranges.Add((copy.From, copy.Size));
            }
        } while (changed);
        if (facts.Options.Diagnostics.Frames.Contains(function.Entry))
            foreach (var call in statements.OfType<Call>())
                for (var i = 0; i < call.Arguments.Length; i++)
                    if (ExprMap.Walk(call.Arguments[i]).Any(e => e is FrameAddress))
                        facts.Options.Diagnostics.Write("frame", function.Entry, $"[frame] 0x{call.Address:x} {call.Op} {call.Target} arg{i} {call.Arguments[i]} size={frames.ArgumentSize(call, i)}");
        if (!facts.Options.PromoteFrameSlots || FrameSlotPromotion.Run(function, frames.ArgumentSize, ranges.ToArray(), overlapping: true) == 0) return;
        var slots = function.Blocks.SelectMany(b => b.Statements).OfType<Assign>().Select(a => a.Target).ToHashSet();
        var dominators = Dominators.Compute(function);
        SsaBuilder.Build(function, dominators, slots.Contains, calls, stackPointer);
        // 新的栈局部别名不应遮住连续复制；传播只消除纯副本，不移动读取。
        Propagate.Run(function, dominators);
    }
}
