using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Ssa;

namespace Cpp2CS.Recovery;

/// <summary>托管调用已定型后，用 ref 参数的完整大小区分相邻的独立栈局部。</summary>
internal static class ManagedFramePromotion
{
    public static void Run(ProgramFacts facts, MachineFunction function, ManagedAbi abi, ICallModel calls, Storage stackPointer)
    {
        var signatures = new Dictionary<Call, AbiSignature?>(ReferenceEqualityComparer.Instance);
        AbiSignature? Signature(Call call)
        {
            if (!signatures.TryGetValue(call, out var signature))
            {
                var candidates = call.Op?.Operand is MethodRef method ? [method]
                    : call.Op is null && call.Target is Const target
                        ? facts.EntriesAt(target.Value).Select(e => e.Method).OfType<MethodRef>().Distinct().ToArray() : [];
                var exact = call.Arguments.OfType<Symbol>().Where(s => s.Kind == SymbolKind.Method).Select(s => (MethodRef)s.Value)
                    .Where(m => candidates.Any(c => c.Method == m.Method)).Distinct().ToArray();
                var callee = call.Op is null && call.Target is Const address && facts.Unregistered.At(address.Value) is { } identity
                    ? UnregisteredMethods.Resolve(identity, call, e => e, abi, out _)
                    : exact is [var known] ? known : candidates is [var only] ? only : null;
                signature = callee is null ? null : abi.Classify(callee, out _);
                signatures[call] = signature;
            }
            return signature;
        }
        int? ArgumentSize(Call call, int index)
        {
            if (call.Op?.Kind == OpKind.WriteBarrier && index == 0) return 8;
            if (index >= call.Sources.Length) return null;
            var signature = Signature(call);
            if (signature is null) return null;
            var register = call.Sources[index];
            var argument = signature.Arguments.Concat(signature.Return is { Passing: Passing.Indirect } result ? [result] : [])
                .FirstOrDefault(a => a.Pieces is [var piece] && piece.Register == register);
            var type = argument?.Passing == Passing.Indirect ? argument.Type : (argument?.Type as ByRefRef)?.Element;
            return type is not null && abi.Size(type) is > 0 and var size ? size : null;
        }
        var statements = function.Blocks.SelectMany(b => b.Statements).ToArray();
        var stores = statements.OfType<Store>().Where(s => s is { Target: FrameAddress, Value: Use })
            .ToLookup(s => ((Use)s.Value).Variable);
        var preserved = new List<(long Offset, int Size)>();
        foreach (var call in statements.OfType<Call>())
            for (var i = 0; i < call.Arguments.Length; i++)
                if (call.Arguments[i] is FrameAddress frame && ArgumentSize(call, i) is { } size) preserved.Add((frame.Offset, size));
        foreach (var call in statements.OfType<Call>().Where(c => c.Defines.Any(v => v is not null && stores.Contains(v))))
            if (Signature(call)?.Return is { Passing: Passing.Registers } result && abi.Kind(result.Type) == ValueKind.Struct)
                foreach (var piece in result.Pieces)
                {
                    var index = Array.IndexOf(call.Results, piece.Register);
                    if (index < 0 || index >= call.Defines.Length || call.Defines[index] is not { } variable) continue;
                    foreach (var store in stores[variable]) preserved.Add((((FrameAddress)store.Target).Offset - piece.Offset, abi.Size(result.Type)));
                }
        // 已定型结构体经逐片读写复制到另一段栈时，两侧都保留物理布局供后续整体恢复。
        var definitions = statements.OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
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
        if (Environment.GetEnvironmentVariable("CPP2CS_FRAME_DEBUG") == function.Entry.ToString("x"))
            foreach (var call in statements.OfType<Call>())
                for (var i = 0; i < call.Arguments.Length; i++)
                    if (ExprMap.Walk(call.Arguments[i]).Any(e => e is FrameAddress))
                        Console.Error.WriteLine($"[frame] 0x{call.Address:x} {call.Op} {call.Target} arg{i} {call.Arguments[i]} size={ArgumentSize(call, i)}");
        if (!Lifting.FunctionLifter.PromoteFrameSlots || FrameSlotPromotion.Run(function, ArgumentSize, ranges.ToArray()) == 0) return;
        var slots = function.Blocks.SelectMany(b => b.Statements).OfType<Assign>().Select(a => a.Target).ToHashSet();
        var dominators = Dominators.Compute(function);
        SsaBuilder.Build(function, dominators, slots.Contains, calls, stackPointer);
    }
}
