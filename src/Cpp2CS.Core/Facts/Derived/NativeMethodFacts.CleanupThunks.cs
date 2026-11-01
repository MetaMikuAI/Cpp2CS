using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Facts.Derived;

internal sealed partial class NativeMethodFacts
{
    internal readonly Dictionary<(ulong, TypeDef), (MethodRef Method, int Depth, bool Inlined)?> cleanupThunks = new();
    internal readonly Dictionary<(ulong, TypeDef), StateDispatch?> stateDispatches = new();

    internal StateDispatch? Dispatch(ulong address, TypeDef owner)
    {
        if (stateDispatches.TryGetValue((address, owner), out var cached)) return cached;
        StateDispatch? result = null;
        if (facts.Code.At(address) is { } range && range.Start == address && range.Size <= 256
            && lifter.Lift(address) is { Succeeded: true } lifted && rewriter.Run(lifted.Function) is { Errors.Count: 0, Residuals.Count: 0 })
            result = StateDispatch.Read(lifted.Function, call => call is { Op: null, Target: Const target, Kind: CallKind.Direct or CallKind.Tail }
                && facts.EntriesAt(target.Value).Any(e => e.Method is { Method: { IsStatic: false, Parameters.Count: 0 } m }
                    && m.Owner == owner && ManagedTypes.IsVoid(m.ReturnType)) ? WithoutMethodInfo(call) : null);
        return stateDispatches[(address, owner)] = result;
    }

    internal (MethodRef Method, int Depth, bool Inlined)? CleanupThunk(ulong address, TypeDef type)
    {
        if (cleanupThunks.TryGetValue((address, type), out var cached)) return cached;
        (MethodRef, int, bool)? result = null;
        if (type.GenericParameters.Count == 0 && facts.Helpers.At(address)?.Kind == HelperKind.Unknown
            && facts.Code.At(address) is { Size: <= 64 } range && range.Start == address
            && lifter.Lift(address) is { Succeeded: true } direct && rewriter.Run(direct.Function) is { Errors.Count: 0, Residuals.Count: 0 }
            && direct.Function.Blocks is [var block] && block.Statements.LastOrDefault() is Call { Op: null, Kind: CallKind.Tail, Target: Const target } tail
            && WithoutMethodInfo(tail) is { Arguments: [Use directReceiver] })
        {
            Expr value = directReceiver;
            var depth = 0;
            var chain = block.Statements.Take(block.Statements.Count - 1).OfType<Define>().ToArray();
            foreach (var definition in chain.Reverse())
            {
                if (value is not Use use || use.Variable != definition.Target || definition.Value is not Load { Width: 64 } load) break;
                value = load.Address;
                depth++;
            }
            var candidates = facts.EntriesAt(target.Value).Select(e => e.Method).OfType<MethodRef>().Distinct().Where(m =>
                !m.Method.IsStatic && m.Method.Owner == type && m.Method.Parameters.Count == 0 && m.Method.GenericParameters.Count == 0
                && ManagedTypes.IsVoid(m.Method.ReturnType)).ToArray();
            if (depth is > 0 and <= 3 && chain.Length == depth && block.Statements.Count == depth + 1
                && value is Use { Variable.Version: 0 } input && input.Variable.Storage == Storage.Gpr(0) && candidates is [var callee])
                result = (callee, depth, false);
        }
        if (result is not null) return cleanupThunks[(address, type)] = result;
        if (type.GenericParameters.Count == 0 && facts.Helpers.At(address)?.Kind == HelperKind.Unknown && Dispatch(address, type) is { } thunk)
        {
            var receiver = thunk.Receiver;
            var depth = 0;
            while (receiver is Load { Width: 64 } load && depth < 3) { receiver = load.Address; depth++; }
            if (depth > 0 && receiver is Use { Variable.Version: 0 } input && input.Variable.Storage == Storage.Gpr(0))
            {
                var candidates = type.Methods.Where(m => !m.IsStatic && m.Parameters.Count == 0 && ManagedTypes.IsVoid(m.ReturnType)
                    && m.Address != 0 && m.GenericParameters.Count == 0 && Dispatch(m.Address, type) is { } dispatch
                    && dispatch.Receiver == receiver && dispatch.Same(thunk)).ToArray();
                if (candidates is [var only]) result = (new(only, [], []), depth, true);
            }
        }
        return cleanupThunks[(address, type)] = result;
    }
}
