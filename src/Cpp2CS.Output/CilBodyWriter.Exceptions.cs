using Cpp2CS.Recovery;
using Mono.Cecil.Cil;

namespace Cpp2CS.Output;

internal sealed partial class CilBodyWriter
{
    private IReadOnlyList<ManagedRegion> regions = [];
    private ulong currentBlock;
    private Instruction? exceptionReturn;
    private VariableDefinition? exceptionReturnValue;

    private bool LeavesRegion(ulong target) => regions.Any(r =>
        r.Try.Contains(currentBlock) && !r.Try.Contains(target) || r.Handler.Contains(currentBlock) && !r.Handler.Contains(target));

    private void ReturnFromBlock()
    {
        if (!regions.Any(r => r.Try.Contains(currentBlock) || r.Handler.Contains(currentBlock)))
        { ClearPinnedArrays(); il.Emit(OpCodes.Ret); return; }
        exceptionReturn ??= Instruction.Create(OpCodes.Nop);
        if (!ManagedTypes.IsVoid(methodContext.Method.ReturnType))
        {
            exceptionReturnValue ??= Temp(methodContext.Method.ReturnType);
            il.Emit(OpCodes.Stloc, exceptionReturnValue);
        }
        il.Emit(OpCodes.Leave, exceptionReturn);
    }

    private void WriteExceptionTable(ManagedBody recovered)
    {
        if (regions.Count == 0) return;
        var end = exceptionReturn ?? Instruction.Create(OpCodes.Nop);
        il.Append(end);
        if (exceptionReturn is not null)
        {
            if (exceptionReturnValue is not null) il.Emit(OpCodes.Ldloc, exceptionReturnValue);
            ClearPinnedArrays();
            il.Emit(OpCodes.Ret);
        }
        else { il.Emit(OpCodes.Ldnull); il.Emit(OpCodes.Throw); }
        var positions = recovered.Blocks.Select((b, i) => (b.Address, i)).ToDictionary(p => p.Address, p => p.i);
        Instruction After(IReadOnlyList<ulong> members)
        {
            var last = members.Max(a => positions[a]);
            return last + 1 == recovered.Blocks.Count ? end : labels[recovered.Blocks[last + 1].Address];
        }
        foreach (var region in regions)
            body.ExceptionHandlers.Add(new ExceptionHandler(region.Kind == ManagedRegionKind.Catch ? ExceptionHandlerType.Catch : ExceptionHandlerType.Fault)
            {
                TryStart = labels[region.Try[0]], TryEnd = After(region.Try),
                HandlerStart = labels[region.HandlerEntry], HandlerEnd = After(region.Handler),
                CatchType = region.Kind == ManagedRegionKind.Catch ? TypeReference(region.CatchType ?? types.Corlib("System.Exception")) : null,
            });
    }
}
