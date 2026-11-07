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
            body.ExceptionHandlers.Add(new ExceptionHandler(region.Kind switch
            {
                ManagedRegionKind.Catch => ExceptionHandlerType.Catch,
                ManagedRegionKind.Finally => ExceptionHandlerType.Finally,
                _ => ExceptionHandlerType.Fault,
            })
            {
                TryStart = labels[region.Try[0]],
                TryEnd = After(region.Try),
                HandlerStart = labels[region.HandlerEntry],
                HandlerEnd = After(region.Handler),
                CatchType = region.Kind == ManagedRegionKind.Catch ? TypeReference(region.CatchType ?? types.Corlib("System.Exception")) : null,
            });
        RouteBranchesIntoTry();
    }

    /// <summary>
    /// 只能经第一条指令进入 try（ECMA-335 I.12.4.2.8.2.7）。原生代码恢复 await 时直接跳到 try 中间，C# 也写不出这种跳转，
    /// 反编译器会丢掉这条分支。改成记下目标编号、跳到 try 开头，再从开头分派到目标；目标在内层 try 时逐层进入。
    /// </summary>
    private void RouteBranchesIntoTry()
    {
        VariableDefinition? dispatch = null;
        var next = 1;
        while (true)
        {
            var position = new Dictionary<Instruction, int>();
            for (var i = 0; i < body.Instructions.Count; i++) position.Add(body.Instructions[i], i);
            bool Inside(Instruction at, ExceptionHandler region) => position[at] >= position[region.TryStart] && position[at] < position[region.TryEnd];
            ExceptionHandler? Entered(Instruction site) => site.Operand is Instruction target
                ? body.ExceptionHandlers.Where(r => Inside(target, r) && !Inside(site, r) && target != r.TryStart).OrderBy(r => position[r.TryStart]).FirstOrDefault()
                : null;
            if (body.Instructions.FirstOrDefault(i => i.OpCode.Code == Code.Br && Entered(i) is not null) is not { } branch) return;
            var entry = Entered(branch)!.TryStart;
            var destination = (Instruction)branch.Operand;
            dispatch ??= Temp(types.Int32);
            var number = next++;
            branch.OpCode = OpCodes.Ldc_I4;
            branch.Operand = number;
            var store = Instruction.Create(OpCodes.Stloc, dispatch);
            il.InsertAfter(branch, store);
            il.InsertAfter(store, Instruction.Create(OpCodes.Br, entry));
            var skip = Instruction.Create(OpCodes.Nop);
            var at = entry;
            foreach (var instruction in new[]
            {
                Instruction.Create(OpCodes.Ldloc, dispatch), Instruction.Create(OpCodes.Ldc_I4, number), Instruction.Create(OpCodes.Ceq),
                Instruction.Create(OpCodes.Brfalse, skip), Instruction.Create(OpCodes.Ldc_I4_0), Instruction.Create(OpCodes.Stloc, dispatch),
                Instruction.Create(OpCodes.Br, destination), skip,
            })
            {
                il.InsertAfter(at, instruction);
                at = instruction;
            }
        }
    }
}
