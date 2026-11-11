using Cpp2CS.Input;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Pipeline;

public sealed class IntegerRecoveryStage : IMethodStage<NativeFunction, ManagedBody>
{
    public string Name => "恢复";
    public StageResult<ManagedBody> Run(NativeFunction input, MethodContext context)
    {
        if (context.Facts.Architecture != "arm64")
            return new Missing<ManagedBody>(new(Name, context.Entry.Address, "绑定", new("lowering.Binding", "该架构的 ABI 尚未装配")));
        var pointer = context.Facts.Image.PointerWidth;
        var layouts = new FieldLayouts(context.Facts.Spec, pointer, pointer);
        var binder = new MethodBinder(new(layouts, pointer * 8), new Aapcs64());
        var kind = context.Entry.Kind switch
        {
            EntryKind.Method => BindingEntryKind.Ordinary,
            EntryKind.GenericMethod => BindingEntryKind.SharedGeneric,
            EntryKind.AdjustorThunk or EntryKind.GenericAdjustorThunk => BindingEntryKind.AdjustorThunk,
            EntryKind.Invoker => BindingEntryKind.Invoker,
            _ => BindingEntryKind.Wrapper,
        };
        var result = new IntegerLowering(input, MethodRef.Open(context.Method), binder,
            new ManagedTypes(context.Facts.Model, layouts, pointer)).Run(kind);
        return result.Body is { } body ? new Completed<ManagedBody>(body)
            : new Missing<ManagedBody>(new(Name, result.Failure!.Position == 0 ? context.Entry.Address : result.Failure.Position,
                result.Failure.Kind.ToString(), result.Failure.Reason));
    }
}
