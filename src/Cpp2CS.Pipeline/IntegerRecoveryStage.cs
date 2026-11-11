using System.Reflection;
using Cpp2CS.Input;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Output;
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
        var types = new ManagedTypes(context.Facts.Model, layouts, pointer);
        var result = new IntegerLowering(input, MethodRef.Open(context.Method), binder, types, context.Facts.Image).Run(kind);
        if (result.Body is { } candidate)
        {
            var attributes = context.Method.Attributes;
            var implementation = context.Method.ImplAttributes;
            if ((attributes & (MethodAttributes.Abstract | MethodAttributes.PinvokeImpl)) != 0
                || (implementation & (MethodImplAttributes.InternalCall | MethodImplAttributes.Unmanaged)) != 0
                || (implementation & MethodImplAttributes.CodeTypeMask) is MethodImplAttributes.Native or MethodImplAttributes.Runtime)
                return new Missing<ManagedBody>(new(Name, context.Entry.Address, "方法声明",
                    new("lowering.NonCilBody", "方法声明不允许普通 CIL 方法体")));
            // 位重解释依赖匹配核心库的 BCL 方法；裁剪掉的能力是缺口，不交给输出层制造非法体。
            foreach (var value in candidate.Blocks.SelectMany(b => b.Statements)
                .SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk))
            {
                bool missing = value switch
                {
                    ConversionValue { Kind: ConversionKind.Bitcast } cast
                        when (types.Kind(cast.Type) is TypeKind.Float or TypeKind.Double) != (types.Kind(cast.Operand.Type) is TypeKind.Float or TypeKind.Double)
                        => BitConversions.Find(types, cast.Operand.Type, cast.Type) is null,
                    ConstantValue constant when BitConversions.ConstantNeedsBitcast(types, constant)
                        => BitConversions.Find(types, types.Integer(constant.Width, false), constant.Type) is null,
                    _ => false,
                };
                if (missing) return new Missing<ManagedBody>(new(Name, context.Entry.Address, "标量表示",
                    new("lowering.BitRepresentation", "匹配核心库缺少同宽浮点位重解释方法")));
            }
        }
        return result.Body is { } body ? new Completed<ManagedBody>(body)
            : new Missing<ManagedBody>(new(Name, result.Failure!.Position == 0 ? context.Entry.Address : result.Failure.Position,
                result.Failure.Kind.ToString(), result.Failure.Reason));
    }
}
