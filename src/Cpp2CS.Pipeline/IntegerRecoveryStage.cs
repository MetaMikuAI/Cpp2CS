using System.Reflection;
using Cpp2CS.Input;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Output;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Runtime;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Pipeline;

public sealed class IntegerRecoveryStage : IMethodStage<NativeFunction, ManagedBody>
{
    private sealed record Components(MethodBinder Binder, ManagedTypes Types, CallNamingQuery Calls);
    private readonly System.Runtime.CompilerServices.ConditionalWeakTable<GlobalFacts, Lazy<Components>> components = [];
    private static Components Create(GlobalFacts facts)
    {
        var pointer = facts.Image.PointerWidth;
        var layouts = new FieldLayouts(facts.Spec, pointer, pointer);
        var binder = new MethodBinder(new(layouts, pointer * 8), new Aapcs64());
        var spec = facts.Spec.Layout;
        var calls = new CallNamingQuery(binder, new NamingCodeMap(facts.CodeMap),
            new RuntimeFunctionMap(facts.RuntimeFunctions), RuntimeFunctionCatalog.Select(spec.UnityVersion, spec.Triple, spec.DataModel));
        return new(binder, new ManagedTypes(facts.Model, layouts, pointer), calls);
    }
    public string Name => "恢复";
    public StageResult<ManagedBody> Run(NativeFunction input, MethodContext context)
    {
        if (context.Facts.Architecture != "arm64")
            return new Missing<ManagedBody>(new(Name, context.Entry.Address, "绑定", new("lowering.Binding", "该架构的 ABI 尚未装配")));
        // 映像的异常范围尚未接入前端时，不能把受保护调用当作普通调用发布。
        var protectedCall = input.Blocks.SelectMany(b => b.Statements).OfType<Call>().FirstOrDefault(call =>
            call.Trace is { } trace && context.Facts.Image.TryRegions.Any(region => region.Handler is not null
                && trace.NativeAddress >= region.Start && trace.NativeAddress - region.Start < region.Length));
        if (protectedCall is not null)
            return new Missing<ManagedBody>(new(Name, protectedCall.Trace!.NativeAddress, "Exception",
                new("lowering.Exception", "映像中的调用有异常处理入口，异常流尚未接入下降")));
        var parts = components.GetValue(context.Facts, facts => new(() => Create(facts))).Value;
        var kind = context.Entry.Kind switch
        {
            EntryKind.Method => BindingEntryKind.Ordinary,
            EntryKind.GenericMethod => BindingEntryKind.SharedGeneric,
            EntryKind.AdjustorThunk or EntryKind.GenericAdjustorThunk => BindingEntryKind.AdjustorThunk,
            EntryKind.Invoker => BindingEntryKind.Invoker,
            _ => BindingEntryKind.Wrapper,
        };
        var types = parts.Types;
        var transformed = StructureRecovery.Run(input, context, parts.Binder, kind, parts.Types.Layouts);
        var result = new IntegerLowering(transformed.Function, MethodRef.Open(context.Method), parts.Binder,
            types, context.Facts.Image, parts.Calls, new ManagedCallEffects(parts.Calls), context.Facts.Spec, transformed.Names).Run(kind);
        if (result.Body is { } candidate)
        {
            var attributes = context.Method.Attributes;
            var implementation = context.Method.ImplAttributes;
            if ((attributes & (MethodAttributes.Abstract | MethodAttributes.PinvokeImpl)) != 0
                || (implementation & (MethodImplAttributes.InternalCall | MethodImplAttributes.Unmanaged)) != 0
                || (implementation & MethodImplAttributes.CodeTypeMask) is MethodImplAttributes.Native or MethodImplAttributes.Runtime)
                return new Missing<ManagedBody>(new(Name, context.Entry.Address, "方法声明",
                    new("lowering.NonCilBody", "方法声明不允许普通 CIL 方法体")));
            // 位重解释与浮点取整等依赖匹配核心库的 BCL 方法；裁剪掉的能力是缺口，不交给输出层制造非法体。
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
                if (value is UnaryValue math && MathMethods.Uses(math) && MathMethods.Find(types, math) is null)
                    return new Missing<ManagedBody>(new(Name, context.Entry.Address, "标量表示",
                        new("lowering.MathMethod", "匹配核心库缺少所需的 System.Math 方法")));
            }
        }

        return result.Body is { } body ? new Completed<ManagedBody>(body)
            : new Missing<ManagedBody>(new(Name, result.Failure!.Position == 0 ? context.Entry.Address : result.Failure.Position,
                result.Failure.Kind.ToString(), result.Failure.Reason));
    }
}
