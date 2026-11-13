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
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Pipeline;

public sealed class IntegerRecoveryStage : IMethodStage<NativeFunction, ManagedBody>
{
    private sealed record Components(MethodBinder Binder, ManagedTypes Types, CallNamingQuery Calls, AccessorQuery? Accessors, ConstructorQuery? Constructors);
    private readonly System.Runtime.CompilerServices.ConditionalWeakTable<GlobalFacts, Lazy<Components>> components = [];
    private readonly bool enableAccessorInlining;
    private readonly bool enableConstructorInlining;
    private readonly IMethodTemplateSource? constructorSource;
    private readonly Action<ConstructorAttempt>? observeConstructors;
    private readonly IMethodStage<CodeEntry, NativeFunction> templateFrontend;
    private readonly Action<AccessorAttempt>? observeAccessors;
    public IntegerRecoveryStage(IMethodStage<CodeEntry, NativeFunction>? templateFrontend = null,
        bool enableAccessorInlining = true, Action<AccessorAttempt>? observeAccessors = null,
        bool enableConstructorInlining = true, Action<ConstructorAttempt>? observeConstructors = null, IMethodTemplateSource? constructorSource = null)
    {
        this.templateFrontend = templateFrontend ?? new FrontendStage([new FrontendProvider("arm64", RecoverySession.DefaultComponents)]);
        this.enableAccessorInlining = enableAccessorInlining;
        this.observeAccessors = observeAccessors;
        this.enableConstructorInlining = enableConstructorInlining;
        this.observeConstructors = observeConstructors;
        this.constructorSource = constructorSource;
    }
    private Components Create(GlobalFacts facts)
    {
        var pointer = facts.Image.PointerWidth;
        var layouts = new FieldLayouts(facts.Spec, pointer, pointer);
        var binder = new MethodBinder(new(layouts, pointer * 8), new Aapcs64());
        var spec = facts.Spec.Layout;
        var calls = new CallNamingQuery(binder, new NamingCodeMap(facts.CodeMap),
            new RuntimeFunctionMap(facts.RuntimeFunctions), RuntimeFunctionCatalog.Select(spec.UnityVersion, spec.Triple, spec.DataModel));
        var types = new ManagedTypes(facts.Model, layouts, pointer);
        return new(binder, types, calls, enableAccessorInlining
            ? new AccessorQuery(types, new AccessorTemplateSource(facts, templateFrontend), observeAccessors) : null,
            enableConstructorInlining ? new ConstructorQuery(types,
                new ConstructorTemplates(constructorSource ?? new MethodTemplateSource(facts, templateFrontend, constructors: true), types), observeConstructors) : null);
    }
    public string Name => "恢复";
    public StageResult<ManagedBody> Run(NativeFunction input, MethodContext context)
    {
        if (context.Facts.Architecture != "arm64")
            return new Missing<ManagedBody>(new(Name, context.Entry.Address, "绑定", new("lowering.Binding", "该架构的 ABI 尚未装配")));
        if (input.Blocks.SelectMany(b => b.Statements).Any(s => s is ExclusiveEvent))
            return new Missing<ManagedBody>(new(Name, context.Entry.Address, "独占访问",
                new("lowering.Atomic", "恢复层尚未定义独占事件的托管语义")));
        if (input.Blocks.SelectMany(b => b.Statements).Any(s => s is MemoryFence or MemoryRead { Acquire: true } or MemoryWrite { Release: true }))
            return new Missing<ManagedBody>(new(Name, context.Entry.Address, "同步访问",
                new("lowering.Synchronization", "恢复层尚未定义同步访问的托管语义")));
        var parts = components.GetValue(context.Facts, facts => new(() => Create(facts))).Value;
        var kind = context.Entry.Kind switch
        {
            EntryKind.Method => BindingEntryKind.Ordinary,
            EntryKind.GenericMethod => BindingEntryKind.SharedGeneric,
            EntryKind.AdjustorThunk or EntryKind.GenericAdjustorThunk => BindingEntryKind.AdjustorThunk,
            EntryKind.Invoker => BindingEntryKind.Invoker,
            _ => BindingEntryKind.Wrapper,
        };
        var definition = MethodRef.Open(context.Method);
        var layouts = GenericWitness.IsGeneric(context.Method)
            ? new GenericWitness(definition, context.Entry.Method!, parts.Types.Layouts) : parts.Types.Layouts;
        var types = GenericWitness.IsGeneric(context.Method) ? new ManagedTypes(context.Facts.Model, layouts, parts.Types.PointerSize) : parts.Types;
        var transformed = StructureRecovery.Run(input, context, parts.Binder, kind, layouts);
        var result = new IntegerLowering(transformed.Function, MethodRef.Open(context.Method), parts.Binder,
            types, context.Facts.Image, parts.Calls, new ManagedCallEffects(parts.Calls), context.Facts.Spec, transformed.Names, parts.Accessors, parts.Constructors,
            witness: context.Entry.Method, rgctx: new MetadataRgctxDecoder(context.Facts)).Run(kind);
        if (result.Failure is { } failure && transformed.Records.FirstOrDefault(r =>
            !r.Removed && r.Address == failure.Position && r.Why is not null) is { Why: { } why })
            return new Missing<ManagedBody>(new("结构", failure.Position, "类型判断", why with { Cause = failure.Reason }));
        if (result.Body is { } candidate)
        {
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

        var failureReason = result.Failure?.Reason;
        if (failureReason is not null)
            foreach (var diagnostic in transformed.Records.Where(r => !r.Removed && r.Address == result.Failure!.Position && r.Reason is not null).Select(r => r.Reason!).Distinct())
                failureReason = Attach(failureReason, diagnostic);
        return result.Body is { } body ? new Completed<ManagedBody>(GenericWitness.IsGeneric(context.Method)
            ? body with { WitnessCoverage = GenericWitnessCoverage.ReferenceOnly } : body)
            : new Missing<ManagedBody>(new(Name, result.Failure!.Position == 0 ? context.Entry.Address : result.Failure.Position,
                result.Failure.Kind.ToString(), failureReason!));
    }
    private static Cpp2CS.Native.Terms.Reason Attach(Cpp2CS.Native.Terms.Reason reason, Cpp2CS.Native.Terms.Reason cause) =>
        reason with { Cause = reason.Cause is null ? cause : Attach(reason.Cause, cause) };
}
