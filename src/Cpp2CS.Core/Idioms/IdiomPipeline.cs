using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Ssa;
using static Cpp2CS.Idioms.IdiomRewriter;

namespace Cpp2CS.Idioms;

internal static class IdiomPipeline
{
    internal static void Run(this IdiomState state)
    {
        if (state.facts.EntriesAt(state.function.Entry).FirstOrDefault(e => e.Method is not null && e.Kind is EntryKind.Method or EntryKind.GenericMethod) is { Method: { } method })
        {
            state.self = method;
            state.selfMethodInfo = state.owner.abi.Classify(method, out _)?.MethodInfo?.Register;
        }
        else if (state.facts.Unregistered.At(state.function.Entry) is { } identity)
        {
            // 自身只提供定义上下文；入口转传的 MethodInfo 不能实例化为任意一个正见证。
            state.self = new MethodRef(identity.Definition, [], []);
            state.selfMethodInfo = identity.Abi.MethodInfo?.Register;
        }

        var entrySignatures = state.facts.EntriesAt(state.function.Entry).Select(e => e.Method).OfType<MethodRef>().Distinct().Select(m => state.owner.abi.Classify(m, out _)).ToArray();
        if (entrySignatures.Length == 0 && state.facts.Unregistered.At(state.function.Entry) is { } stackIdentity)
            entrySignatures = [stackIdentity.Abi];
        if (entrySignatures.All(s => s is not null) && StackInputNormalizer.Run(state.function, state.owner.abi, entrySignatures.Select(s => s!).ToArray(), out var hiddenStack))
        {
            if (hiddenStack is { } offset)
                state.selfMethodInfo = Storage.Slot(offset);
            state.Cleanup();
        }

        state.Passes.Run("idioms.CountCalls", () =>
        {
            state.CountCalls();
        });
        state.Passes.Run("idioms.TrimResultBuffers", () =>
        {
            state.TrimResultBuffers();
        });
        state.Passes.Run("idioms.Symbols", () =>
        {
            state.Symbols(rgctx: false);
        });
        state.Passes.Run("idioms.MetadataSlotPhis", () =>
        {
            if (state.MetadataSlotPhis())
                state.Cleanup();
        });
        state.Passes.Run("idioms.StringSlotChoices", () =>
        {
            if (state.StringSlotChoices())
                state.Cleanup();
        });
        state.Passes.Run("idioms.Normalize", () =>
        {
            state.Normalize();
        });
        // RGCTX 数组只在其守卫（InitMethodRgctx）归一之后才当作已初始化的值
        state.Passes.Run("idioms.Symbols", () =>
        {
            state.Symbols(rgctx: true);
        });
        state.Passes.Run("idioms.Normalize", () =>
        {
            state.Normalize();
        });
        state.Passes.Run("idioms.MergedIndirectTails.Run", () =>
        {
            if (MergedIndirectTails.Run(state.function))
                state.Cleanup();
        });
        state.Passes.Run("idioms.FrameSlotPromotion.ForwardCallSpills", () =>
        {
            if (FrameSlotPromotion.ForwardCallSpills(state.function, c => c.Op is null && state.owner.HelperOf(c)?.Kind == HelperKind.InterfaceLookup))
                state.Cleanup();
        });
        state.Passes.Run("idioms.SharedInterfaceTails.Run", () =>
        {
            if (SharedInterfaceTails.Run(state.function, c => c.Op is null && state.owner.HelperOf(c)?.Kind == HelperKind.InterfaceLookup, state.Fresh))
                state.Cleanup();
        });
        state.Passes.Run("idioms.InterfaceDispatch", () =>
        {
            if (state.InterfaceDispatch())
                state.Cleanup();
        });
        state.Passes.Run("idioms.SharedInterfaceTails.SplitInvokes", () =>
        {
            if (SharedInterfaceTails.SplitInvokes(state.function, e => state.defs.Expand(e)))
                state.Cleanup();
        });
        state.Passes.Run("idioms.Calls", () =>
        {
            state.Calls();
        });
        // 延迟值替换后才出现的 MethodInfo 符号（如内联 Array.Empty<T>() 的 MethodInfo+0x38 → RGCTX）：再符号化一次。
        state.Passes.Run("idioms.ReplaceLazy", () =>
        {
            if (state.lazyValues.Count > 0)
            {
                state.ReplaceLazy();
                state.Symbols(rgctx: true);
            }
        });
        state.Passes.Run("idioms.RefreshOperands", () =>
        {
            state.RefreshOperands();
        });
        state.Passes.Run("idioms.ThreadStaticBlocks", () =>
        {
            if (state.ThreadStaticBlocks())
                state.Cleanup();
        });
        state.Passes.Run("idioms.FrameMemoryNormalizer.Run", () =>
        {
            if (FrameMemoryNormalizer.Run(state.function, state.Fresh))
                state.Cleanup();
        });
        state.Passes.Run("idioms.MathImportNormalizer.Run", () =>
        {
            if (MathImportNormalizer.Run(state.function, state.Fresh))
            {
                if (state.facts.Options.PromoteFrameSlots && FrameSlotPromotion.Run(state.function) > 0)
                    SsaBuilder.Build(state.function, Dominators.Compute(state.function), s => s.Bank == Bank.Stack, state.owner.calls, state.owner.NativeCallees.Convention.StackPointer);
                state.Cleanup();
            }
        });
        state.Passes.Run("idioms.FrameAddressTails", () =>
        {
            if (state.function.Range.ExceptionRegions.Length == 0 && TailDuplication.Run(state.function,
                b => b.Statements.OfType<Phi>().Any(p => p.Sources.All(v => state.defs.Expand(new Use(v, 64)) is FrameAddress { Offset: < 0 }))))
                state.Cleanup();
        });
        state.Passes.Run("idioms.ClassTails", () =>
        {
            if (state.function.Range.ExceptionRegions.Length != 0) return;
            for (var round = 0; round < 8 && TailDuplication.Run(state.function,
                b => b.Statements.OfType<Phi>().Any(p => p.Sources.All(v => state.defs.Expand(new Use(v, 64)) is Symbol { Kind: SymbolKind.Class }))); round++)
            {
                state.Cleanup();
                state.RefreshOperands();
            }
        });
        state.Passes.Run("idioms.FreshArrayElementClasses", () =>
        {
            if (state.FreshArrayElementClasses())
                state.Cleanup();
        });
        state.Passes.Run("idioms.DynamicArrayElementChecks", () =>
        {
            if (state.DynamicArrayElementChecks())
                state.Cleanup();
        });
        state.Passes.Run("idioms.EnumElementClasses", () =>
        {
            if (state.EnumElementClasses())
                state.Cleanup();
        });
        state.Passes.Run("idioms.UnboxGuards", () =>
        {
            if (state.UnboxGuards())
                state.Cleanup();
        });
        state.Passes.Run("idioms.RefreshInterfaceOperands", () =>
        {
            state.RefreshInterfaceOperands();
        });
        state.Passes.Run("idioms.DelegateCallNormalizer.Run", () =>
        {
            if (!state.owner.AuditLegacyDelegateCalls && DelegateCallNormalizer.Run(state.facts, state.function, state.Result))
                state.Cleanup();
        });
        state.Passes.Run("idioms.ManagedThrowNormalizer.Run", () =>
        {
            if (!state.owner.AuditRawManagedThrows && ManagedThrowNormalizer.Run(state.facts, state.function, state.Result))
                state.Cleanup();
        });
        state.Passes.Run("idioms.PruneRuntimeGuards", () =>
        {
            if (state.foldedRuntimeGuards)
                state.PruneRuntimeGuards();
        });
        state.Passes.Run("idioms.InitializedClassLoads", () =>
        {
            while (state.InitializedClassLoads())
            {
                state.Cleanup();
                state.PruneRuntimeGuards();
                state.Symbols(rgctx: true);
            }
        });
        state.Passes.Run("idioms.SplitClassGuards", () =>
        {
            if (state.SplitClassGuards())
                state.Cleanup();
        });
        state.Passes.Run("idioms.FiniteConditions.Simplify", () =>
        {
            while (FiniteConditions.Simplify(state.function))
                state.Cleanup();
        });
        state.Passes.Run("idioms.ZeroUnionConditions", () =>
        {
            if (state.ZeroUnionConditions())
                state.Cleanup();
        });
        state.Passes.Run("idioms.CheckedReferenceValues", () =>
        {
            if (state.CheckedReferenceValues())
                state.Cleanup();
        });
        state.Passes.Run("idioms.SuccessfulTypeCheckValues", () =>
        {
            if (state.SuccessfulTypeCheckValues())
                state.Cleanup();
        });
        state.Passes.Run("idioms.CheckedClassValues.Run", () =>
        {
            if (CheckedClassValues.Run(state.function, state.RawDefinition, state.Fresh))
                state.Cleanup();
        });
        state.Passes.Run("idioms.ZeroPhiSources", () =>
        {
            if (state.ZeroPhiSources())
                state.Cleanup();
        });
        state.Passes.Run("idioms.EqualAddressPhis", () =>
        {
            if (state.EqualAddressPhis())
                state.Cleanup();
        });
        state.Passes.Run("idioms.StaticFieldPhiLoads", () =>
        {
            if (state.StaticFieldPhiLoads())
                state.Cleanup();
        });
        state.Passes.Run("idioms.StringSlotChoices", () =>
        {
            if (state.StringSlotChoices())
                state.Cleanup();
        });
        state.Passes.Run("idioms.ArrayAddressPhis", () =>
        {
            if (state.ArrayAddressPhis())
                state.Cleanup();
        });
        state.Passes.Run("idioms.ArrayPointerLoops", () =>
        {
            if (state.ArrayPointerLoops())
                state.Cleanup();
        });
        state.Passes.Run("idioms.ExceptionStackValues.Run", () =>
        {
            if (ExceptionStackValues.Run(state.function))
                state.Cleanup();
        });
        state.Passes.Run("idioms.ReadOnlyData", () =>
        {
            state.ReadOnlyData();
        });
        state.Passes.Run("idioms.AddressPhiLoads.Run", () =>
        {
            while (AddressPhiLoads.Run(state.function, state.Fresh))
            {
                state.Cleanup();
                state.Symbols(rgctx: true);
                if (state.StringSlotChoices())
                    state.Cleanup();
                state.ReadOnlyData();
            }
        });
        state.Passes.Run("idioms.ClassPhiAllocations.Run", () =>
        {
            if (ClassPhiAllocations.Run(state.function, address => state.facts.EntriesAt(address).Any(e => e.Method is { Method: { Name: ".ctor", IsStatic: false, Parameters.Count: 0 } }), state.Fresh))
                state.Cleanup();
        });
        state.Passes.Run("idioms.MergedAllocationNormalizer.Run", () =>
        {
            if (MergedAllocationNormalizer.Run(state.function, state.facts))
                state.Cleanup();
        });
        state.Passes.Run("idioms.SelectedAddressLoads.Run", () =>
        {
            for (var round = 0; round < 8 && SelectedAddressLoads.Run(state.function); round++)
            {
                state.Cleanup();
                state.Symbols(rgctx: true);
                state.ReadOnlyData();
            }
        });
        state.Passes.Run("idioms.ConstantDivisionNormalizer.Run", () =>
        {
            if (ConstantDivisionNormalizer.Run(state.function))
                state.Cleanup();
        });
        state.Passes.Run("idioms.FlagPhiConditions", () =>
        {
            if (state.FlagPhiConditions())
                state.Cleanup();
        });
        // 后续守卫归约可能才把对象和类指针的入边对齐。
        state.Passes.Run("idioms.refresh", () =>
        {
            state.defs = new Defs(state.function);
        });
        state.Passes.Run("idioms.Calls", () =>
        {
            state.Calls(indirectOnly: true);
        });
        state.Passes.Run("idioms.Residuals", () =>
        {
            state.Residuals();
        });
    }
}
