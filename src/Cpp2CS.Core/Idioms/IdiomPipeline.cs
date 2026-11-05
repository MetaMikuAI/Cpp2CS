using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Idioms;

/// <summary>
/// L2 的规则表。规则只在证明成立时改写，改写后清理并继续；一轮没有变化即稳定，规则之间不靠手工重跑传递事实。
/// 表的次序只影响到达不动点的轮数，某条规则依赖另一条的结果时，会在下一轮看到它。
/// </summary>
internal static class IdiomPipeline
{
    private const int Rounds = 16;

    /// <param name="Once">规则每次应用都会新增语句（把检查成功一侧的值改写为一次转换），只能应用一次。</param>
    private sealed record Rule(string Name, Func<IdiomState, bool> Apply, bool Once = false);

    /// <summary>没有返回值的规则只按语句是否变化判断。</summary>
    private static Rule Do(string name, Action<IdiomState> apply) => new(name, state => { apply(state); return false; });

    private static readonly Rule[] Table =
    [
        new("metadata", Metadata),
        new("interface.tails", s => SharedInterfaceTails.Run(s.function, c => c.Op is null && s.owner.HelperOf(c)?.Kind == HelperKind.InterfaceLookup, s.Fresh)),
        new("indirect.tails", s => MergedIndirectTails.Run(s.function)),
        new("interface.dispatch", s => s.InterfaceDispatch()),
        new("interface.invokes", s => SharedInterfaceTails.SplitInvokes(s.function, e => s.defs.Expand(e))),
        Do("calls", s => s.Calls()),
        new("invoker", s => s.InvokerCalls()),
        new("shared.values", s => s.SharedValues()),
        new("stack.boxing", s => s.StackBoxing()),
        new("lazy.metadata", LazyMetadata),
        Do("operands", s => s.RefreshOperands()),
        new("thread.statics", s => s.ThreadStaticBlocks()),
        new("memory.constant", s => ConstantMemoryNormalizer.Run(s.function, s.Fresh)),
        new("math.imports", MathImports),
        new("array.fresh-elements", s => s.FreshArrayElementClasses()),
        new("array.element-checks", s => s.DynamicArrayElementChecks()),
        new("enum.element-classes", s => s.EnumElementClasses()),
        new("unbox.guards", s => s.UnboxGuards()),
        Do("interface.operands", s => s.RefreshInterfaceOperands()),
        new("delegates", s => !s.owner.AuditLegacyDelegateCalls && DelegateCallNormalizer.Run(s.facts, s.function, s.Result)),
        new("managed.throws", s => !s.owner.AuditRawManagedThrows && ManagedThrowNormalizer.Run(s.facts, s.function, s.Result)),
        new("runtime.guards", RuntimeGuards),
        new("class.initialized", ClassInitialized),
        new("once.guards", s => s.OnceGuards()),
        new("conditions.finite", s => FiniteConditions.Simplify(s.function)),
        new("conditions.zero-union", s => s.ZeroUnionConditions()),
        new("checked.references", s => s.CheckedReferenceValues(), Once: true),
        new("checked.types", s => s.SuccessfulTypeCheckValues(), Once: true),
        new("checked.classes", s => CheckedClassValues.Run(s.function, s.RawDefinition, s.Fresh), Once: true),
        new("phi.zero-sources", s => s.ZeroPhiSources()),
        new("phi.equal-addresses", s => s.EqualAddressPhis()),
        new("phi.static-fields", s => s.StaticFieldPhiLoads()),
        new("phi.strings", s => s.StringSlotChoices()),
        new("phi.array-addresses", s => s.ArrayAddressPhis()),
        new("loops.affine", s => AffineInduction.Run(s.function, s.RawDefinition)),
        new("loops.array-pointers", s => s.ArrayPointerLoops()),
        new("exception.stack", s => ExceptionStackValues.Run(s.function) | ExceptionStackValues.SelectedSlots(s.function, s.owner.CallEffects, s.Fresh)),
        Do("readonly.data", s => s.ReadOnlyData()),
        new("phi.address-loads", s => AddressPhiLoads.Run(s.function, s.Fresh)),
        new("phi.class-allocations", s => ClassPhiAllocations.Run(s.function,
            address => s.facts.EntriesAt(address).Any(e => e.Method is { Method: { Name: ".ctor", IsStatic: false, Parameters.Count: 0 } }), s.Fresh)),
        new("allocations.merged", s => MergedAllocationNormalizer.Run(s.function, s.facts)),
        new("select.address-loads", s => SelectedAddressLoads.Run(s.function)),
        new("division.constant", s => ConstantDivisionNormalizer.Run(s.function)),
        new("phi.flags", s => s.FlagPhiConditions()),
    ];

    internal static void Run(this IdiomState state)
    {
        Identify(state);
        state.Cleanup();
        state.Passes.Run("idioms.CountCalls", () => state.CountCalls());
        state.Passes.Run("idioms.TrimResultBuffers", () => state.TrimResultBuffers());
        var changed = new List<string>();
        for (var round = 0; round < Rounds; round++)
        {
            changed.Clear();
            foreach (var rule in Table)
                if ((round == 0 || !rule.Once) && state.Passes.Run($"idioms.{rule.Name}", () => Apply(state, rule)))
                    changed.Add(rule.Name);
            if (changed.Count == 0) break;
        }
        if (changed.Count > 0) state.Reject("idioms.rounds", state.function.Entry, $"规则仍在改写：{string.Join("、", changed)}");
        state.Passes.Run("idioms.Residuals", () => state.Residuals());
    }

    /// <summary>规则的自述只决定是否清理；是否算作改写看语句有没有变化，否则自述不准的规则会让不动点停不下来。</summary>
    private static bool Apply(IdiomState state, Rule rule)
    {
        var before = state.function.Blocks.SelectMany(b => b.Statements).ToArray();
        var reported = rule.Apply(state);
        var after = state.function.Blocks.SelectMany(b => b.Statements).ToArray();
        var changed = before.Length != after.Length || !before.Zip(after).All(p => ReferenceEquals(p.First, p.Second) || p.First.ToString() == p.Second.ToString());
        var reportedErrors = state.Result.Errors.Count;
        if (changed || reported) state.Cleanup();
        if (state.Result.Errors.Count > reportedErrors) state.Result.Errors[reportedErrors] = $"{rule.Name}：{state.Result.Errors[reportedErrors]}";
        return changed;
    }

    /// <summary>函数自身的托管身份与隐藏 MethodInfo 的位置；栈上传入的实参改写为入口值。</summary>
    private static void Identify(IdiomState state)
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
        var signatures = state.facts.EntriesAt(state.function.Entry).Select(e => e.Method).OfType<MethodRef>().Distinct().Select(m => state.owner.abi.Classify(m, out _)).ToArray();
        if (signatures.Length == 0 && state.facts.Unregistered.At(state.function.Entry) is { } stackIdentity)
            signatures = [stackIdentity.Abi];
        if (signatures.All(s => s is not null) && StackInputNormalizer.Run(state.function, state.owner.abi, signatures.Select(s => s!).ToArray(), out var hiddenStack)
            && hiddenStack is { } offset)
            state.selfMethodInfo = Storage.Slot(offset);
    }

    /// <summary>元数据符号与守卫。RGCTX 数组只在其守卫（InitMethodRgctx）归一之后才当作已初始化的值。</summary>
    private static bool Metadata(IdiomState state)
    {
        if (!state.rgctxReady)
        {
            state.rgctxReady = true;
            state.Symbols(rgctx: false);
            if (state.MetadataSlotPhis()) state.Cleanup();
            if (state.StringSlotChoices()) state.Cleanup();
            state.Normalize();
        }
        state.Symbols(rgctx: true);
        state.Normalize();
        return false;
    }

    private static bool LazyMetadata(IdiomState state)
    {
        if (state.lazyValues.Count == 0) return false;
        state.ReplaceLazy();
        state.lazyValues.Clear();
        return true;
    }

    private static bool MathImports(IdiomState state)
    {
        if (!MathImportNormalizer.Run(state.function, state.Fresh)) return false;
        if (state.facts.Options.PromoteFrameSlots && FrameSlotPromotion.Run(state.function) > 0)
            SsaBuilder.Build(state.function, Dominators.Compute(state.function), s => s.Bank == Bank.Stack, state.owner.calls, state.owner.NativeCallees.Convention.StackPointer);
        return true;
    }

    /// <summary>被先前初始化支配的标志位读取折叠为常量，分支由下一轮清除。</summary>
    private static bool ClassInitialized(IdiomState state)
    {
        if (!state.InitializedClassLoads()) return false;
        state.foldedRuntimeGuards = true;
        return true;
    }

    private static bool RuntimeGuards(IdiomState state)
    {
        if (!state.foldedRuntimeGuards) return false;
        state.foldedRuntimeGuards = false;
        state.PruneRuntimeGuards();
        return true;
    }
}
