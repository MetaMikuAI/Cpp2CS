using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;
using Cpp2CS.Ssa;

namespace Cpp2CS.Idioms;

/// <summary>L2 模板。每个模板命中一次计一次（见 <see cref="IdiomResult.Hits"/>）。</summary>
public enum Template
{
    /// <summary>读取元数据槽位 → Symbol。</summary>
    MetadataSlot,
    /// <summary>读取 Il2CppClass.static_fields → Symbol(StaticFields)。</summary>
    StaticFields,
    /// <summary>读取 MethodInfo.klass → Symbol(Class)。</summary>
    MethodClass,
    /// <summary>读取 MethodInfo.rgctx_data / Il2CppClass.rgctx_data → Symbol(Rgctx)。</summary>
    RgctxData,
    /// <summary>读取 RGCTX 数组第 i 项 → 表中条目（Class/Type/Method/Constrained）。</summary>
    RgctxEntry,
    /// <summary>方法级 s_Il2CppMethodInitialized 守卫及其中的 InitMetadata 调用：整体删除。</summary>
    MetadataInitGuard,
    /// <summary>cctor_finished_or_no_cctor 守卫 + il2cpp_runtime_class_init → RunClassConstructor。</summary>
    ClassConstructorGuard,
    /// <summary>initialized_and_no_error 位守卫 + InitializedTypeInfo → InitClass。</summary>
    InitClassGuard,
    /// <summary>MethodInfo.rgctx_data 为空守卫 + InitMethodRgctx → InitMethodRgctx。</summary>
    MethodRgctxGuard,
    /// <summary>条件分支到只抛异常的块 → NullCheck / BoundsCheck / ThrowIf。</summary>
    NullCheck, BoundsCheck, ThrowIf,
    /// <summary>内联的接口偏移扫描 + 慢路径查找 → InterfaceInvokeData。</summary>
    InterfaceDispatch,
    /// <summary>typeHierarchyDepth 比较 + typeHierarchy[depth-1] 比较 → TypeCheck。</summary>
    InlineTypeCheck,
    VirtualCall, InterfaceCall, DelegateCall, MethodPointerCall,
    /// <summary>MethodInfo.slot 读取 → 元数据中的槽位常量。</summary>
    MethodSlot,
    /// <summary>vtable[slot].method + 泛型方法实例 → 运行时解析泛型虚方法；之后经其 virtualMethodPointer 调用。</summary>
    GenericVirtualCall,
    /// <summary>直接调用已识别的运行时 helper → 对应操作。</summary>
    HelperCall,
    /// <summary>写屏障与其前紧邻的同一引用写入配对。</summary>
    WriteBarrier,
    /// <summary>守卫之外的 InitMetadata(槽位)：结果即槽位的值 → Symbol。</summary>
    LazyMetadataInit,
    /// <summary>PLT 导入调用。</summary>
    ImportCall,
    /// <summary>同一个 wrapper 分配、写入与抛出的完整配对。</summary>
    ManagedThrow,
}

/// <summary>模板没有消化的运行时痕迹：Category 用于汇总，Detail 是样例说明。</summary>
public readonly record struct Residual(ulong Address, string Category, string Detail);

/// <summary>
/// 一个模板实例的机器级描述，供 tests/oracle/template_oracle.py 在 Unicorn 中执行原指令验证：
/// Head 为起始块地址；Exits 为出口块地址；Inputs 为输入的位置（槽位地址、起始时所在寄存器）与参数。
/// </summary>
public sealed record TemplateInstance(Template Template, ulong Function, ulong Head, IReadOnlyDictionary<string, ulong> Exits, IReadOnlyDictionary<string, object> Inputs);

public sealed class IdiomResult
{
    public List<TemplateInstance> Instances { get; } = [];
    public Dictionary<Template, int> Hits { get; } = new();
    public List<Residual> Residuals { get; } = [];
    public List<string> Errors { get; } = [];
    /// <summary>本函数守卫中初始化的槽位、读取的槽位、守卫字节地址。</summary>
    public HashSet<ulong> InitializedSlots { get; } = [];
    public HashSet<ulong> ReadSlots { get; } = [];
    public HashSet<ulong> Guards => [.. GuardSlots.Keys];
    /// <summary>守卫字节 → 它的区域初始化的槽位（升序）。</summary>
    public Dictionary<ulong, ulong[]> GuardSlots { get; } = new();
    /// <summary>已证明为元数据初始化守卫的条件分支位置，供原生同形核对使用。</summary>
    public HashSet<ulong> MetadataGuardBranches { get; } = [];
    /// <summary>改写之前，对各类 helper 的调用点数与间接调用数。</summary>
    public Dictionary<HelperKind, int> HelperCalls { get; } = new();
    public int IndirectCalls { get; set; }

    public void Hit(Template template) => Hits[template] = Hits.GetValueOrDefault(template) + 1;
}

/// <summary>
/// L2 惯用法归一：在寄存器 SSA 上把 IL2CPP 生成代码的固定形态替换为带语义的 <see cref="RuntimeOp"/>。
/// 每个模板都检查完整形态（守卫条件按代入常量后的分支方向判定，区域内只允许模板规定的语句），
/// 不符合就不改动，留作 <see cref="Residual"/>。改动控制流之后重新传播并校验 SSA。
/// </summary>
public sealed class IdiomRewriter(ProgramFacts facts)
{
    private readonly ProgramFacts facts = facts;
    private readonly ImageSection[] guardSections = facts.Model.Image.Sections
        .Where(s => (s.Flags & 1) != 0 && !s.Executable && s.Name != ".got").ToArray();
    private readonly ManagedAbi abi = new(facts.Layouts);
    private readonly Lifting.FactsCallModel calls = new(facts, new Arm64Machine(facts.Code).Convention);
    private readonly Lifting.FunctionLifter inputLifter = new(facts);
    private readonly Dictionary<ulong, HashSet<Storage>?> nativeInputs = new();
    private readonly Dictionary<ulong, bool> unusedResultBuffers = new();

    private bool UnusedResultBuffer(ulong entry)
    {
        if (!unusedResultBuffers.TryGetValue(entry, out var unused))
        {
            var convention = inputLifter.Machine.Convention;
            // 未知签名保留全部可能的返回寄存器，x8 只承担间接返回地址，不是托管参数寄存器。
            var returned = convention.IntegerResults.Concat(convention.FloatResults)
                .Select(r => (Expr)new Read(r, r.Bank == Bank.Vec ? 128 : 64)).ToArray();
            var reads = Lifting.NativeInputs.Reads(inputLifter.Lift(entry, new Intrinsic("return", returned, 64), simplify: false));
            unused = convention.IndirectResult is { } buffer && reads is not null && !reads.Contains(buffer);
            unusedResultBuffers.Add(entry, unused);
        }
        return unused;
    }

    internal bool UnusedInput(ulong entry, Storage register)
    {
        if (!nativeInputs.TryGetValue(entry, out var reads))
        {
            // 递归调用暂不证明未用；后续只缓存完整分析的结果。
            nativeInputs.Add(entry, null);
            var methods = facts.EntriesAt(entry).Select(e => e.Method).OfType<MethodRef>().ToArray();
            reads = null;
            if (methods.Length > 0 && methods.All(m => !m.Method.IsVirtual && (m.Method.Address == entry || m.Method.Address == 0)
                && !m.TypeArguments.Concat(m.MethodArguments).Any(FieldLayouts.IsFullyShared)))
            {
                var signatures = methods.Select(m => abi.Classify(m, out _)).ToArray();
                if (signatures.All(s => s is not null))
                {
                    // 同地址的多个所有者取返回寄存器并集，不能把另一签名的返回输入误判为未用。
                    var returned = signatures.SelectMany(s => s!.Return?.Pieces ?? []).Distinct()
                        .Select(p => (Expr)new Read(p.Register, p.Width)).ToArray();
                    reads = Lifting.NativeInputs.Reads(inputLifter.Lift(entry,
                        returned.Length == 0 ? null : new Intrinsic("return", returned, 64), simplify: false),
                        RecoverUnusedInputs ? (call, input) => call is { Op: null, Kind: CallKind.Direct or CallKind.Tail, Target: Const target }
                            && UnusedInput(target.Value, input) : null);
                }
            }
            nativeInputs[entry] = reads;
        }
        return reads is not null && !reads.Contains(register);
    }

    /// <summary>为哪些函数（按入口）记录模板实例；null 为全部。记录要逐个寄存器回溯取值，普查全程序时按函数抽样。</summary>
    public Func<ulong, bool>? RecordFilter { get; set; }
    /// <summary>只读普查中的宽泛委托偏移标签；恢复器使用默认的严格归一。</summary>
    public bool AuditLegacyDelegateCalls { get; init; }
    /// <summary>仅供全程序普查保留 allocate/store/throw 的原始配对证据。</summary>
    public bool AuditRawManagedThrows { get; init; }
    /// <summary>恢复托管调用时清理未用输入的残值；事实推断仍保留原始调用参数。</summary>
    public bool RecoverUnusedInputs { get; init; }

    public IdiomResult Run(MachineFunction function)
    {
        var context = new Context(this, function);
        context.Run();
        return context.Result;
    }

    /// <summary>调用目标是运行时 helper（不含托管区域中没有注册表所有者的生成函数，它们按托管调用处理）。</summary>
    private RuntimeHelper? HelperOf(Call call) =>
        call is { Kind: CallKind.Direct or CallKind.Tail, Target: Const target } && facts.Helpers.At(target.Value) is { } helper
            && facts.Code.RegionOf(target.Value) != CodeRegion.Managed ? helper : null;

    private sealed class Context(IdiomRewriter owner, MachineFunction function)
    {
        private readonly ProgramFacts facts = owner.facts;
        private readonly HashSet<Block> removed = [];
        private readonly Dictionary<Variable, object> interfaceData = new();
        /// <summary>泛型虚方法解析结果（MethodInfo*）→ 方法。</summary>
        private readonly Dictionary<Variable, MethodRef> genericVirtual = new();
        /// <summary>守卫之外的 InitMetadata 调用及其结果代表的符号；Calls 之后替换为定义（或删除）。</summary>
        private readonly List<(Call Call, Symbol Value)> lazyValues = [];
        /// <summary>由槽位读取得到的符号 → 槽位地址（模板实例的输入位置）。</summary>
        private readonly Dictionary<Symbol, ulong> symbolSlots = new();
        private int nextTemp = -1;
        private Defs defs = new(function);
        private readonly bool recording = owner.RecordFilter?.Invoke(function.Entry) ?? true;
        /// <summary>函数自身的托管所有者与其 MethodInfo* 入口位置（共享泛型代码由此取自身的 RGCTX）。</summary>
        private MethodRef? self;
        private Storage? selfMethodInfo;
        private bool foldedRuntimeGuards;

        public IdiomResult Result { get; } = new();

        public void Run()
        {
            if (facts.EntriesAt(function.Entry).FirstOrDefault(e => e.Method is not null && e.Kind is EntryKind.Method or EntryKind.GenericMethod) is { Method: { } method })
            {
                self = method;
                selfMethodInfo = owner.abi.Classify(method, out _)?.MethodInfo?.Register;
            }
            else if (facts.Unregistered.At(function.Entry) is { } identity)
            {
                // 自身只提供定义上下文；入口转传的 MethodInfo 不能实例化为任意一个正见证。
                self = new MethodRef(identity.Definition, [], []);
                selfMethodInfo = identity.Abi.MethodInfo?.Register;
            }
            var entrySignatures = facts.EntriesAt(function.Entry).Select(e => e.Method).OfType<MethodRef>().Distinct()
                .Select(m => owner.abi.Classify(m, out _)).ToArray();
            if (entrySignatures.Length == 0 && facts.Unregistered.At(function.Entry) is { } stackIdentity) entrySignatures = [stackIdentity.Abi];
            if (entrySignatures.All(s => s is not null)
                && StackInputNormalizer.Run(function, owner.abi, entrySignatures.Select(s => s!).ToArray(), out var hiddenStack))
            {
                if (hiddenStack is { } offset) selfMethodInfo = Storage.Slot(offset);
                Cleanup();
            }
            CountCalls();
            TrimResultBuffers();
            Symbols(rgctx: false);
            if (MetadataSlotPhis()) Cleanup();
            if (StringSlotChoices()) Cleanup();
            Normalize();
            // RGCTX 数组只在其守卫（InitMethodRgctx）归一之后才当作已初始化的值
            Symbols(rgctx: true);
            Normalize();
            if (SharedInterfaceTails.Run(function, c => c.Op is null && owner.HelperOf(c)?.Kind == HelperKind.InterfaceLookup, Fresh)) Cleanup();
            if (InterfaceDispatch()) Cleanup();
            if (SharedInterfaceTails.SplitInvokes(function, e => defs.Expand(e), Fresh)) Cleanup();
            Calls();
            // 延迟值替换后才出现的 MethodInfo 符号（如内联 Array.Empty<T>() 的 MethodInfo+0x38 → RGCTX）：再符号化一次。
            if (lazyValues.Count > 0)
            {
                ReplaceLazy();
                Symbols(rgctx: true);
            }
            RefreshOperands();
            if (ThreadStaticBlocks()) Cleanup();
            if (FrameMemoryNormalizer.Run(function, Fresh)) Cleanup();
            if (FreshArrayElementClasses()) Cleanup();
            if (DynamicArrayElementChecks()) Cleanup();
            if (EnumElementClasses()) Cleanup();
            if (UnboxGuards()) Cleanup();
            RefreshInterfaceOperands();
            if (!owner.AuditLegacyDelegateCalls && DelegateCallNormalizer.Run(facts, function, Result)) Cleanup();
            if (!owner.AuditRawManagedThrows && ManagedThrowNormalizer.Run(facts, function, Result)) Cleanup();
            if (foldedRuntimeGuards) PruneRuntimeGuards();
            while (InitializedClassLoads())
            {
                Cleanup();
                PruneRuntimeGuards();
                Symbols(rgctx: true);
            }
            if (SplitClassGuards()) Cleanup();
            while (FiniteConditions.Simplify(function)) Cleanup();
            if (CheckedReferenceValues()) Cleanup();
            if (SuccessfulTypeCheckValues()) Cleanup();
            if (ZeroPhiSources()) Cleanup();
            if (EqualAddressPhis()) Cleanup();
            if (StaticFieldPhiLoads()) Cleanup();
            if (StringSlotChoices()) Cleanup();
            if (ArrayAddressPhis()) Cleanup();
            if (ArrayPointerLoops()) Cleanup();
            if (ExceptionStackValues.Run(function)) Cleanup();
            if (ReadOnlyDataNormalizer.Run(function, facts.Model.Image, address => facts.Usages.At(address)?.Usage.Kind
                is UsageKind.StringLiteral or UsageKind.MethodDef or UsageKind.MethodRef))
            {
                Cleanup();
                if (MetadataSlotPhis()) Cleanup();
                if (StringSlotChoices()) Cleanup();
            }
            if (AddressPhiLoads.Run(function, Fresh))
            {
                Cleanup();
                Symbols(rgctx: true);
            }
            if (ClassPhiAllocations.Run(function, address => facts.EntriesAt(address)
                .Any(e => e.Method is { Method: { Name: ".ctor", IsStatic: false, Parameters.Count: 0 } }), Fresh)) Cleanup();
            if (MergedAllocationNormalizer.Run(function, facts)) Cleanup();
            if (FlagPhiConditions()) Cleanup();
            Residuals();
        }

        /// <summary>守卫与检查归一到不动点：一个守卫删除之后汇合处的 φ 变平凡，依赖它的下一个守卫才能判定。</summary>
        private void Normalize()
        {
            for (var round = 0; round < 32; round++)
            {
                defs = new Defs(function);
                if (owner.RecoverUnusedInputs) DiscardUnusedInputs();
                // 类型检查先于抛异常检查：castclass / as 后判空的失败一侧是只抛异常的块
                var changed = SplitMetadataGuards();
                changed |= Guards();
                changed |= RetainMetadataPath();
                changed |= TypeChecks();
                changed |= Checks();
                changed |= CheckedTypeChains();
                if (!changed) return;
                Cleanup();
            }
        }

        private void Cleanup()
        {
            Result.Errors.AddRange(Lowering.Cleanup(function));
            removed.Clear();
            defs = new Defs(function);
        }

        private IEnumerable<Stmt> All => function.Blocks.Where(b => !removed.Contains(b)).SelectMany(b => b.Statements);

        private bool ArrayAddressPhis()
        {
            var allocations = All.OfType<Call>().Where(c => c.Op is { Kind: OpKind.NewArray, Operand: ArrayRef { IsVector: true } a }
                && ManagedTypes.IsReferenceType(a.Element) && c.Defines.FirstOrDefault() is not null).ToDictionary(c => c.Defines[0], c => c.Op!.Operand);
            Expr MathValue(Expr expression, int depth = 0) => depth > 12 ? expression : ExprMap.Map(expression,
                e => e is Use use && RawDefinition(use) is (Binary or Ir.Convert) and var value ? MathValue(value, depth + 1) : null);
            Expr? Index(Expr offset) => MathValue(offset) switch
            {
                Const { Value: 0 } => Expr.C(0, 64),
                Binary { Op: BinOp.Shl, Right: Const { Value: 3 }, Left: var value } => value,
                Binary { Op: BinOp.AShr, Right: Const { Value: 29 }, Left: Binary { Op: BinOp.Shl, Left: var value, Right: Const { Value: 32 } } }
                    => Fold.Convert(ConvKind.SignExtend, Fold.Convert(ConvKind.Truncate, value, 32), 64),
                _ => null,
            };
            var changed = false;
            foreach (var block in function.Blocks)
            foreach (var pointer in block.Statements.OfType<Phi>().ToArray())
            {
                if (block.Predecessors.Any(p => p.NormalSuccessors.Count() != 1) || !block.Statements.Contains(pointer)) continue;
                foreach (var basis in block.Statements.OfType<Phi>().Where(p => p != pointer).ToArray())
                {
                    if (basis.Sources.Length != pointer.Sources.Length || !basis.Sources.All(allocations.ContainsKey)
                        || basis.Sources.Select(v => allocations[v]).Distinct().Count() != 1) continue;
                    var indices = new List<Expr>();
                    for (var i = 0; i < pointer.Sources.Length; i++)
                    {
                        if (pointer.Sources[i] == basis.Sources[i]) { indices.Add(Expr.C(0, 64)); continue; }
                        if (RawDefinition(new Use(pointer.Sources[i], 64)) is not Binary { Op: BinOp.Add, Left: Use root, Right: var offset }
                            || root.Variable != basis.Sources[i] || Index(offset) is not { } index) break;
                        indices.Add(index);
                    }
                    if (indices.Count != pointer.Sources.Length) continue;
                    var sources = indices.Select(_ => Fresh()).ToArray();
                    for (var i = 0; i < indices.Count; i++)
                    {
                        var pred = block.Predecessors[i];
                        pred.Statements.Insert(pred.Statements.Count - (pred.Statements.LastOrDefault() is Jump ? 1 : 0), new Define(pointer.Address, sources[i], indices[i]));
                    }
                    var selected = Fresh();
                    block.Statements.Remove(pointer);
                    block.Statements.Insert(0, new Phi(pointer.Address, selected, sources));
                    block.Statements.Insert(block.Statements.TakeWhile(s => s is Phi).Count(), new Define(pointer.Address, pointer.Target,
                        new Binary(BinOp.Add, new Use(basis.Target, 64), new Binary(BinOp.Shl, new Use(selected, 64), Expr.C(3, 64), 64), 64)));
                    changed = true;
                    break;
                }
            }
            return changed;
        }

        // 指针和下标同步递增的数组循环：pointer += 8 与 index++ 保持同一元素位置。
        private bool ArrayPointerLoops()
        {
            var arrays = All.OfType<Call>().Where(c => c.Op is { Kind: OpKind.NewArray, Operand: ArrayRef { IsVector: true } a }
                && ManagedTypes.IsReferenceType(a.Element) && c.Defines.FirstOrDefault() is not null).Select(c => c.Defines[0]).ToHashSet();
            Use Root(Use value)
            {
                var seen = new HashSet<Variable>();
                while (seen.Add(value.Variable) && RawDefinition(value) is Use copy) value = copy;
                return value;
            }
            var changed = false;
            foreach (var block in function.Blocks)
            foreach (var pointer in block.Statements.OfType<Phi>().Where(p => p.Sources.Length == 2).ToArray())
            {
                for (var seed = 0; seed < 2; seed++)
                {
                    if (RawDefinition(new Use(pointer.Sources[seed], 64)) is not Binary { Op: BinOp.Add, Left: Use array, Right: Const { Value: 32 } }
                        || !arrays.Contains(Root(array).Variable)
                        || RawDefinition(new Use(pointer.Sources[1 - seed], 64)) is not Binary { Op: BinOp.Add, Left: Use previous, Right: Const { Value: 8 } }
                        || previous.Variable != pointer.Target) continue;
                    var index = block.Statements.OfType<Phi>().FirstOrDefault(p => p.Sources.Length == 2
                        && RawDefinition(new Use(p.Sources[seed], 64)) is Const { Value: 0 }
                        && RawDefinition(new Use(p.Sources[1 - seed], 64)) is Binary { Op: BinOp.Add, Left: Use prior, Right: Const { Value: 1 }, Width: 64 }
                        && prior.Variable == p.Target);
                    if (index is null) continue;
                    block.Statements.Remove(pointer);
                    var address = new Binary(BinOp.Add, new Binary(BinOp.Add, array, Expr.C(32, 64), 64),
                        new Binary(BinOp.Shl, new Use(index.Target, 64), Expr.C(3, 64), 64), 64);
                    foreach (var current in function.Blocks)
                        for (var i = 0; i < current.Statements.Count; i++)
                            current.Statements[i] = ExprMap.MapOperands(current.Statements[i], e => ExprMap.Map(e,
                                part => part is Use use && use.Variable == pointer.Target ? address : null));
                    changed = true;
                    break;
                }
            }
            return changed;
        }

        private bool SplitClassGuards()
        {
            var changed = false;
            foreach (var head in function.Blocks)
            {
                if (head.Statements.LastOrDefault() is not Branch guard || head.NormalSuccessors.ToArray() is not [var first, var second]) continue;
                var condition = defs.Expand(guard.Condition);
                if (TopLoads(condition).Distinct().ToArray() is not [Load { Width: 32,
                    Address: Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Class, Value: TypeRef type },
                        Right: Const { Value: RuntimeLayout.ClassCctorFinishedOrNoCctor } } } load]) continue;
                var side = Direction(condition, Replace(load, 0));
                if (side is not (0 or 1) || Direction(condition, Replace(load, 1)) != 1 - side) continue;
                var init = side == 0 ? first : second;
                var skip = side == 0 ? second : first;
                if (init.Predecessors.Count != 1 || init.Statements.LastOrDefault() is not Branch after
                    || skip.Statements.LastOrDefault() is not Branch normal || skip.Statements.Any(s => s is not (Define or Nop or Branch))) continue;
                var prefix = init.Statements.SkipLast(1).Where(s => s is not Nop).ToArray();
                if (prefix is not [Call { Op.Kind: OpKind.RunClassConstructor } call] || !Equals(call.Op.Operand, type)) continue;
                var a = defs.Expand(after.Condition);
                var b = defs.Expand(normal.Condition);
                if (!(a == b && after.Target == normal.Target && after.Fallthrough == normal.Fallthrough)
                    && !(a == Fold.Simplify(new Not(b)) && after.Target == normal.Fallthrough && after.Fallthrough == normal.Target)) continue;
                // RunClassConstructor 自身处理已初始化状态；保留初始化臂及其后续业务分支。
                head.Statements[^1] = new Jump(guard.Address, init.Start);
                MachineFunction.RemoveEdgeAt(head, 1 - side.Value);
                changed = true;
            }
            return changed;
        }

        private bool FlagPhiConditions()
        {
            var changed = false;
            foreach (var block in function.Blocks)
                foreach (var phi in block.Statements.OfType<Phi>().Where(p => p.Target.Storage.Bank == Bank.Flags).ToArray())
                {
                    var tests = All.SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).OfType<TestFlags>()
                        .Where(t => t.FlagsValue is Use u && u.Variable == phi.Target).Distinct().ToArray();
                    foreach (var test in tests)
                    {
                        var conditions = phi.Sources.Select(v => Fold.TestFlags(defs.Expand(new Use(v, 0)), test.Code)).ToArray();
                        if (conditions.Any(c => ExprMap.Walk(c).Any(e => e is TestFlags or Flags or ConditionalFlags or Unknown or Load))) continue;
                        var result = Fresh();
                        var inputs = conditions.Select(_ => Fresh()).ToArray();
                        for (var p = 0; p < inputs.Length; p++)
                        {
                            var pred = block.Predecessors[p];
                            var index = pred.Statements.Count - (pred.Statements.LastOrDefault() is Jump or Branch ? 1 : 0);
                            pred.Statements.Insert(index, new Define(phi.Address, inputs[p], conditions[p]));
                        }
                        block.Statements.Insert(0, new Phi(phi.Address, result, inputs));
                        foreach (var current in function.Blocks)
                            for (var i = 0; i < current.Statements.Count; i++)
                                current.Statements[i] = ExprMap.MapOperands(current.Statements[i], e => ExprMap.Map(e, x => x.Equals(test) ? new Use(result, 1) : null));
                        changed = true;
                    }
                }
            return changed;
        }

        private bool SuccessfulTypeCheckValues()
        {
            var dominators = Dominators.Compute(function);
            var checks = All.OfType<Call>().Where(c => c.Op?.Kind == OpKind.TypeCheck).ToArray();
            var changed = false;
            foreach (var check in checks)
            {
                if (check.Op?.Operand is not TypeRef type || check.Arguments is not [Use klass]
                    || RawDefinition(klass) is not Load { Width: 64, Address: Use obj } || check.Defines.FirstOrDefault() is not { } flag) continue;
                foreach (var block in function.Blocks)
                {
                    var at = block.Statements.FindIndex(s => s is Call { Op.Kind: OpKind.ThrowIf, Op.Operand: "System.InvalidCastException",
                        Arguments: [Compare { Cond: Cond.Eq, Left: Use result, Right: Const { Value: 0 } }] } && result.Variable == flag);
                    Block? start = at >= 0 ? block : null;
                    var position = at + 1;
                    if (start is null && block.Statements.LastOrDefault() is Branch
                        { Condition: Compare { Cond: Cond.Eq or Cond.Ne, Left: Use result, Right: Const { Value: 0 } } test } branch && result.Variable == flag)
                    {
                        var address = test.Cond == Cond.Eq ? branch.Fallthrough : branch.Target;
                        start = block.NormalSuccessors.FirstOrDefault(b => b.Start == address && b.Predecessors.Count == 1);
                        position = start?.Statements.TakeWhile(s => s is Phi).Count() ?? 0;
                    }
                    if (start is null) continue;
                    var cast = Fresh();
                    RefineReferenceUses(start, position, obj, cast, dominators);
                    start.Statements.Insert(position, new Call(check.Address, CallKind.Direct, Expr.C(0, 64))
                    {
                        Op = new RuntimeOp(OpKind.IsInst, type), Arguments = [obj], Results = [cast.Storage], Defines = [cast],
                    });
                    changed = true;
                    break;
                }
            }
            return changed;
        }

        private void RefineReferenceUses(Block start, int position, Use obj, Variable cast, Dominators dominators)
        {
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is Phi phi)
                    {
                        var sources = phi.Sources.Select((source, at) => source == obj.Variable
                            && dominators.Dominates(start.Index, block.Predecessors[at].Index) ? cast : source).ToArray();
                        block.Statements[i] = phi with { Sources = sources };
                    }
                    else if (dominators.Dominates(start.Index, block.Index) && (block != start || i >= position))
                        block.Statements[i] = ExprMap.MapOperands(block.Statements[i], e => ExprMap.Map(e,
                            part => part is Use use && use.Variable == obj.Variable ? new Use(cast, use.Width) : null));
                }
        }

        // null 与通过 castclass 检查的路径汇合后，值具有目标引用类型；后续 phi 也必须保留这个类型。
        private bool CheckedReferenceValues()
        {
            var dominators = Dominators.Compute(function);
            var changed = false;
            foreach (var join in function.Blocks.Where(b => b.Predecessors.Count == 2))
            foreach (var check in join.Predecessors)
            {
                if (check.Statements.LastOrDefault() is not Jump to || to.Target != join.Start) continue;
                var path = new List<Block> { check };
                var first = check;
                while (first.Predecessors is [var parent] && parent.Statements.LastOrDefault() is Jump next
                    && next.Target == first.Start && !path.Contains(parent)) { path.Add(parent); first = parent; }
                if (first.Predecessors is not [var head] || !join.Predecessors.Contains(head)
                    || head.Statements.LastOrDefault() is not Branch { Condition: Compare { Cond: Cond.Eq or Cond.Ne, Left: Use obj, Right: Const { Value: 0 } } test } branch
                    || (test.Cond == Cond.Eq ? branch.Target : branch.Fallthrough) != join.Start) continue;
                var calls = path.SelectMany(b => b.Statements).OfType<Call>().ToArray();
                TypeRef? target = null;
                foreach (var call in calls)
                {
                    if (call is { Op.Kind: OpKind.TypeCheck, Op.Operand: DefinitionRef { Definition.IsValueType: false } type, Arguments: [Use klass] }
                        && RawDefinition(klass) is Load { Width: 64, Address: var source } && source == obj
                        && call.Defines.FirstOrDefault() is { } flag && calls.Any(c => c is
                            { Op.Kind: OpKind.ThrowIf, Op.Operand: "System.InvalidCastException", Arguments: [Compare { Cond: Cond.Eq, Left: Use result, Right: Const { Value: 0 } }] }
                            && result.Variable == flag)) target = type;
                    if (call is { Op.Kind: OpKind.ThrowIf, Op.Operand: "System.InvalidCastException", Arguments: [Compare { Cond: Cond.Ne, Left: Use sealedClass, Right: Symbol { Kind: SymbolKind.Class, Value: DefinitionRef { Definition.IsValueType: false } sealedType } }] }
                        && (sealedType.Definition.Attributes & System.Reflection.TypeAttributes.Sealed) != 0
                        && RawDefinition(sealedClass) is Load { Width: 64, Address: var instance } && instance == obj) target = sealedType;
                }
                if (target is null) continue;
                var cast = Fresh();
                RefineReferenceUses(join, 0, obj, cast, dominators);
                join.Statements.Insert(join.Statements.TakeWhile(s => s is Phi).Count(), new Call(join.Start, CallKind.Direct, Expr.C(0, 64))
                {
                    Op = new RuntimeOp(OpKind.IsInst, target), Arguments = [obj], Results = [cast.Storage], Defines = [cast],
                });
                changed = true;
                break;
            }
            return changed;
        }

        // 判空边上的对象寄存器确定为零，也可复用作 Nullable 等结构体的全零返回片。
        private bool ZeroPhiSources()
        {
            var dominators = Dominators.Compute(function);
            var zeros = new List<(Variable Value, Block From, Block To)>();
            foreach (var block in function.Blocks)
                if (block.Statements.LastOrDefault() is Branch { Condition: Compare { Cond: Cond.Eq or Cond.Ne, Left: Use { Width: 64 } value, Right: Const { Value: 0 } } test } branch
                    && block.NormalSuccessors.FirstOrDefault(b => b.Start == (test.Cond == Cond.Eq ? branch.Target : branch.Fallthrough)) is { } target)
                    zeros.Add((value.Variable, block, target));
            var changed = false;
            foreach (var block in function.Blocks)
                foreach (var phi in block.Statements.OfType<Phi>().ToArray())
                {
                    var sources = phi.Sources.ToArray();
                    for (var i = 0; i < sources.Length; i++)
                    {
                        var parent = block.Predecessors[i];
                        if (!zeros.Any(z => z.Value == sources[i] && (z.From == parent && z.To == block
                            || z.To.Predecessors.Count == 1 && dominators.Dominates(z.To.Index, parent.Index)))) continue;
                        sources[i] = Fresh();
                        var terminal = parent.Statements.LastOrDefault();
                        parent.Statements.Insert(parent.Statements.Count - (terminal is Jump or Branch or IndirectJump or Return ? 1 : 0),
                            new Define(terminal?.Address ?? parent.Start, sources[i], Expr.C(0, 64)));
                        changed = true;
                    }
                    block.Statements[block.Statements.IndexOf(phi)] = phi with { Sources = sources };
                }
            return changed;
        }

        // 分支选择静态字段的地址、合流后再读取：把只读元数据寻址分发到原分支，合流的是字段值。
        private bool StaticFieldPhiLoads()
        {
            Expr ResolveMetadata(Expr expression)
            {
                var mapped = ExprMap.Map(expression, part => !ReferenceEquals(part, expression) ? ResolveMetadata(part) : null);
                var part = mapped;
                if (part is not Load { Width: 64 } load) return mapped;
                if (load.Address is Const address)
                {
                    if (facts.Usages.At(address.Value) is { } usage) return new Symbol(SymbolOf(usage.Usage.Kind), usage.Usage.Value);
                    if (facts.Model.Image.RelocatedPointer(address.Value) is { } pointer && facts.Usages.At(pointer) is not null) return Expr.C(pointer, 64);
                }
                return Split(load.Address) is (Symbol { Kind: SymbolKind.Class } type, RuntimeLayout.ClassStaticFields)
                    ? new Symbol(SymbolKind.StaticFields, type.Value) : mapped;
            }
            var changed = false;
            foreach (var block in function.Blocks)
            foreach (var phi in block.Statements.OfType<Phi>().ToArray())
            {
                if (block.Predecessors.Any(p => p.NormalSuccessors.Count() != 1 || p.Handler == block)) continue;
                foreach (var statement in block.Statements.Where(s => s is not Phi).ToArray())
                {
                    if (statement is not Define && statement is not Return) break;
                    foreach (var load in ExprMap.Operands(statement).SelectMany(ExprMap.Walk).OfType<Load>().ToArray())
                    {
                        var expanded = defs.Expand(load);
                        if (!ExprMap.Walk(expanded).OfType<Use>().Any(u => u.Variable == phi.Target)) continue;
                        var values = phi.Sources.Select(v => ResolveMetadata(ExprMap.Map(expanded,
                            part => part is Use use && use.Variable == phi.Target ? defs.Expand(new Use(v, v.Width)) : null))).ToArray();
                        if (values.Any(v => v is not Load l || Split(l.Address).Basis is not (Symbol { Kind: SymbolKind.StaticFields } or Use))) continue;
                        var target = Fresh();
                        var incoming = new Variable[values.Length];
                        for (var i = 0; i < values.Length; i++)
                        {
                            var parent = block.Predecessors[i];
                            var last = parent.Statements.LastOrDefault();
                            incoming[i] = Fresh();
                            parent.Statements.Insert(parent.Statements.Count - (last is Jump or Branch or IndirectJump or Return ? 1 : 0),
                                new Define(last?.Address ?? parent.Start, incoming[i], values[i]));
                        }
                        block.Statements.Insert(block.Statements.IndexOf(phi) + 1, new Phi(phi.Address, target, incoming));
                        var position = block.Statements.IndexOf(statement);
                        if (position >= 0) block.Statements[position] = ExprMap.MapOperands(statement, e => ExprMap.Map(e, part => part == load ? new Use(target, load.Width) : null));
                        changed = true;
                    }
                }
            }
            return changed;
        }

        // 不同分支计算同一个字段地址时，合流后仍使用原地址表达式，不生成无类型的原生指针局部。
        private bool EqualAddressPhis()
        {
            var changed = false;
            var phis = All.OfType<Phi>().ToDictionary(p => p.Target);
            void Leaves(Expr value, HashSet<Variable> active, HashSet<Expr> leaves)
            {
                value = defs.Expand(value);
                if (value is Use use && phis.TryGetValue(use.Variable, out var phi))
                {
                    if (!active.Add(use.Variable)) return;
                    foreach (var source in phi.Sources) Leaves(new Use(source, source.Width), active, leaves);
                }
                else leaves.Add(value);
            }
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Phi phi || phi.Sources.Length == 0) continue;
                    var leaves = new HashSet<Expr>();
                    Leaves(new Use(phi.Target, phi.Target.Width), [], leaves);
                    var sources = leaves.ToArray();
                    if (sources is not [Binary { Op: BinOp.Add, Right: Const } address]
                        || ExprMap.Walk(address).Any(e => e is Load or Unknown or Intrinsic)) continue;
                    block.Statements[i] = new Define(phi.Address, phi.Target, address);
                    changed = true;
                }
            return changed;
        }

        // 未用参数中的寄存器残值不应保活元数据守卫和无定义的合并值。
        private void DiscardUnusedInputs()
        {
            var phis = All.OfType<Phi>().ToDictionary(p => p.Target);
            var metadataResults = All.OfType<Call>().Where(c => owner.HelperOf(c)?.Kind == HelperKind.InitMetadata)
                .SelectMany(c => c.Defines).ToHashSet();
            bool ResidualInput(Expr value, HashSet<Variable> seen)
            {
                if (value is Unknown or Use { Variable.Version: < 0 } or Symbol { Kind: not SymbolKind.String }) return true;
                if (value is Ir.Convert convert) return ResidualInput(convert.Operand, seen);
                if (value is not Use use || !seen.Add(use.Variable)) return false;
                if (metadataResults.Contains(use.Variable)) return true;
                if (defs.Raw(use.Variable) is { } source) return ResidualInput(source, seen);
                return phis.TryGetValue(use.Variable, out var phi)
                    && phi.Sources.Any(v => ResidualInput(new Use(v, v.Width), seen));
            }
            var changed = false;
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Call { Op: null, Kind: CallKind.Direct or CallKind.Tail, Target: Const target } call
                        || owner.calls.Signature(target.Value) is not { } signature) continue;
                    var methods = facts.EntriesAt(target.Value).Select(e => e.Method).OfType<MethodRef>().ToArray();
                    if (methods.Length == 0 || methods.Any(m => m.Method.Address != target.Value && m.Method.Address != 0
                        || m.TypeArguments.Concat(m.MethodArguments).Any(FieldLayouts.IsFullyShared))) continue;
                    var args = (Expr[])call.Arguments.Clone();
                    for (var k = 0; k < args.Length && k < call.Sources.Length; k++)
                    {
                        // 原生函数可不读 MethodInfo，但恢复泛型调用仍依赖它选择实例。
                        if (call.Sources[k] == signature.MethodInfo && methods.Any(m => m.Method.GenericParameters.Count != 0
                            || m.Method.Owner.GenericParameters.Count != 0)) continue;
                        if (args[k] is Unknown || !ResidualInput(args[k], [])) continue;
                        if (call.Sources[k] != signature.MethodInfo && !owner.UnusedInput(target.Value, call.Sources[k])) continue;
                        args[k] = new Unknown("原生被调方未用的输入", args[k].Width);
                        changed = true;
                    }
                    block.Statements[i] = call with { Arguments = args };
                }
            if (changed) Cleanup();
        }

        private void TrimResultBuffers()
        {
            if (owner.inputLifter.Machine.Convention.IndirectResult is not { } buffer) return;
            var changed = false;
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Call { Op: null, Kind: CallKind.Direct or CallKind.Tail, Target: Const target } call
                        || facts.Code.RegionOf(target.Value) != CodeRegion.Managed || owner.calls.Signature(target.Value) is not null) continue;
                    var index = Array.IndexOf(call.Sources, buffer);
                    if (index < 0 || !owner.UnusedResultBuffer(target.Value)) continue;
                    block.Statements[i] = call with
                    {
                        Sources = call.Sources.Where((_, k) => k != index).ToArray(),
                        Arguments = call.Arguments.Where((_, k) => k != index).ToArray(),
                    };
                    changed = true;
                }
            if (changed) Cleanup();
        }

        private void CountCalls()
        {
            foreach (var call in All.OfType<Call>())
            {
                if (owner.HelperOf(call) is { } helper) Result.HelperCalls[helper.Kind] = Result.HelperCalls.GetValueOrDefault(helper.Kind) + 1;
                else if (call.Kind is CallKind.Indirect or CallKind.TailIndirect) Result.IndirectCalls++;
            }
        }

        // ---------- 槽位与静态字段块 ----------

        private static SymbolKind SymbolOf(UsageKind kind) => kind switch
        {
            UsageKind.TypeInfo => SymbolKind.Class,
            UsageKind.Il2CppType => SymbolKind.Type,
            UsageKind.MethodDef or UsageKind.MethodRef => SymbolKind.Method,
            UsageKind.FieldInfo => SymbolKind.Field,
            _ => SymbolKind.String,
        };

        /// <summary>地址拆成（基址, 常量偏移）。</summary>
        private static (Expr Basis, ulong Offset) Split(Expr address) =>
            address is Binary { Op: BinOp.Add, Right: Const offset } b ? (b.Left, offset.Value) : (address, 0);

        private static DefinitionRef GenericForm(TypeDef type) =>
            new(type, type.GenericParameters.Select(p => (TypeRef)new GenericParameterRef(p.Name, false, p.Position) { Parameter = p }).ToArray());

        private static RgctxTable Table(MethodRef method) => new(method.Method.Owner.Assembly, method.Method.Token, method.ToString(), method.TypeArguments, method.MethodArguments);

        private static RgctxTable Table(DefinitionRef type) => new(type.Definition.Assembly, type.Definition.Token, type.ToString(), type.Arguments, []);

        /// <summary>RGCTX 第 index 项（以表的实参代入）。表中没有该项返回 null。</summary>
        private Symbol? Entry(RgctxTable table, int index)
        {
            if (!facts.Registrations.Rgctx.TryGetValue((table.Image, table.Token), out var entries) || index < 0 || index >= entries.Length) return null;
            TypeRef Type(TypeRef t) => table.TypeArguments is null && table.MethodArguments is null ? t : t.Substitute(table.TypeArguments ?? [], table.MethodArguments ?? []);
            MethodRef Method(MethodRef m) => table.TypeArguments is null && table.MethodArguments is null ? m
                : m with { TypeArguments = m.TypeArguments.Select(Type).ToArray(), MethodArguments = m.MethodArguments.Select(Type).ToArray() };
            static TypeRef Element(TypeRef t) => t is ByRefRef r ? r.Element : t;
            var entry = entries[index];
            return entry switch
            {
                { Kind: RgctxKind.Type, Value: TypeRef t } => new Symbol(SymbolKind.Type, Type(t)),
                { Kind: RgctxKind.Class, Value: TypeRef t } => new Symbol(SymbolKind.Class, Type(Element(t))),
                { Kind: RgctxKind.Array, Value: TypeRef t } => new Symbol(SymbolKind.Class, new ArrayRef(Type(Element(t)), 1)),
                { Kind: RgctxKind.Method, Value: MethodRef m } => new Symbol(SymbolKind.Method, Method(m)),
                { Kind: RgctxKind.Constrained, Value: ValueTuple<TypeRef, MethodRef> c } => new Symbol(SymbolKind.Constrained, (Type(c.Item1), Method(c.Item2))),
                _ => null,
            };
        }

        /// <summary>
        /// 符号化（与传播交替到不动点）：槽位读取 → Symbol；Class+0xB8 → 静态字段块；MethodInfo+0x20 → 声明类。
        /// rgctx 为真时还有：MethodInfo+0x38 / Class+0xC0 → RGCTX 数组，数组第 i 项（偏移 8i）→ 表中条目；
        /// 函数自身的 MethodInfo* 参数的 RGCTX 保留泛型参数形式。
        /// </summary>
        private void Symbols(bool rgctx)
        {
            var dominators = Dominators.Compute(function);
            var ownDefinition = self?.Method;
            while (true)
            {
                var changed = false;
                Expr? Map(Expr e)
                {
                    // FieldInfo 表按声明顺序排列，每项包含 name/type/parent/offset/token，共 32 字节。
                    if (e is Load { Width: 64, Address: Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Class, Value: DefinitionRef fieldOwner }, Right: Const { Value: RuntimeLayout.ClassFields } } }
                        && fieldOwner.Definition.Fields.Count > 0)
                    {
                        changed = true;
                        return new Symbol(SymbolKind.Field, new FieldRef(fieldOwner.Definition.Fields[0], fieldOwner));
                    }
                    if (e is Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Field, Value: FieldRef field }, Right: Const fieldOffset }
                        && field.DeclaringType is DefinitionRef fieldType && fieldOffset.Value % RuntimeLayout.FieldInfoSize == 0
                        && fieldType.Definition.Fields.ToList().IndexOf(field.Field) + (long)fieldOffset.Value / RuntimeLayout.FieldInfoSize is var fieldIndex
                        && fieldIndex >= 0 && fieldIndex < fieldType.Definition.Fields.Count)
                    {
                        changed = true;
                        return new Symbol(SymbolKind.Field, new FieldRef(fieldType.Definition.Fields[(int)fieldIndex], fieldType));
                    }
                    // RGCTX 已解析为元数据表后，判空只决定运行时的延迟初始化；托管体使用初始化后的表。
                    if (e is Compare { Cond: Cond.Eq or Cond.Ne, Left: Symbol { Kind: SymbolKind.Rgctx, Value: RgctxTable guardTable }, Right: Const { Value: 0 } } guard
                        && facts.Registrations.Rgctx.TryGetValue((guardTable.Image, guardTable.Token), out var entries) && entries.Length > 0)
                    {
                        changed = true;
                        foldedRuntimeGuards = true;
                        Result.Hit(Template.MethodRgctxGuard);
                        return Expr.C(guard.Cond == Cond.Ne ? 1UL : 0UL, 1);
                    }
                    // MethodInfo.slot（uint16）：泛型实例与定义相同，取元数据中的槽位
                    if (e is Load { Width: 16, Address: Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Method, Value: MethodRef slotted }, Right: Const { Value: RuntimeLayout.MethodSlot } } }
                        && slotted.Method.Slot is >= 0 and < 0xFFFF)
                    {
                        Result.Hit(Template.MethodSlot);
                        changed = true;
                        return Expr.C((ulong)slotted.Method.Slot, 16);
                    }
                    if (e is not Load { Width: 64 } load) return null;
                    if (load.Address is Const address && facts.Usages.At(address.Value) is { } slot)
                    {
                        Result.ReadSlots.Add(address.Value);
                        Result.Hit(Template.MetadataSlot);
                        changed = true;
                        var symbol = new Symbol(SymbolOf(slot.Usage.Kind), slot.Usage.Value);
                        symbolSlots.TryAdd(symbol, address.Value);
                        return symbol;
                    }
                    var (basis, offset) = Split(load.Address);
                    var own = basis is Use { Variable: { Version: 0 } v } && v.Storage == selfMethodInfo && ownDefinition is not null;
                    Symbol? found = (basis, offset) switch
                    {
                        (Symbol { Kind: SymbolKind.Class } c, RuntimeLayout.ClassStaticFields) => new Symbol(SymbolKind.StaticFields, c.Value),
                        (Symbol { Kind: SymbolKind.Method, Value: MethodRef m }, RuntimeLayout.MethodKlass) => new Symbol(SymbolKind.Class, m.DeclaringType),
                        (_, RuntimeLayout.MethodKlass) when own => new Symbol(SymbolKind.Class, GenericForm(ownDefinition!.Owner)),
                        (Symbol { Kind: SymbolKind.Method, Value: MethodRef m }, RuntimeLayout.MethodRgctxData) when rgctx => new Symbol(SymbolKind.Rgctx, Table(m)),
                        (_, RuntimeLayout.MethodRgctxData) when rgctx && own =>
                            new Symbol(SymbolKind.Rgctx, new RgctxTable(ownDefinition!.Owner.Assembly, ownDefinition.Token, ownDefinition.ToString(), null, null)),
                        (Symbol { Kind: SymbolKind.Class, Value: DefinitionRef t }, RuntimeLayout.ClassRgctxData) when rgctx => new Symbol(SymbolKind.Rgctx, Table(t)),
                        (Symbol { Kind: SymbolKind.Rgctx, Value: RgctxTable table }, var o) when o % 8 == 0 => Entry(table, (int)(o / 8)),
                        _ => null,
                    };
                    if (found is null) return null;
                    Result.Hit(found.Kind switch
                    {
                        SymbolKind.StaticFields => Template.StaticFields,
                        SymbolKind.Rgctx => Template.RgctxData,
                        _ when basis is Symbol { Kind: SymbolKind.Rgctx } => Template.RgctxEntry,
                        _ => Template.MethodClass,
                    });
                    changed = true;
                    return found;
                }
                foreach (var block in function.Blocks)
                    for (var i = 0; i < block.Statements.Count; i++)
                        block.Statements[i] = ExprMap.MapOperands(block.Statements[i], e => ExprMap.Map(e, Map));
                if (!changed) break;
                Propagate.Run(function, dominators);
            }
        }

        // 分支先选择字符串槽地址、合流后统一读取；将只读元数据的选择还原成字符串值的选择。
        private bool StringSlotChoices()
        {
            var definitions = new Defs(function);
            var changed = false;
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                    block.Statements[i] = ExprMap.MapOperands(block.Statements[i], e => ExprMap.Map(e, part =>
                    {
                        if (part is not Load { Width: 64 } load) return null;
                        var address = load.Address;
                        for (var depth = 0; depth < 8 && address is Use use && definitions.Raw(use.Variable) is { } value; depth++) address = value;
                        if (address is not Select || SlotValue(definitions.Expand(address), out var slots) is not { } choice
                            || slots.Any(s => s.Usage.Kind != UsageKind.StringLiteral)) return null;
                        changed = true;
                        Result.ReadSlots.UnionWith(slots.Select(s => s.Address));
                        return choice;
                    }));
            return changed;
        }

        private Expr? SlotValue(Expr address, out UsageSlot[] slots)
        {
            var found = new List<UsageSlot>();
            Expr? Read(Expr value)
            {
                if (value is Const constant && facts.Usages.At(constant.Value) is { } slot
                    && slot.Usage.Kind is UsageKind.StringLiteral or UsageKind.MethodDef or UsageKind.MethodRef)
                {
                    found.Add(slot);
                    return new Symbol(SymbolOf(slot.Usage.Kind), slot.Usage.Value);
                }
                return value is Select choice && Read(choice.True) is { } yes && Read(choice.False) is { } no
                    ? choice with { True = yes, False = no } : null;
            }
            var result = Read(address);
            slots = found.ToArray();
            return slots.Select(s => SymbolOf(s.Usage.Kind)).Distinct().Count() == 1 ? result : null;
        }

        private bool MetadataSlotPhis()
        {
            var changed = false;
            var definitions = new Defs(function);
            foreach (var block in function.Blocks)
            foreach (var phi in block.Statements.OfType<Phi>().ToArray())
            {
                if (phi.Sources.Length != block.Predecessors.Count
                    || block.Predecessors.Any(p => !p.NormalSuccessors.Contains(block) || p.Handler == block)) continue;
                var choices = phi.Sources.Select(v =>
                {
                    var value = SlotValue(definitions.Expand(new Use(v, v.Width)), out var slots);
                    return (Value: value, Slots: slots);
                }).ToArray();
                if (choices.Any(c => c.Value is null)
                    || choices.SelectMany(c => c.Slots).Select(s => SymbolOf(s.Usage.Kind)).Distinct().Count() != 1) continue;
                var loads = All.SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).OfType<Load>()
                    .Where(l => l is { Width: 64, Address: Use use } && use.Variable == phi.Target).ToHashSet();
                if (loads.Count == 0) continue;
                var target = Fresh();
                var sources = new Variable[choices.Length];
                for (var i = 0; i < choices.Length; i++)
                {
                    var parent = block.Predecessors[i];
                    var last = parent.Statements.LastOrDefault();
                    var position = parent.Statements.Count - (last is Jump or Branch or IndirectJump or Return ? 1 : 0);
                    sources[i] = Fresh();
                    parent.Statements.Insert(position, new Define(last?.Address ?? parent.Start, sources[i], choices[i].Value!));
                    foreach (var slot in choices[i].Slots)
                    {
                        Result.ReadSlots.Add(slot.Address);
                        symbolSlots.TryAdd(new Symbol(SymbolOf(slot.Usage.Kind), slot.Usage.Value), slot.Address);
                    }
                }
                block.Statements.Insert(block.Statements.IndexOf(phi) + 1, new Phi(phi.Address, target, sources));
                foreach (var member in function.Blocks)
                    for (var i = 0; i < member.Statements.Count; i++)
                        member.Statements[i] = ExprMap.MapOperands(member.Statements[i], e => ExprMap.Map(e,
                            part => part is Load load && loads.Contains(load) ? new Use(target, 64) : null));
                Result.Hit(Template.MetadataSlot);
                changed = true;
            }
            return changed;
        }

        // Calls 已记录 InitMetadata 的初始化证据，再删除只负责延迟初始化的不可达分支。
        private void PruneRuntimeGuards()
        {
            foreach (var block in function.Blocks)
            {
                if (block.Statements.LastOrDefault() is not Branch { Condition: Const constant } branch) continue;
                var normal = block.NormalSuccessors.ToArray();
                if (normal.Length != 2 || normal[0].Start != branch.Target || normal[1].Start != branch.Fallthrough) continue;
                var side = constant.Value != 0 ? 0 : 1;
                block.Statements[^1] = new Jump(branch.Address, normal[side].Start);
                MachineFunction.RemoveEdgeAt(block, 1 - side);
            }
            Cleanup();
        }

        // ---------- 守卫 ----------

        // 初始化臂还含字段重读时保留该臂的数据流，只移除元数据标志；避免丢掉合流处实际使用的值。
        private bool RetainMetadataPath()
        {
            var changed = false;
            foreach (var head in function.Blocks)
            {
                if (removed.Contains(head) || head.Statements.LastOrDefault() is not Branch branch || head.NormalSuccessors.ToArray() is not [var first, var second]) continue;
                var condition = defs.Expand(branch.Condition);
                if (TopLoads(condition).Distinct().ToArray() is not [Load { Width: 8, Address: Const guard } load]
                    || !owner.guardSections.Any(s => s.Contains(guard.Value))) continue;
                var side = Direction(condition, Replace(load, 0));
                if (side is not (0 or 1) || Direction(condition, Replace(load, 1)) != 1 - side) continue;
                var init = side == 0 ? first : second;
                var skip = side == 0 ? second : first;
                if (Chain(init, skip) is not { Count: > 0 } chain) continue;
                var statements = chain.SelectMany(b => b.Statements).ToArray();
                var calls = statements.OfType<Call>().ToArray();
                var stores = statements.OfType<Store>().ToArray();
                if (calls.Length == 0 || stores is not [Store { Target: Const target, Value: Const { Value: 1, Width: 8 } } set]
                    || target.Value != guard.Value || calls.Any(c => owner.HelperOf(c)?.Kind != HelperKind.InitMetadata)
                    || statements.Any(s => s is not (Call or Store or Define or Nop or Jump))) continue;
                var slots = calls.Select(c => defs.Expand(c.Arguments.FirstOrDefault() ?? Expr.C(0, 64)))
                    .OfType<Const>().Select(c => c.Value).ToArray();
                if (slots.Length != calls.Length || slots.Any(s => facts.Usages.At(s) is null)) continue;
                var storeBlock = chain.Single(b => b.Statements.Contains(set));
                storeBlock.Statements[storeBlock.Statements.IndexOf(set)] = new Nop(set.Address, "MetadataInitGuard");
                head.Statements[^1] = new Jump(branch.Address, init.Start);
                MachineFunction.RemoveEdgeAt(head, 1 - side.Value);
                Result.GuardSlots[guard.Value] = slots.Distinct().Order().ToArray();
                Result.InitializedSlots.UnionWith(slots);
                Result.MetadataGuardBranches.Add(branch.Address);
                Result.Hit(Template.MetadataInitGuard);
                changed = true;
            }
            return changed;
        }

        // 初始化分支复制了后继业务判断时，两臂没有直线汇合；只跳过已证明等价的初始化前缀。
        private bool SplitMetadataGuards()
        {
            var changed = false;
            foreach (var head in function.Blocks)
            {
                if (head.Statements.LastOrDefault() is not Branch branch || head.NormalSuccessors.ToArray() is not [var first, var second]) continue;
                var condition = defs.Expand(branch.Condition);
                if (TopLoads(condition).Distinct().ToArray() is not [Load { Width: 8, Address: Const guard } load]
                    || !owner.guardSections.Any(s => s.Contains(guard.Value))) continue;
                var side = Direction(condition, Replace(load, 0));
                if (side is not (0 or 1) || Direction(condition, Replace(load, 1)) != 1 - side) continue;
                var init = side == 0 ? first : second;
                var skip = side == 0 ? second : first;
                if (init.IsLandingPad || init.Predecessors.Count != 1 || init.Statements.LastOrDefault() is not Branch after
                    || skip.Statements.LastOrDefault() is not Branch normal || skip.Statements.Any(s => s is not (Define or Nop or Branch))) continue;
                var left = defs.Expand(after.Condition);
                var right = defs.Expand(normal.Condition);
                if (!(left == right && after.Target == normal.Target && after.Fallthrough == normal.Fallthrough)
                    && !(left == Fold.Simplify(new Not(right)) && after.Target == normal.Fallthrough && after.Fallthrough == normal.Target)) continue;
                var slots = new List<ulong>();
                var sets = 0;
                var valid = true;
                foreach (var statement in init.Statements.SkipLast(1))
                    switch (statement)
                    {
                        case Call call when owner.HelperOf(call)?.Kind == HelperKind.InitMetadata
                            && defs.Expand(call.Arguments.FirstOrDefault() ?? Expr.C(0, 64)) is Const slot && facts.Usages.At(slot.Value) is not null:
                            slots.Add(slot.Value);
                            break;
                        case Store { Target: Const target, Value: Const { Value: 1, Width: 8 } } when target.Value == guard.Value:
                            sets++;
                            break;
                        case Define { Value: Const or Symbol } or Nop:
                            break;
                        default:
                            valid = false;
                            break;
                    }
                if (!valid || slots.Count == 0 || sets != 1) continue;
                head.Statements[^1] = new Jump(branch.Address, skip.Start);
                MachineFunction.RemoveEdgeAt(head, side.Value);
                Result.GuardSlots[guard.Value] = slots.Distinct().Order().ToArray();
                Result.InitializedSlots.UnionWith(slots);
                Result.MetadataGuardBranches.Add(branch.Address);
                Result.Hit(Template.MetadataInitGuard);
                changed = true;
            }
            return changed;
        }

        private bool InitializedClassLoads() => self?.Method.Name != ".cctor" && ClassInitializationFacts.Run(function);

        /// <summary>从 start 出发的单前驱、单后继直链，直到 merge；不是直链返回 null。</summary>
        private static List<Block>? Chain(Block start, Block merge)
        {
            var chain = new List<Block>();
            for (var b = start; b != merge; )
            {
                if (b.Predecessors.Count != 1 || b.IsLandingPad || chain.Count >= 64) return null;
                var next = b.NormalSuccessors.ToArray();
                if (next.Length != 1) return null;
                chain.Add(b);
                b = next[0];
            }
            return chain;
        }

        private bool Guards()
        {
            var changed = false;
            foreach (var head in function.Blocks.ToArray())
            {
                if (removed.Contains(head) || head.Statements.LastOrDefault() is not Branch branch) continue;
                var normal = head.NormalSuccessors.ToArray();
                if (normal.Length != 2 || normal[0] == normal[1]) continue;
                for (var side = 0; side < 2; side++)
                {
                    // 两臂都跳到汇合点时，先越过没有活语句的跳过臂，形成标准的类初始化守卫。
                    var skipped = normal[1 - side];
                    if (skipped.Predecessors.Count == 1 && !skipped.IsLandingPad && skipped.Statements.All(s => s is Nop or Jump)
                        && skipped.NormalSuccessors.ToArray() is [var merge] && merge != head
                        && Chain(normal[side], merge) is { Count: > 0 } guarded
                        && guarded.SelectMany(b => b.Statements).OfType<Call>().ToArray() is [var initializer]
                        && owner.HelperOf(initializer)?.Kind == HelperKind.ClassInit)
                    {
                        var targets = side == 0 ? new List<(Block, Block)> { (normal[0], head), (merge, skipped) }
                            : [(merge, skipped), (normal[1], head)];
                        var rewritten = new Branch(branch.Address, branch.Condition, targets[0].Item1.Start, targets[1].Item1.Start);
                        if (Rewire(head, [], rewritten, targets, [skipped]))
                        {
                            Remove([skipped]);
                            changed = true;
                            break;
                        }
                    }
                    if (Chain(normal[side], normal[1 - side]) is not { Count: > 0 } chain) continue;
                    if (!Guard(head, branch, side, chain, normal[1 - side])) continue;
                    changed = true;
                    break;
                }
            }
            return changed;
        }

        /// <summary>块内的一个执行位置：第 Index 条语句之前、地址 Address 的指令之前（传播删去的定义按地址排入）。</summary>
        private readonly record struct Point(int Index, ulong Address);

        /// <summary>
        /// 模板在 head 内的起点：第 end 条语句（默认终结语句）与 extra 依赖的 head 内定义中最早一条所在的指令
        /// （调用的结果视为起点处已在寄存器中）。依赖包括传播删去、已内联进这些表达式的定义（如虚调用目标的两次读取），
        /// 以及终结分支之前最后一次写标志位的指令（比较）。起点不是 head 自己的指令（之前的改写插入的语句）时退回 head 开头。
        /// </summary>
        private Point Start(Block head, params Expr[] extra) => Start(head, head.Statements.Count - 1, extra);

        /// <param name="end">根语句下标；等于语句数时没有根语句，只以 extra 为根（块末尾）。</param>
        private Point Start(Block head, int end, params Expr[] extra)
        {
            var statements = head.Statements;
            var endAddress = end < statements.Count ? statements[end].Address : statements.Count > 0 ? statements[^1].Address + 1 : head.Start;
            var defined = new Dictionary<Variable, int>();
            for (var i = 0; i < end; i++)
                if (statements[i] is Define d) defined[d.Target] = i;
            var start = end;
            var seen = new HashSet<Variable>();
            var roots = (end < statements.Count ? ExprMap.Operands(statements[end]) : []).Concat(extra).ToList();
            var work = new Stack<Expr>(roots);
            while (work.Count > 0)
                foreach (var use in ExprMap.Walk(work.Pop()).OfType<Use>())
                    if (seen.Add(use.Variable) && defined.TryGetValue(use.Variable, out var i))
                    {
                        start = Math.Min(start, i);
                        work.Push(((Define)statements[i]).Value);
                    }
            var address = start < statements.Count ? statements[start].Address : endAddress;
            var inlined = roots.Select(e => defs.Expand(e)).SelectMany(ExprMap.Walk).ToHashSet();
            // 删去的定义只看最后一次调用或写内存之后的：更早的同一表达式（如两次虚调用各自读 klass）未必是这里用到的值
            var barrier = statements.Take(Math.Min(end, statements.Count)).Where(x => x is Call or Store && x.Address >= head.Start && x.Address < endAddress)
                .Select(x => x.Address).DefaultIfEmpty(head.Start).Max();
            Define? flags = null;
            foreach (var (block, d) in function.Dead)
            {
                if (block != head || d.Address < head.Start || d.Address >= endAddress || d.Address <= barrier && barrier != head.Start) continue;
                if (d.Target.Storage.Bank == Bank.Flags) { if (flags is null || d.Address > flags.Address) flags = d; }
                // 只看有运算的定义：常量、复制之类处处可能作为子表达式出现，而且由前缀执行与 env 重建
                else if (defs.Expand(new Use(d.Target, d.Target.Width)) is not (Const or Use or Symbol or FrameAddress) and var value && inlined.Contains(value))
                    address = Math.Min(address, d.Address);
            }
            if (end < statements.Count && statements[end] is Branch && flags is not null
                && !statements.Take(end).Any(x => x.Address > flags.Address && x is Define { Target.Storage.Bank: Bank.Flags }))
                address = Math.Min(address, flags.Address);
            var first = statements.TakeWhile(x => x is Phi).Count();
            if (address < head.Start || address > endAddress) return new(first, head.Start);
            var index = statements.FindIndex(x => x is not Phi && x.Address >= address);
            if (index < 0 || index > start) index = start;
            return index <= first && (first == statements.Count || address <= statements[first].Address) ? new(first, head.Start) : new(index, address);
        }

        /// <summary>
        /// 值的放置方式：有位置时为 <see cref="Location"/> 的字符串（去掉宽度转换后再试一次）；
        /// 否则值是对"可放置的基址 + 常量偏移"的读取时为 {base, offset, width}（测试分配一个对象，把值写入该字段）。
        /// </summary>
        private object? Placement(Expr expanded, Block head, Point start)
        {
            var stripped = StripConversions(expanded);
            // 读取优先按"基址 + 偏移"布置：模板可能重新读取内存，寄存器里同一表达式的旧值不一定被用到
            var registers = Location(expanded, head, start) ?? Location(stripped, head, start);
            if (stripped is Load load && Split(load.Address) is var (basis, offset) && Location(basis, head, start) is { } at)
            {
                // 同时给出展开相同的寄存器：模板用的可能是早先读到寄存器里的值，也可能重新读内存
                var field = new Dictionary<string, object> { ["base"] = at, ["offset"] = offset, ["width"] = load.Width };
                if (registers is not null) field["also"] = registers;
                return field;
            }
            return registers;
        }

        /// <summary>
        /// 值在 head 内 start 处的位置，多个位置以 "+" 连接：来自槽位的符号为 "slot:地址"；
        /// 此处版本展开后等于该值的通用寄存器为 "xN"（复制传播之后，SSA 变量所属的寄存器不一定仍持有它）。都没有时为 null。
        /// </summary>
        private string? Location(Expr expanded, Block head, Point start)
        {
            var places = new List<string>();
            if (expanded is Symbol symbol && symbolSlots.TryGetValue(symbol, out var slot)) places.Add($"slot:0x{slot:x}");
            // 删去的槽位读取没有经过符号化，仍是对槽位地址的读取
            var slotLoad = places.Count > 0 ? new Load(Expr.C(symbolSlots[(Symbol)expanded], 64), 64) : null;
            for (var i = 0; i < 31; i++)
                if (ReachingBefore(head, start, Storage.Gpr(i)) is { } v && defs.Expand(new Use(v, 64)) is var e && (e == expanded || e == slotLoad)) places.Add($"x{i}");
            return places.Count == 0 ? null : string.Join("+", places);
        }

        private Variable? ReachingBefore(Block head, Point start, Storage storage) =>
            LastDefinition(head, storage, start.Index, start.Address) ?? ReachingAt(head, storage, new());

        /// <summary>
        /// block 入口处 storage 的 SSA 版本：块内的 phi，或所有前驱出口处的同一版本；路径不一致或不可知时为 null。
        /// 被调用破坏而没有新版本的寄存器为版本 -1（不会与任何值相等）。
        /// 环按乐观方式处理：回到正在求值的块时不提供信息（该路径上没有重新定义时值不变；有重新定义时在那里得到别的版本而不一致）。
        /// 依赖这种假设的中间结果不缓存。
        /// </summary>
        private Variable? ReachingAt(Block block, Storage storage, Dictionary<Block, Variable?> memo) =>
            Reaching(block, storage, memo, [], out _) is var (v, known) && known ? v : null;

        private (Variable? Value, bool Known) Reaching(Block block, Storage storage, Dictionary<Block, Variable?> memo, HashSet<Block> active, out bool assumed)
        {
            assumed = false;
            foreach (var phi in block.Statements.OfType<Phi>())
                if (phi.Target.Storage == storage) return (phi.Target, true);
            // 已折叠、等待 Cleanup 删除的区域块不再是路径
            var predecessors = block.Predecessors.Distinct().Where(p => !removed.Contains(p)).ToArray();
            if (predecessors.Length == 0) return block == function.EntryBlock ? (new Variable(storage, 0), true) : (null, false);
            if (memo.TryGetValue(block, out var cached)) return (cached, cached is not null);
            if (active.Contains(block)) { assumed = true; return (null, true); }
            if (active.Count > 400) return (null, false);
            active.Add(block);
            Variable? found = null;
            var known = true;
            foreach (var predecessor in predecessors)
            {
                var v = LastDefinition(predecessor, storage, predecessor.Statements.Count, ulong.MaxValue);
                if (v is null)
                {
                    (v, var ok) = Reaching(predecessor, storage, memo, active, out var inner);
                    assumed |= inner;
                    if (!ok) { known = false; break; }
                    if (v is null) continue; // 回边：不提供信息
                }
                if (found is not null && v != found) { known = false; break; }
                found = v;
            }
            active.Remove(block);
            if (!known || found is null) { if (!assumed || !known) memo[block] = null; return (null, false); }
            if (!assumed) memo[block] = found;
            return (found, true);
        }

        /// <summary>block 前 end 条语句与地址 boundary 之前删去的定义（<see cref="MachineFunction.Dead"/>，按指令地址排入）中 storage 的最后一个版本。</summary>
        private Variable? LastDefinition(Block block, Storage storage, int end, ulong boundary)
        {
            Define? dead = null;
            foreach (var (b, d) in function.Dead)
                if (b == block && d.Target.Storage == storage && d.Address < boundary && (dead is null || d.Address >= dead.Address)) dead = d;
            for (var i = end - 1; i >= 0; i--)
            {
                var stmt = block.Statements[i];
                if (dead is not null && dead.Address > stmt.Address) return dead.Target;
                switch (stmt)
                {
                    case Define d when d.Target.Storage == storage: return d.Target;
                    case Phi p when p.Target.Storage == storage: return p.Target;
                    case Call c when c.Defines.FirstOrDefault(v => v?.Storage == storage) is { } v: return v;
                    // 检查与内联类型检查在通过一侧不调用任何函数；其余（含守卫，慢路径会调用）按调用约定破坏寄存器
                    case Call { Op.Kind: OpKind.NullCheck or OpKind.BoundsCheck or OpKind.ThrowIf or OpKind.TypeCheck }: break;
                    case Call c when owner.calls.Clobbers(c).Contains(storage): return new Variable(storage, -1);
                }
            }
            return dead?.Target;
        }

        /// <summary>
        /// 记录实例：起点为 head 内的 start；inputs 另加 "env"：此处持有常量的通用寄存器（如 GOT 项、槽位地址），
        /// "block"：head 的起始地址，"path"：head 的唯一前驱链（起点之前的指令可能计算出被传播删去的地址寄存器）。
        /// </summary>
        private void Record(Template template, Block head, Point start, Dictionary<string, ulong> exits, Dictionary<string, object> inputs)
        {
            var env = new Dictionary<string, ulong>();
            for (var i = 0; i < 31; i++)
                if (ReachingBefore(head, start, Storage.Gpr(i)) is { } v && defs.Expand(new Use(v, 64)) is Const c) env[$"x{i}"] = c.Value;
            inputs["env"] = env;
            // 派生寄存器：此处持有"可放置基址 + 偏移"处读取值的寄存器（如重复使用的 klass->typeHierarchyDepth），测试按布置好的内存计算
            var derived = new Dictionary<string, object>();
            for (var i = 0; i < 31; i++)
                if (!env.ContainsKey($"x{i}") && ReachingBefore(head, start, Storage.Gpr(i)) is { } v
                    && StripConversions(defs.Expand(new Use(v, 64))) is Load load && Split(load.Address) is var (basis, offset)
                    && basis is not Const && Location(basis, head, start) is { } at)
                    derived[$"x{i}"] = new Dictionary<string, object> { ["base"] = at, ["offset"] = offset, ["width"] = load.Width };
            inputs["derived"] = derived;
            inputs["block"] = head.Start;
            // 唯一前驱链：从链首到 head 只有这一条路径，沿它执行得到的寄存器值就是程序在 head 入口的值
            var path = new List<ulong>();
            for (var b = head; b.Predecessors.Distinct().Where(x => !removed.Contains(x)).ToArray() is [var p] && p != head && !b.IsLandingPad && !path.Contains(p.Start) && path.Count < 8; b = p)
                path.Insert(0, p.Start);
            inputs["path"] = path;
            Result.Instances.Add(new(template, function.Entry, Math.Max(start.Address, head.Start), exits, inputs));
        }

        /// <summary>不在另一个读取的地址之内的读取。</summary>
        private static IEnumerable<Load> TopLoads(Expr e)
        {
            if (e is Load load) { yield return load; yield break; }
            foreach (var child in ExprMap.Children(e))
                foreach (var l in TopLoads(child)) yield return l;
        }

        /// <summary>代入 subst 之后条件的取值决定的分支方向：0 为跳转目标一侧，1 为顺序一侧；不确定为 null。</summary>
        private static int? Direction(Expr condition, Func<Expr, Expr?> subst) =>
            Fold.Simplify(ExprMap.Map(condition, subst)) is Const c ? (c.Value != 0 ? 0 : 1) : null;

        private static Func<Expr, Expr?> Replace(Expr load, ulong value) =>
            e => e == load ? Expr.C(value, e.Width) : null;

        private bool Guard(Block head, Branch branch, int side, List<Block> chain, Block merge)
        {
            var statements = chain.SelectMany(b => b.Statements).ToList();
            var calls = statements.OfType<Call>().ToList();
            if (calls.Count == 0) return false;
            var helpers = calls.Select(c => owner.HelperOf(c)?.Kind).ToList();
            var condition = defs.Expand(branch.Condition);
            var loads = TopLoads(condition).Distinct().ToList();
            if (loads.Count != 1) return false;
            var load = loads[0];
            bool Decides(ulong enter, ulong skip) =>
                Direction(condition, Replace(load, enter)) == side && Direction(condition, Replace(load, skip)) == 1 - side;

            // s_Il2CppMethodInitialized：读 1 字节守卫，区域内只有 InitMetadata(槽位)、置位写入与纯定义
            if (helpers.All(k => k == HelperKind.InitMetadata))
            {
                if (load is not { Width: 8, Address: Const guard } || !owner.guardSections.Any(s => s.Contains(guard.Value))) return false;
                var slots = new List<ulong>();
                var sets = 0;
                foreach (var stmt in statements)
                {
                    switch (stmt)
                    {
                        case Call call when defs.Expand(call.Arguments.FirstOrDefault() ?? Expr.C(0, 64)) is Const slot && facts.Usages.At(slot.Value) is not null:
                            slots.Add(slot.Value);
                            break;
                        case Store { Target: Const target, Value: Const { Value: 1, Width: 8 } } when target.Value == guard.Value:
                            sets++;
                            break;
                        case Define { Value: Const or Symbol } or Nop or Jump:
                            break;
                        default:
                            return false;
                    }
                }
                if (sets == 0 || !Decides(0, 1) || Merge(head, chain, merge, null, null) is not { } overrides) return false;
                if (recording) Record(Template.MetadataInitGuard, head, Start(head), new() { ["merge"] = merge.Start }, new()
                {
                    ["guard"] = guard.Value, ["slots"] = slots.ToArray(),
                    ["helpers"] = calls.Select(c => ((Const)c.Target).Value).Distinct().ToArray(),
                });
                Collapse(head, merge, head, [], overrides, branch.Address);
                Remove(chain);
                Result.GuardSlots[guard.Value] = [.. Result.GuardSlots.GetValueOrDefault(guard.Value, []).Union(slots).Order()];
                Result.MetadataGuardBranches.Add(branch.Address);
                Result.InitializedSlots.UnionWith(slots);
                Result.Hit(Template.MetadataInitGuard);
                return true;
            }

            if (calls.Count != 1 || calls[0].Arguments.Length == 0) return false;
            var helperCall = calls[0];
            var argument = helperCall.Arguments[0];
            var regionDefined = Defined(chain);
            if (ExprMap.Walk(argument).OfType<Use>().Any(u => regionDefined.Contains(u.Variable))) return false;
            var subject = defs.Expand(argument);
            Expr Field(int offset) => Fold.Simplify(new Binary(BinOp.Add, subject, Expr.C((ulong)offset, 64), 64));
            var (kind, template, enter, skip, offset, width, returnsArgument) = helpers[0] switch
            {
                HelperKind.ClassInit => (OpKind.RunClassConstructor, Template.ClassConstructorGuard, 0UL, 1UL, RuntimeLayout.ClassCctorFinishedOrNoCctor, 32, false),
                HelperKind.InitializedTypeInfo => (OpKind.InitClass, Template.InitClassGuard, 0UL, 1UL, RuntimeLayout.ClassBitflags1, 8, true),
                HelperKind.InitMethodRgctx => (OpKind.InitMethodRgctx, Template.MethodRgctxGuard, 0UL, 0x1000UL, RuntimeLayout.MethodRgctxData, 64, true),
                _ => default,
            };
            if (width == 0 || load.Width != width || load.Address != Field(offset) || !Decides(enter, skip)) return false;
            // 区域内除 helper 调用外只允许纯定义：常量、符号、对守卫字段的重新读取（初始化之后的值）
            if (!statements.All(s => s is Nop or Jump || ReferenceEquals(s, helperCall)
                || s is Define { Value: Const or Symbol } || s is Define d && defs.Expand(d.Value) == load)) return false;
            var result = returnsArgument && helperCall.Defines.Length > 0 ? helperCall.Defines[0] : null;
            if (result is not null && statements.Any(s => ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => u.Variable == result))) return false;

            var reload = new List<Stmt>();
            Variable? reloaded = null;
            Variable Reload()
            {
                if (reloaded is not null) return reloaded;
                reloaded = Fresh();
                reload.Add(new Define(helperCall.Address, reloaded, new Load(Fold.Simplify(new Binary(BinOp.Add, argument, Expr.C((ulong)offset, 64), 64)), width)));
                return reloaded;
            }
            if (Merge(head, chain, merge, result is null ? null : subject, v => defs.Expand(new Use(v, 64)) == load ? Reload() : null) is not { } merged) return false;
            var op = new Call(helperCall.Address, CallKind.Direct, helperCall.Target)
            {
                Op = new RuntimeOp(kind, subject is Symbol { Kind: SymbolKind.Class } c ? c.Value : null),
                Arguments = [argument],
            };
            var at = recording ? Start(head, argument) : default;
            if (recording && Location(subject, head, at) is { } where)
                Record(template, head, at, new() { ["merge"] = merge.Start }, new() { ["subject"] = where, ["helper"] = ((Const)helperCall.Target).Value });
            Collapse(head, merge, head, [op, .. reload], merged, branch.Address);
            Remove(chain);
            Result.Hit(template);
            return true;
        }

        /// <summary>
        /// 守卫区域删除之后，merge 中各 φ 只保留跳过一侧（head→merge）的操作数。逐个核对它与区域一侧的取值一致：
        /// 区域一侧是 helper 结果且 helper 返回参数本身（resultEquals）时，跳过一侧必须就是参数；
        /// 区域一侧是对守卫字段的重新读取时，改用 reload 在 helper 之后重新读取；两侧展开后相同则一致；
        /// 都不满足时，若该 φ 没有实际使用（只流向保守约定的调用参数或其他 φ），改为未定义值，否则放弃模板。
        /// 返回 φ 目标 → 新操作数的替换表。
        /// </summary>
        private Dictionary<Variable, Variable>? Merge(Block head, List<Block> chain, Block merge, Expr? resultEquals, Func<Variable, Variable?>? reload)
        {
            var regionIndex = merge.Predecessors.IndexOf(chain[^1]);
            var headIndex = merge.Predecessors.IndexOf(head);
            var regionDefined = Defined(chain);
            var overrides = new Dictionary<Variable, Variable>();
            foreach (var phi in merge.Statements.OfType<Phi>())
            {
                Variable inside = phi.Sources[regionIndex], skipped = phi.Sources[headIndex];
                if (inside == skipped || !regionDefined.Contains(inside)) continue;
                var call = chain.SelectMany(b => b.Statements).OfType<Call>().FirstOrDefault(c => c.Defines.Contains(inside));
                if (call is not null && resultEquals is not null && call.Defines[0] == inside)
                {
                    if (defs.Expand(new Use(skipped, 64)) != resultEquals)
                    {
                        if (Used(phi.Target)) return null;
                        overrides[phi.Target] = new Variable(phi.Target.Storage, -1);
                    }
                    continue;
                }
                if (call is null && reload?.Invoke(inside) is { } fresh)
                {
                    overrides[phi.Target] = fresh;
                    continue;
                }
                if (call is null && defs.Expand(new Use(inside, 64)) == defs.Expand(new Use(skipped, 64))) continue;
                if (Used(phi.Target)) return null;
                overrides[phi.Target] = new Variable(phi.Target.Storage, -1);
            }
            return overrides;
        }

        /// <summary>变量是否有实际使用：经 φ 传递后出现在调用以外的语句中，或作为按签名确定参数的调用的参数。</summary>
        private bool Used(Variable variable)
        {
            var seen = new HashSet<Variable> { variable };
            var work = new Stack<Variable>(seen);
            while (work.Count > 0)
            {
                var v = work.Pop();
                foreach (var stmt in function.Blocks.Where(b => !removed.Contains(b)).SelectMany(b => b.Statements))
                {
                    if (stmt is Phi phi)
                    {
                        if (phi.Sources.Contains(v) && seen.Add(phi.Target)) work.Push(phi.Target);
                        continue;
                    }
                    if (!ExprMap.Operands(stmt).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => u.Variable == v)) continue;
                    if (stmt is not Call call) return true;
                    if (call.Kind is CallKind.Direct or CallKind.Tail && call.Target is Const t && owner.calls.Signature(t.Value) is { } signature)
                    {
                        // 非泛型调用的隐藏 MethodInfo 不参与托管参数语义；泛型调用仍保留实例身份依赖。
                        var methods = facts.EntriesAt(t.Value).Select(e => e.Method).OfType<MethodRef>().ToArray();
                        var hidden = methods.Length > 0 && methods.All(m => m.Method.GenericParameters.Count == 0 && m.Method.Owner.GenericParameters.Count == 0)
                            ? signature.MethodInfo : null;
                        // 只有原生被调方确实读取的参数才保留合并值；未用寄存器可能只是元数据初始化的残值。
                        if (call.Arguments.Where((argument, i) => ExprMap.Walk(argument).OfType<Use>().Any(u => u.Variable == v)
                            && (i >= call.Sources.Length || call.Sources[i] != hidden && !owner.UnusedInput(t.Value, call.Sources[i]))).Any()) return true;
                    }
                    if (ExprMap.Walk(call.Target).OfType<Use>().Any(u => u.Variable == v)) return true;
                }
            }
            return false;
        }

        private static HashSet<Variable> Defined(IEnumerable<Block> blocks)
        {
            var set = new HashSet<Variable>();
            foreach (var stmt in blocks.SelectMany(b => b.Statements))
                switch (stmt)
                {
                    case Define d: set.Add(d.Target); break;
                    case Phi p: set.Add(p.Target); break;
                    case Call c: foreach (var v in c.Defines) if (v is not null) set.Add(v); break;
                }
            return set;
        }

        private void Remove(IEnumerable<Block> blocks) => removed.UnionWith(blocks);

        /// <summary>
        /// 把 head 的终结语句换成 insert + 跳到 merge，删去 head 的其他正常出边（区域由 Cleanup 删除）。
        /// merge 中各 φ 对新边的操作数取 via→merge 边上的操作数（via 为 head 时取原有的 head→merge 边），overrides 优先。
        /// </summary>
        private static void Collapse(Block head, Block merge, Block via, List<Stmt> insert, Dictionary<Variable, Variable>? overrides, ulong address)
        {
            var viaIndex = merge.Predecessors.IndexOf(via);
            if (viaIndex < 0) throw new InvalidOperationException($"{via} 不是 {merge} 的前驱");
            var count = merge.Statements.TakeWhile(s => s is Phi).Count();
            var operands = new Variable[count];
            for (var i = 0; i < count; i++)
            {
                var phi = (Phi)merge.Statements[i];
                operands[i] = overrides is not null && overrides.TryGetValue(phi.Target, out var o) ? o : phi.Sources[viaIndex];
            }
            for (var k = head.NormalSuccessors.Count() - 1; k >= 0; k--) MachineFunction.RemoveEdgeAt(head, k);
            head.Statements.RemoveAt(head.Statements.Count - 1);
            head.Statements.AddRange(insert);
            head.Statements.Add(new Jump(address, merge.Start));
            MachineFunction.AddEdge(head, merge);
            for (var i = 0; i < count; i++)
            {
                var phi = (Phi)merge.Statements[i];
                merge.Statements[i] = phi with { Sources = [.. phi.Sources, operands[i]] };
            }
        }

        // ---------- 抛异常的检查 ----------

        /// <summary>只抛异常的块：除 φ、常量定义与 nop 外只有一个对 Throw 类 helper 的调用，且没有正常后继。</summary>
        private RuntimeHelper? ThrowBlock(Block block)
        {
            if (block.NormalSuccessors.Any() || block.Statements.Count == 0 || block.Statements[^1] is not Call call) return null;
            if (owner.HelperOf(call) is not { Kind: HelperKind.Throw } helper) return null;
            return block.Statements.Take(block.Statements.Count - 1).All(s => s is Phi or Nop or Define { Value: Const }) ? helper : null;
        }

        private bool Checks()
        {
            var changed = false;
            foreach (var head in function.Blocks.ToArray())
            {
                if (removed.Contains(head) || head.Statements.LastOrDefault() is not Branch branch) continue;
                var normal = head.NormalSuccessors.ToArray();
                if (normal.Length != 2 || normal[0] == normal[1]) continue;
                for (var side = 0; side < 2; side++)
                {
                    if (ThrowBlock(normal[side]) is not { } helper || ThrowBlock(normal[1 - side]) is not null) continue;
                    var condition = Fold.Simplify(side == 0 ? branch.Condition : new Not(branch.Condition));
                    var (kind, template, arguments) = (helper.Detail, condition) switch
                    {
                        ("System.NullReferenceException", Compare { Cond: Cond.Eq, Left: { Width: 64 } value, Right: Const { Value: 0 } }) =>
                            (OpKind.NullCheck, Template.NullCheck, new[] { value }),
                        ("System.IndexOutOfRangeException", Compare { Cond: Cond.Uge or Cond.Ugt or Cond.Ule or Cond.Ult } compare) =>
                            (OpKind.BoundsCheck, Template.BoundsCheck, Bounds(compare)),
                        _ => (OpKind.ThrowIf, Template.ThrowIf, new[] { condition }),
                    };
                    var op = new Call(branch.Address, CallKind.Direct, ((Call)normal[side].Statements[^1]).Target)
                    {
                        Op = new RuntimeOp(kind, kind == OpKind.ThrowIf ? helper.Detail : null),
                        Arguments = arguments,
                        NativeExceptionSite = normal[side].Statements[^1].Address,
                    };
                    var at = recording ? Start(head) : default;
                    var throwHelper = ((Const)((Call)normal[side].Statements[^1]).Target).Value;
                    var exits = new Dictionary<string, ulong> { ["throw"] = normal[side].Start, ["pass"] = normal[1 - side].Start };
                    if (recording && kind == OpKind.NullCheck && Placement(defs.Expand(arguments[0]), head, at) is { } where)
                        Record(template, head, at, exits, new() { ["value"] = where, ["helper"] = throwHelper });
                    // 越界：idx ≥u len 时抛出（比较宽度为 width）
                    if (recording && kind == OpKind.BoundsCheck && arguments.Length == 2
                        && Placement(defs.Expand(arguments[0]), head, at) is { } indexAt && Placement(defs.Expand(arguments[1]), head, at) is { } lengthAt)
                        Record(template, head, at, exits, new() { ["index"] = indexAt, ["length"] = lengthAt, ["width"] = arguments[0].Width, ["helper"] = throwHelper });
                    head.Statements[^1] = op;
                    head.Statements.Add(new Jump(branch.Address, normal[1 - side].Start));
                    MachineFunction.RemoveEdgeAt(head, side);
                    Result.Hit(template);
                    changed = true;
                    break;
                }
            }
            return changed;
        }

        /// <summary>越界条件拆成（索引, 长度）：idx ≥u len、idx >u len-1 等形式统一为两个操作数，原条件不能拆时保留条件本身。</summary>
        private static Expr[] Bounds(Compare compare) => compare.Cond switch
        {
            Cond.Uge => [compare.Left, compare.Right],
            Cond.Ule => [compare.Right, compare.Left],
            _ => [compare],
        };

        // ---------- 内联类型检查 ----------

        private Expr? RawDefinition(Expr e) => e is Use { Variable: var v } ? defs.Raw(v) : null;

        private static Expr StripConversions(Expr e) => e is Ir.Convert c ? StripConversions(c.Operand) : e is Extract { Low: 0 } x ? StripConversions(x.Operand) : e;

        /// <summary>
        /// il2cpp_codegen 的 IsInstClass 快速路径（目标类非接口、非 sealed）：
        /// head：klass->typeHierarchyDepth &lt;u T->typeHierarchyDepth 则失败；next：klass->typeHierarchy[T.depth-1] == T 则成功。
        /// 两块换成 t = TypeCheck&lt;T&gt;(klass)；if (t == 0) 失败 else 成功。
        /// </summary>
        private bool TypeChecks()
        {
            var changed = false;
            foreach (var head in function.Blocks.ToArray())
            {
                if (removed.Contains(head) || head.Statements.LastOrDefault() is not Branch branch) continue;
                var normal = head.NormalSuccessors.ToArray();
                if (normal.Length != 2 || normal[0] == normal[1]) continue;
                // 深度比较：Ult(objDepth, typeDepth) 跳到失败一侧（或 Uge 跳到继续一侧）
                if (StripConversions(Fold.Simplify(branch.Condition)) is not Compare { Cond: Cond.Ult or Cond.Uge } depth) continue;
                if (StripConversions(RawDefinition(StripConversions(depth.Left)) ?? depth.Left) is not Load { Width: 8, Address: Binary { Op: BinOp.Add, Right: Const { Value: RuntimeLayout.ClassTypeHierarchyDepth } } objectDepth }) continue;
                var expandedTypeDepth = StripConversions(defs.Expand(depth.Right));
                if (expandedTypeDepth is not Load { Width: 8, Address: Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Class } type, Right: Const { Value: RuntimeLayout.ClassTypeHierarchyDepth } } }) continue;
                var klass = objectDepth.Left;
                var (fail, next) = depth.Cond == Cond.Ult ? (normal[0], normal[1]) : (normal[1], normal[0]);
                if (next.Predecessors.Count != 1 || next.IsLandingPad) continue;
                // 继承链比较：*(klass->typeHierarchy + depth*8 - 8) == T
                var hierarchy = Fold.Simplify(new Load(Fold.Simplify(new Binary(BinOp.Add, defs.Expand(klass), Expr.C(RuntimeLayout.ClassTypeHierarchy, 64), 64)), 64));
                bool IsHierarchyTest(Expr e, out bool equal)
                {
                    equal = false;
                    if (defs.Expand(e) is not Compare { Cond: Cond.Eq or Cond.Ne } c) return false;
                    var (entry, symbol) = c.Right is Symbol ? (c.Left, c.Right) : (c.Right, c.Left);
                    equal = c.Cond == Cond.Eq;
                    return symbol == type && entry is Load { Width: 64 } entryLoad && Terms(entryLoad.Address).Contains(hierarchy);
                }
                var result = Fresh();
                var op = new Call(branch.Address, CallKind.Direct, Expr.C(0, 64))
                {
                    Op = new RuntimeOp(OpKind.TypeCheck, type.Value),
                    Arguments = [klass],
                    Results = [result.Storage],
                    Defines = [result],
                };
                var isType = new Compare(Cond.Ne, new Use(result, 64), Expr.C(0, 64));

                // 形态一：next 以继承链比较分支到成功/失败 → 两块合成一个分支
                if (next.Statements.LastOrDefault() is Branch compare && IsHierarchyTest(compare.Condition, out var equalTaken)
                    && next.Statements.Take(next.Statements.Count - 1).All(s => s is Define or Nop)
                    && next.NormalSuccessors.ToArray() is [var a0, var a1] && a0 != a1 && (a0 == fail || a1 == fail)
                    && (a0 == fail ? a1 : a0).Predecessors.Count == 1)
                {
                    var success = a0 == fail ? a1 : a0;
                    if ((compare.Target == success.Start) != equalTaken || success.Predecessors.Count != 1) continue;
                    // next 中的定义（如转换后的对象）只在成功一侧可能被使用：移到成功块开头
                    var moved = next.Statements.OfType<Define>().Cast<Stmt>().ToList();
                    var at = recording ? Start(head) : default;
                    if (recording && Location(defs.Expand(klass), head, at) is { } klassAt && Location(type, head, at) is { } typeAt)
                        Record(Template.InlineTypeCheck, head, at, new() { ["fail"] = fail.Start, ["success"] = success.Start }, new() { ["klass"] = klassAt, ["type"] = typeAt });
                    if (!Rewire(head, [op], new Branch(branch.Address, new Compare(Cond.Eq, new Use(result, 64), Expr.C(0, 64)), fail.Start, success.Start),
                            [(fail, head), (success, next)], [next])) continue;
                    success.Statements.InsertRange(success.Statements.TakeWhile(s => s is Phi).Count(), moved);
                    Remove([next]);
                }
                // 形态二：next 中以继承链比较作条件（如 as 的 Select）→ 原位替换为 TypeCheck 的结果（next 中深度检查已通过，两者等价）
                else
                {
                    var replaced = false;
                    Expr? Substitute(Expr e)
                    {
                        if (e is not Compare || !IsHierarchyTest(e, out var equal)) return null;
                        replaced = true;
                        return equal ? isType : new Not(isType);
                    }
                    for (var i = 0; i < next.Statements.Count && !replaced; i++)
                        next.Statements[i] = ExprMap.MapOperands(next.Statements[i], e => ExprMap.Map(e, Substitute));
                    if (!replaced) continue;
                    head.Statements.Insert(head.Statements.Count - 1, op);
                    head.Statements[^1] = branch with { Condition = depth.Cond == Cond.Ult ? new Not(isType) : isType };
                }
                Result.Hit(Template.InlineTypeCheck);
                changed = true;
            }
            return changed;
        }

        // castclass 的两个失败分支可能已归一成 ThrowIf；继承深度与继承表检查共同还原为一次类型检查。
        private bool CheckedTypeChains()
        {
            var changed = false;
            foreach (var head in function.Blocks)
                for (var index = 0; index < head.Statements.Count; index++)
                {
                    if (head.Statements[index] is not Call { Op.Kind: OpKind.ThrowIf, Op.Operand: "System.InvalidCastException", Arguments: [Compare { Cond: Cond.Ult } depth] } first
                        || StripConversions(defs.Expand(depth.Left)) is not Load { Width: 8, Address: Binary { Op: BinOp.Add, Right: Const { Value: RuntimeLayout.ClassTypeHierarchyDepth } } objectDepth }
                        || StripConversions(defs.Expand(depth.Right)) is not Load { Width: 8, Address: Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Class } type, Right: Const { Value: RuntimeLayout.ClassTypeHierarchyDepth } } }) continue;
                    var klass = StripConversions(RawDefinition(StripConversions(depth.Left)) ?? depth.Left);
                    var objectClass = klass is Load { Address: Binary { Left: var basis } } ? basis : objectDepth.Left;
                    var hierarchy = new Load(Fold.Simplify(new Binary(BinOp.Add, objectDepth.Left, Expr.C(RuntimeLayout.ClassTypeHierarchy, 64), 64)), 64);
                    foreach (var (block, statement) in Recovery.AllocationPairing.Following(head, index))
                    {
                        if (statement is Define or Nop) continue;
                        if (statement is not Call { Op.Kind: OpKind.ThrowIf, Op.Operand: "System.InvalidCastException", Arguments: [Compare { Cond: Cond.Ne } compare] } second) break;
                        var expanded = defs.Expand(compare);
                        if (expanded is not Compare test || test.Right != type || test.Left is not Load { Width: 64 } item
                            || !Terms(item.Address).Contains(hierarchy)) break;
                        var result = Fresh();
                        head.Statements.Insert(index, new Call(first.Address, CallKind.Direct, Expr.C(0, 64))
                        {
                            Op = new RuntimeOp(OpKind.TypeCheck, type.Value), Arguments = [objectClass], Results = [result.Storage], Defines = [result],
                        });
                        head.Statements[++index] = first with { Arguments = [new Compare(Cond.Eq, new Use(result, 64), Expr.C(0, 64))] };
                        block.Statements[block.Statements.IndexOf(second)] = new Nop(second.Address, "TypeCheck");
                        Result.Hit(Template.InlineTypeCheck);
                        changed = true;
                        break;
                    }
                }
            return changed;
        }

        /// <summary>
        /// 把 head 的终结语句换成 insert + terminator，正常后继改为 targets（顺序与 terminator 一致）。
        /// 每个新边上 φ 的操作数取 via→to 边上的操作数；该操作数定义在 region 中时，只有没有实际使用的 φ 改为未定义值，否则放弃（返回 false，不做改动）。
        /// </summary>
        private bool Rewire(Block head, List<Stmt> insert, Stmt terminator, List<(Block To, Block Via)> targets, List<Block> region)
        {
            var regionDefined = Defined(region);
            var operands = new List<Variable[]>();
            foreach (var (to, via) in targets)
            {
                var index = to.Predecessors.IndexOf(via);
                if (index < 0) return false;
                var phis = to.Statements.TakeWhile(s => s is Phi).Cast<Phi>().ToArray();
                var row = new Variable[phis.Length];
                for (var i = 0; i < phis.Length; i++)
                {
                    var source = phis[i].Sources[index];
                    if (regionDefined.Contains(source))
                    {
                        if (Used(phis[i].Target)) return false;
                        source = new Variable(source.Storage, -1);
                    }
                    row[i] = source;
                }
                operands.Add(row);
            }
            for (var k = head.NormalSuccessors.Count() - 1; k >= 0; k--) MachineFunction.RemoveEdgeAt(head, k);
            head.Statements.RemoveAt(head.Statements.Count - 1);
            head.Statements.AddRange(insert);
            head.Statements.Add(terminator);
            for (var t = 0; t < targets.Count; t++)
            {
                var to = targets[t].To;
                MachineFunction.AddEdge(head, to);
                for (var i = 0; i < operands[t].Length; i++)
                {
                    var phi = (Phi)to.Statements[i];
                    to.Statements[i] = phi with { Sources = [.. phi.Sources, operands[t][i]] };
                }
            }
            return true;
        }

        // ---------- 接口分派 ----------

        private Variable Fresh()
        {
            if (nextTemp < 0)
            {
                var variables = function.Blocks.SelectMany(b => b.Statements).SelectMany(s => s switch
                {
                    Define d => [d.Target], Phi p => p.Sources.Append(p.Target), Call c => c.Defines.Where(v => v is not null), _ => Array.Empty<Variable>(),
                }).Concat(function.Dead.Select(d => d.Define.Target));
                nextTemp = variables.Where(v => v.Storage.Bank == Bank.Temp).Select(v => v.Storage.Index).DefaultIfEmpty(-1).Max() + 1;
            }
            return new Variable(Storage.Temp(nextTemp++), 1);
        }

        private static List<Expr> Terms(Expr e) => e is Binary { Op: BinOp.Add } b ? [.. Terms(b.Left), .. Terms(b.Right)] : [e];

        /// <summary>
        /// il2cpp_codegen_get_interface_invoke_data 内联形态：head 扫描 klass->interfaceOffsets，命中时得到
        /// &amp;klass->vtable[offset + slot]，否则慢路径调用 InterfaceLookup(obj, interface, slot)；两路在 merge 汇合。
        /// </summary>
        private bool InterfaceDispatch()
        {
            var dominators = Dominators.Compute(function);
            var changed = false;
            foreach (var slow in function.Blocks.ToArray())
            {
                if (removed.Contains(slow)) continue;
                var call = slow.Statements.OfType<Call>().FirstOrDefault(c => c.Op is null && owner.HelperOf(c)?.Kind == HelperKind.InterfaceLookup);
                if (call is null || call.Arguments.Length < 3 || call.Results.Length == 0 || call.Results[0] != Storage.Gpr(0) || call.Defines.FirstOrDefault() is not { } result) continue;
                // 慢路径块处于 try 区间时，调用之后另有一个只含跳转的块
                var slowExit = slow;
                while (slowExit.NormalSuccessors.ToArray() is [var only] && only.Predecessors.Count == 1 && only.Statements.All(s => s is Jump or Nop) && only != slow)
                    slowExit = only;
                if (slowExit.NormalSuccessors.ToArray() is not [var merge]) continue;
                var head = function.Blocks[dominators.Idom[merge.Index]];
                if (head == merge || removed.Contains(head) || head.Statements.LastOrDefault() is not Branch) continue;

                var region = new HashSet<Block>();
                var work = new Stack<Block>(head.NormalSuccessors);
                var valid = true;
                while (work.Count > 0 && valid)
                {
                    var b = work.Pop();
                    if (b == merge || b == head || !region.Add(b)) continue;
                    if (!dominators.Dominates(head.Index, b.Index) || region.Count > 32 || b.IsLandingPad) valid = false;
                    foreach (var n in b.NormalSuccessors) work.Push(n);
                }
                if (!valid || !region.Contains(slow) || merge.Predecessors.Contains(head)) continue;
                if (!region.SelectMany(b => b.Statements).All(s => s is Define or Phi or Branch or Jump or Nop || ReferenceEquals(s, call))) continue;
                var fromRegion = merge.Predecessors.Where(region.Contains).Distinct().ToArray();
                if (fromRegion.Length != 2 || merge.Predecessors.Count(region.Contains) != 2 || !fromRegion.Contains(slowExit)) continue;
                var hit = fromRegion.Single(p => p != slowExit);
                int slowIndex = merge.Predecessors.IndexOf(slowExit), hitIndex = merge.Predecessors.IndexOf(hit);
                var phis = merge.Statements.OfType<Phi>().ToList();
                var selected = phis.Where(p => p.Sources[slowIndex] == result).ToList();
                if (selected.Count != 1) continue;
                var regionDefined = Defined(region);
                // 其他 φ 在命中一侧取区域内部的值时，慢路径一侧必须是未定义值（或该 φ 没有实际使用），合并后改为未定义值
                var overrides = new Dictionary<Variable, Variable>();
                var consistent = true;
                foreach (var p in phis.Where(p => p != selected[0] && regionDefined.Contains(p.Sources[hitIndex])))
                {
                    if (p.Sources[slowIndex].Version >= 0 && Used(p.Target)) { consistent = false; break; }
                    overrides[p.Target] = new Variable(p.Target.Storage, -1);
                }
                if (!consistent) continue;
                if (call.Arguments.Take(3).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => regionDefined.Contains(u.Variable))) continue;
                if (defs.Expand(call.Arguments[2]) is not Const slot) continue;
                var target = defs.Expand(call.Arguments[0]);
                // 命中一侧的值 = klass + (offset << 4) + vtable + slot * 16，klass = *obj
                // 槽位或者加在常量里（vtable + slot*16），或者先加到 offset 上再移位（(offset + slot) << 4）
                var terms = Terms(defs.Expand(new Use(selected[0].Sources[hitIndex], 64)));
                var constant = terms.OfType<Const>().Aggregate(0UL, (sum, c) => sum + c.Value);
                var scaled = terms.Where(t => t is not Const && t != new Load(target, 64)).ToList();
                if (!terms.Contains(new Load(target, 64)) || scaled is not [Binary { Op: BinOp.Shl, Right: Const { Value: 4 } } shifted]) continue;
                if (constant != (ulong)RuntimeLayout.VtableMethodPointer((int)slot.Value)
                    && !(constant == (ulong)RuntimeLayout.ClassVtable && slot.Value > 0 && ExprMap.Walk(shifted.Left).Contains(Expr.C(slot.Value, 32)))) continue;

                var iface = defs.Expand(call.Arguments[1]);
                var operand = (iface is Symbol { Kind: SymbolKind.Class } c ? c.Value : null, (int)slot.Value);
                var data = Fresh();
                var op = new Call(call.Address, CallKind.Direct, call.Target)
                {
                    Op = new RuntimeOp(OpKind.InterfaceInvokeData, operand),
                    Arguments = [call.Arguments[0], call.Arguments[1], slot],
                    Results = [data.Storage],
                    Defines = [data],
                };
                var at = recording ? Start(head, call.Arguments[0], call.Arguments[1]) : default;
                if (recording && Location(target, head, at) is { } objectAt && Location(iface, head, at) is { } ifaceAt
                    && selected[0].Target.Storage.Bank == Bank.Gpr)
                    Record(Template.InterfaceDispatch, head, at, new() { ["merge"] = merge.Start }, new()
                    {
                        ["object"] = objectAt, ["interface"] = ifaceAt, ["slot"] = slot.Value,
                        ["result"] = $"x{selected[0].Target.Storage.Index}", ["helper"] = ((Const)call.Target).Value,
                    });
                overrides[selected[0].Target] = data;
                Collapse(head, merge, hit, [op], overrides, call.Address);
                Remove(region);
                interfaceData[data] = operand;
                Result.Hit(Template.InterfaceDispatch);
                changed = true;
            }
            return changed;
        }

        /// <summary>
        /// 接口分派识别时接口类还未符号化（经 RGCTX 的类，在延迟值替换后才成为 Class 符号）：按已符号化的类参数补上
        /// InterfaceInvokeData 与使用其结果的 CallInterface 的接口。
        /// </summary>
        private void RefreshInterfaceOperands()
        {
            var updated = new Dictionary<Variable, (object?, int)>();
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                    if (block.Statements[i] is Call { Op: { Kind: OpKind.InterfaceInvokeData, Operand: ValueTuple<object?, int> { Item1: null } pair } } data
                        && data.Arguments.Length > 1 && defs.Expand(data.Arguments[1]) is Symbol { Kind: SymbolKind.Class } itf && data.Defines is [var result])
                    {
                        var operand = ((object?)itf.Value, pair.Item2);
                        block.Statements[i] = data with { Op = new RuntimeOp(OpKind.InterfaceInvokeData, operand) };
                        interfaceData[result] = operand;
                        updated[result] = operand;
                    }
            if (updated.Count == 0) return;
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                    if (block.Statements[i] is Call { Op: { Kind: OpKind.CallInterface, Operand: ValueTuple<object?, int> { Item1: null } } } call
                        && defs.Expand(call.Target) is Load { Address: var address } && Split(address) is (Use { Variable: var data }, 0) && updated.TryGetValue(data, out var operand))
                        block.Statements[i] = call with { Op = new RuntimeOp(OpKind.CallInterface, operand) };
        }

        // ---------- 单个调用 ----------

        private object? ClassOperand(IEnumerable<Expr> arguments) =>
            arguments.Select(a => defs.Expand(a)).OfType<Symbol>().FirstOrDefault(s => s.Kind == SymbolKind.Class)?.Value;

        private void Calls()
        {
            foreach (var block in function.Blocks)
            {
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Call { Op: null } call) continue;
                    var rewritten = call.Kind is CallKind.Indirect or CallKind.TailIndirect ? Indirect(call) : Direct(block, i, call);
                    if (rewritten is null) continue;
                    // 虚调用：目标 = (*obj)->vtable[n].methodPtr，obj 为第一个参数
                    if (recording && rewritten.Op is { Kind: OpKind.CallVirtual, Operand: int slot } && call.Kind == CallKind.Indirect && call.Arguments.Length > 0)
                    {
                        var (where, at) = (block, Start(block, i, call.Target, call.Arguments[0]));
                        // 处于 try 区间的调用自成一块，目标在唯一前驱中计算：起点放到前驱里
                        if (at.Address == block.Start && block.Predecessors.Distinct().ToArray() is [var previous] && previous.NormalSuccessors.Count() == 1 && !block.IsLandingPad
                            && Start(previous, previous.Statements.Count, call.Target, call.Arguments[0]) is var before && before.Index < previous.Statements.Count)
                            (where, at) = (previous, before);
                        if (Location(defs.Expand(call.Arguments[0]), where, at) is { } objectAt)
                            Record(Template.VirtualCall, where, at, new() { ["call"] = call.Address },
                                new() { ["object"] = objectAt, ["offset"] = (ulong)RuntimeLayout.ClassVtable + (ulong)slot * (ulong)RuntimeLayout.VirtualInvokeDataSize });
                    }
                    block.Statements[i] = rewritten;
                }
            }
        }

        private Call? Direct(Block block, int index, Call call)
        {
            if (owner.HelperOf(call) is not { } helper) return null;
            var args = call.Arguments;
            // 泛型虚方法：helper(klass->vtable[m.slot].method, m)，m 为泛型方法实例；按调用点形态识别（helper 本身没有字符串等证据）
            if (args.Length >= 2 && defs.Expand(args[1]) is Symbol { Kind: SymbolKind.Method, Value: MethodRef generic } && generic.MethodArguments.Count > 0
                && defs.Expand(args[0]) is Load { Width: 64 } slotMethod && Split(slotMethod.Address) is var (vtableBase, vtableOffset)
                && vtableBase is Load { Width: 64 } && vtableOffset == (ulong)RuntimeLayout.VtableMethodInfo(generic.Method.Slot)
                && call.Defines.FirstOrDefault() is { } resolved)
            {
                genericVirtual[resolved] = generic;
                Result.Hit(Template.GenericVirtualCall);
                return call with { Op = new RuntimeOp(OpKind.ResolveGenericVirtual, generic), Arguments = [args[0], args[1]], Sources = [] };
            }
            if (helper.Kind == HelperKind.InitMetadata && args.Length > 0 && defs.Expand(args[0]) is Const slotAddress && facts.Usages.At(slotAddress.Value) is { } slot)
            {
                Result.InitializedSlots.Add(slotAddress.Value);
                Result.Hit(Template.LazyMetadataInit);
                lazyValues.Add((call, new Symbol(SymbolOf(slot.Usage.Kind), slot.Usage.Value)));
                return null;
            }
            Expr Arg(int i) => i < args.Length ? args[i] : Expr.C(0, 64);
            (OpKind Kind, object? Operand, Expr[] Arguments)? op = helper.Kind switch
            {
                HelperKind.ObjectNew => (OpKind.NewObject, ClassOperand([Arg(0)]), [Arg(0)]),
                HelperKind.NewArray or HelperKind.NewArrayFull => (OpKind.NewArray, ClassOperand([Arg(0)]), [Arg(0), Arg(1)]),
                HelperKind.Box => (OpKind.Box, ClassOperand([Arg(0)]), [Arg(0), Arg(1)]),
                HelperKind.Unbox => (OpKind.Unbox, ClassOperand([Arg(0), Arg(1)]), [Arg(0), Arg(1)]),
                HelperKind.IsInst => (OpKind.IsInst, ClassOperand([Arg(0), Arg(1)]), [Arg(0), Arg(1)]),
                HelperKind.IsAssignableFrom => (OpKind.IsAssignableFrom, null, [Arg(0), Arg(1)]),
                HelperKind.ClassInit => (OpKind.RunClassConstructor, ClassOperand([Arg(0)]), [Arg(0)]),
                HelperKind.InitializedTypeInfo => (OpKind.InitClass, ClassOperand([Arg(0)]), [Arg(0)]),
                HelperKind.InitMethodRgctx => (OpKind.InitMethodRgctx, null, [Arg(0)]),
                HelperKind.Raise => (OpKind.Throw, null, [Arg(0)]),
                HelperKind.Throw => (OpKind.ThrowNew, helper.Detail, []),
                HelperKind.NullCheck => (OpKind.NullCheck, null, [Arg(0)]),
                HelperKind.GetException => (OpKind.NewException, helper.Detail, []),
                HelperKind.Rethrow => (OpKind.Rethrow, null, [Arg(0)]),
                HelperKind.MemoryBarrier => (OpKind.MemoryBarrier, null, []),
                HelperKind.CompareExchangeReference => (OpKind.CompareExchangeReference, null, [Arg(0), Arg(1), Arg(2)]),
                HelperKind.Terminate => (OpKind.Terminate, null, []),
                HelperKind.UnwindResume => (OpKind.ResumeUnwind, null, [Arg(0)]),
                HelperKind.FieldAddress => (OpKind.FieldAddress, null, [Arg(0), Arg(1)]),
                HelperKind.ArrayElementAddress => (OpKind.ArrayElementAddress, null, [Arg(0), Arg(1), Arg(2)]),
                HelperKind.Export => (OpKind.Export, helper.Detail, args),
                HelperKind.Import when helper.Detail == "__cxa_begin_catch" => (OpKind.BeginCatch, null, [Arg(0)]),
                HelperKind.Import when helper.Detail == "__cxa_end_catch" => (OpKind.EndCatch, null, []),
                HelperKind.Import => (OpKind.Import, helper.Detail, args),
                HelperKind.WriteBarrier when PrecedingStore(block, index, Arg(0), Arg(1)) => (OpKind.WriteBarrier, null, [Arg(0), Arg(1)]),
                _ => null,
            };
            if (op is not { } found) return null;
            Result.Hit(helper.Kind switch
            {
                HelperKind.WriteBarrier => Template.WriteBarrier,
                HelperKind.Import => Template.ImportCall,
                _ => Template.HelperCall,
            });
            return call with { Op = new RuntimeOp(found.Kind, found.Operand), Arguments = found.Arguments, Sources = [] };
        }

        /// <summary>
        /// 写屏障之前、同一块内（中间没有别的调用）有把 value 写到 address 的 Store；
        /// 或 value 为 0 且有一次清零写入覆盖 address 处的 8 字节（initobj / 结构清零之后对引用字段的屏障）。
        /// </summary>
        private bool PrecedingStore(Block block, int index, Expr address, Expr value)
        {
            // 编译器把各路径的写屏障尾合并到汇合块：参数是本块的 φ，逐个前驱核对对应的写入
            if (block.Statements.Take(index).All(s => s is Phi) && (address is Use { Variable: var pa } || value is Use { Variable: var _ }))
            {
                var phis = block.Statements.Take(index).OfType<Phi>().ToDictionary(p => p.Target);
                Expr Along(Expr e, int j) => e is Use { Variable: var v } && phis.TryGetValue(v, out var phi) ? new Use(phi.Sources[j], e.Width) : e;
                if ((address is Use ua && phis.ContainsKey(ua.Variable)) || (value is Use uv && phis.ContainsKey(uv.Variable)))
                    return block.Predecessors.Count > 0 && block.Predecessors.Select((p, j) => (p, j))
                        .All(x => x.p.NormalSuccessors.Count() == 1 && PrecedingStore(x.p, x.p.Statements.Count, Along(address, x.j), Along(value, x.j)));
            }
            var target = defs.Expand(address);
            var stored = defs.Expand(value);
            var (basis, offset) = Split(target);
            // 处于 try 区间的调用自成一块：沿唯一前驱（其唯一正常后继是本块）继续向前找
            for (var i = index - 1; ; i--)
            {
                if (i < 0)
                {
                    if (block.Predecessors is not [var previous] || previous.NormalSuccessors.Count() != 1) return false;
                    block = previous;
                    i = block.Statements.Count;
                    continue;
                }
                switch (block.Statements[i])
                {
                    case Store store when store.Target == address && store.Value == value:
                        return true;
                    case Store store when defs.Expand(store.Target) == target && defs.Expand(store.Value) == stored:
                        return true;
                    // 值为 0 的屏障跟在结构写入（清零或整体复制）之后：该写入覆盖屏障地址处的 8 字节
                    case Store store when stored is Const { Value: 0 }:
                        var (storeBasis, storeOffset) = Split(defs.Expand(store.Target));
                        var bytes = store.Value.Width / 8;
                        if (target is FrameAddress f && storeBasis is FrameAddress g)
                        {
                            if (g.Offset <= f.Offset && f.Offset + 8 <= g.Offset + bytes) return true;
                        }
                        else if (storeBasis == basis && storeOffset <= offset && offset + 8 <= storeOffset + (ulong)bytes) return true;
                        break;
                    case Call call when call.Op?.Kind != OpKind.WriteBarrier:
                        return false;
                }
            }
        }

        /// <summary>守卫之外的 InitMetadata：调用换成"结果 = 槽位的值"，没有结果时删除；之后再传播一次。</summary>
        private void ReplaceLazy()
        {
            var calls = new Dictionary<Call, Symbol>(ReferenceEqualityComparer.Instance);
            foreach (var (call, symbol) in lazyValues) calls[call] = symbol;
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Call call || !calls.TryGetValue(call, out var value)) continue;
                    if (call.Defines.FirstOrDefault() is { } result) block.Statements[i] = new Define(call.Address, result, value);
                    else block.Statements[i] = new Nop(call.Address, "InitMetadata");
                }
            Result.Errors.AddRange(Lowering.Cleanup(function));
            defs = new Defs(function);
        }

        /// <summary>归一时参数尚未符号化的操作：参数变为 Symbol(Class) 之后补上类型。</summary>
        private void RefreshOperands()
        {
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Call { Op: { Operand: null, Kind: OpKind.InitClass or OpKind.RunClassConstructor or OpKind.NewObject or OpKind.NewArray or OpKind.Box or OpKind.Unbox or OpKind.IsInst } op } call) continue;
                    if (ClassOperand(call.Arguments) is { } type) block.Statements[i] = call with { Op = op with { Operand = type } };
                }
        }

        /// <summary>新建数组的运行时元素类型确定；参数和字段数组可能协变，不能按静态类型替换。</summary>
        private bool ThreadStaticBlocks()
        {
            var changed = false;
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Call { Op: null, Target: Const target, Arguments: [Symbol { Kind: SymbolKind.Class, Value: DefinitionRef type }, ..] } call
                        || call.Defines.FirstOrDefault() is not { } result || facts.Layouts.Of(type)?.ThreadStatics.Count is not > 0
                        || facts.Code.Word(target.Value) != 0xb9411400 || facts.Code.Word(target.Value + 4) is not { } branch || !A64.IsB(branch)) continue;
                    var lookup = A64.Imm26Target(branch, target.Value + 4);
                    // thread_static_fields_offset 的高低 16 位索引经 pthread_getspecific 取得的两级线程表。
                    if (facts.Code.Word(lookup + 16) != 0x53107c13 || facts.Code.Word(lookup + 20) != 0x12003c14
                        || facts.Code.Word(lookup + 32) is not { } get || !A64.IsBl(get)
                        || facts.Code.At(A64.Imm26Target(get, lookup + 32))?.Import != "pthread_getspecific"
                        || facts.Code.Word(lookup + 36) != 0xf8735808 || facts.Code.Word(lookup + 40) != 0xf8745900) continue;
                    block.Statements[i] = new Define(call.Address, result, new Symbol(SymbolKind.ThreadStaticFields, type));
                    changed = true;
                }
            return changed;
        }

        private bool UnboxGuards()
        {
            var changed = false;
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Call { Op.Kind: OpKind.ThrowIf, Op.Operand: "System.InvalidCastException",
                        Arguments: [Compare { Cond: Cond.Ne } compare] } check
                        || defs.Expand(compare.Left) is not Load { Width: 64, Address: Binary { Op: BinOp.Add,
                            Left: Load { Width: 64, Address: var obj }, Right: Const { Value: RuntimeLayout.ClassElementClass } } }
                        || defs.Expand(compare.Right) is not Load { Width: 64, Address: Binary { Op: BinOp.Add,
                            Left: Symbol { Kind: SymbolKind.Class, Value: TypeRef type }, Right: Const { Value: RuntimeLayout.ClassElementClass } } }) continue;
                    var following = block.Statements.Skip(i + 1).Where(s => s is not (Nop or Jump)).ToArray();
                    if (following.Length == 0 && block.NormalSuccessors.ToArray() is [var next] && next.Predecessors.Count == 1)
                        following = next.Statements.Where(s => s is not Nop).ToArray();
                    if (following.FirstOrDefault() is not Call { Op.Kind: OpKind.Unbox, Arguments: [var value, ..] } unbox
                        || !Equals(unbox.Op.Operand, type) || !Equals(defs.Expand(value), obj)) continue;
                    // unbox 在同一位置执行类型与 null 检查，原生 element_class 检查不另造托管字段访问。
                    block.Statements[i] = new Nop(check.Address, "拆箱类型检查");
                    changed = true;
                }
            return changed;
        }

        private bool FreshArrayElementClasses()
        {
            var arrays = function.Blocks.SelectMany(b => b.Statements).OfType<Call>()
                .Where(c => c.Op is { Kind: OpKind.NewArray, Operand: ArrayRef } && c.Defines.Length > 0)
                .ToDictionary(c => c.Defines[0], c => (ArrayRef)c.Op!.Operand!);
            var changed = false;
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Call { Op: { Kind: OpKind.IsInst, Operand: null } op, Arguments: [var value, var type] } call
                        || defs.Expand(type) is not Load { Width: 64, Address: var elementAddress }
                        || Split(elementAddress) is not (Load { Width: 64, Address: Use { Variable: var array } }, RuntimeLayout.ClassElementClass)
                        || !arrays.TryGetValue(array, out var arrayType)) continue;
                    block.Statements[i] = call with { Op = op with { Operand = arrayType.Element },
                        Arguments = [value, new Symbol(SymbolKind.Class, arrayType.Element)] };
                    changed = true;
                }
            return changed;
        }

        private bool DynamicArrayElementChecks()
        {
            var changed = false;
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                    if (block.Statements[i] is Call { Op: { Kind: OpKind.IsInst, Operand: null }, Arguments: [var value, var type] } call
                        && (RawDefinition(type) ?? type) is Load { Width: 64, Address: var elementAddress }
                        && Split(elementAddress) is (Use klass, RuntimeLayout.ClassElementClass)
                        && RawDefinition(klass) is Load { Width: 64, Address: Use array })
                    {
                        block.Statements[i] = call with { Op = new RuntimeOp(OpKind.IsInstArrayElement, null), Arguments = [value, array] };
                        changed = true;
                    }
            return changed;
        }

        /// <summary>Enum.GetValues 的数组读取只产生该枚举的装箱值；不把任意 Array 或 IEnumerator 当作同类来源。</summary>
        private bool EnumElementClasses()
        {
            var results = All.OfType<Call>().Where(c => c.Defines.Length > 0).ToDictionary(c => c.Defines[0]);
            Call? Source(Expr value) => defs.Expand(value) is Use u ? results.GetValueOrDefault(u.Variable) : null;
            bool Named(Call? call, string ownerName, string name) => call is { Op: null, Target: Const target }
                && facts.EntriesAt(target.Value).Any(e => e.Method is { } m && m.Method.Owner.FullName == ownerName && m.Method.Name == name);
            TypeRef? Element(Expr value)
            {
                var current = Source(value);
                Call? array;
                if (Named(current, "System.Array", "GetValue") && current!.Arguments.Length > 0) array = Source(current.Arguments[0]);
                else
                {
                    if (current is not { Op: { Kind: OpKind.CallInterface, Operand: (DefinitionRef { Definition.FullName: "System.Collections.IEnumerator" }, 1) }, Arguments: [var iterator, ..] }) return null;
                    var enumerator = Source(iterator);
                    if (!Named(enumerator, "System.Array", "GetEnumerator") || enumerator!.Arguments.Length == 0) return null;
                    array = Source(enumerator.Arguments[0]);
                }
                if (!Named(array, "System.Enum", "GetValues") || array!.Arguments.Length == 0) return null;
                var type = Source(array.Arguments[0]);
                return Named(type, "System.Type", "GetTypeFromHandle") && type!.Arguments.Length > 0
                    && defs.Expand(type.Arguments[0]) is Symbol { Kind: SymbolKind.Type, Value: DefinitionRef { Definition.IsEnum: true } item } ? item : null;
            }
            var changed = false;
            TypeRef? ElementClass(Expr expression)
            {
                if (defs.Expand(expression) is not Load { Width: 64, Address: var address }) return null;
                return Split(address) switch
                {
                    (Load { Width: 64, Address: var instance }, RuntimeLayout.ClassElementClass) => Element(instance),
                    (Symbol { Kind: SymbolKind.Class, Value: DefinitionRef { Definition.IsEnum: true } type }, RuntimeLayout.ClassElementClass) => type,
                    _ => null,
                };
            }
            Expr? Replace(Expr expression)
            {
                if (expression is not Compare { Cond: Cond.Eq or Cond.Ne } compare
                    || ElementClass(compare.Left) is not { } left || !left.Equals(ElementClass(compare.Right))) return null;
                changed = true;
                return Expr.C(compare.Cond == Cond.Eq ? 1UL : 0, 1);
            }
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                    block.Statements[i] = ExprMap.MapOperands(block.Statements[i], e => ExprMap.Map(e, Replace));
            return changed;
        }

        private Call? Indirect(Call call)
        {
            var target = defs.Expand(call.Target);
            if (target is not Load { Width: 64 } load) return null;
            var expanded = call.Arguments.Select(a => defs.Expand(a)).ToArray();
            var terms = Terms(load.Address);
            var constant = terms.OfType<Const>().Aggregate(0UL, (sum, c) => sum + c.Value);
            var rest = terms.Where(t => t is not Const).ToList();
            RuntimeOp? op = null;
            Template template = default;
            // vtable：target = klass->vtable[n].methodPtr，klass = *obj，obj 为第一个参数，klass->vtable[n].method 作为参数传入
            // MethodInfo* 参数可能未设置（被调用者不读它时编译器省略），所以只要求 this 与 vtable 槽位的形态
            if (rest is [Load { Width: 64 } klass] && constant >= RuntimeLayout.ClassVtable && (constant - RuntimeLayout.ClassVtable) % RuntimeLayout.VirtualInvokeDataSize == 0
                && expanded.Length > 0 && expanded[0] == klass.Address)
            {
                op = new RuntimeOp(OpKind.CallVirtual, (int)((constant - RuntimeLayout.ClassVtable) / RuntimeLayout.VirtualInvokeDataSize));
                template = Template.VirtualCall;
            }
            // 接口：target = data->methodPtr，data 为 InterfaceInvokeData 的结果，data->method 作为参数传入
            else if (rest is [Use { Variable: var data }] && constant == 0 && interfaceData.TryGetValue(data, out var operand))
            {
                op = new RuntimeOp(OpKind.CallInterface, operand);
                template = Template.InterfaceCall;
            }
            else if (rest is [Use { Variable: var resolvedMethod }] && constant == RuntimeLayout.MethodVirtualPointer && genericVirtual.TryGetValue(resolvedMethod, out var gvm))
            {
                op = new RuntimeOp(OpKind.CallGenericVirtual, gvm);
                template = Template.GenericVirtualCall;
            }
            else if (rest.Count == 1 && constant == RuntimeLayout.DelegateInvokeImpl)
            {
                op = new RuntimeOp(OpKind.CallDelegate, null);
                template = Template.DelegateCall;
            }
            // MethodInfo.methodPointer：target = method->methodPointer，method 本身作为参数传入
            else if (constant == RuntimeLayout.MethodPointer && rest.Count == 1 && expanded.Contains(rest[0]))
            {
                op = new RuntimeOp(OpKind.CallMethodPointer, rest[0] is Symbol { Kind: SymbolKind.Method } m ? m.Value : null);
                template = Template.MethodPointerCall;
            }
            if (op is null) return null;
            Result.Hit(template);
            return call with { Op = op };
        }

        // ---------- 残余 ----------

        private void Residuals()
        {
            foreach (var block in function.Blocks)
                foreach (var stmt in block.Statements)
                {
                    if (stmt is Call { Op: null } call)
                    {
                        if (owner.HelperOf(call) is { } helper)
                            Result.Residuals.Add(new(call.Address, $"helper:{helper}", Describe(call)));
                        else if (call.Kind is CallKind.Indirect or CallKind.TailIndirect)
                            Result.Residuals.Add(new(call.Address, $"indirect:{Shape(defs.Expand(call.Target))}", Describe(call)));
                        else if (call.Target is Const target && facts.Code.RegionOf(target.Value) == CodeRegion.Managed && facts.EntriesAt(target.Value).Length == 0)
                        {
                            var identity = facts.Unregistered.At(target.Value);
                            if (identity is null) Result.Residuals.Add(new(call.Address, "call:unregistered-managed", Describe(call)));
                            else if (UnregisteredMethods.Resolve(identity, call, e => defs.Expand(e), owner.abi, out var reason) is null)
                                Result.Residuals.Add(new(call.Address, $"call:unregistered-managed:{reason}", Describe(call)));
                        }
                    }
                    foreach (var load in ExprMap.Operands(stmt).SelectMany(ExprMap.Walk).OfType<Load>())
                        if (Terms(load.Address) is [Symbol { Kind: SymbolKind.Class or SymbolKind.Method or SymbolKind.Field } symbol, Const offset])
                            Result.Residuals.Add(new(stmt.Address, $"load:{symbol.Kind}+0x{offset.Value:x}", stmt.ToString()));
                }
            foreach (var slot in Result.ReadSlots.Except(Result.InitializedSlots))
                Result.Residuals.Add(new(function.Entry, $"slot-read-without-init:{facts.Usages.At(slot)!.Usage.Kind}", $"0x{slot:x} {facts.Usages.At(slot)!.Usage}"));
        }

        private static string Describe(Call call)
        {
            var text = call.ToString();
            return text.Length > 300 ? text[..300] : text;
        }

        /// <summary>表达式的形状：变量与符号以类别代替，只保留结构与常量偏移。</summary>
        private static string Shape(Expr e, int depth = 0) => depth > 6 ? "…" : e switch
        {
            Const c => $"0x{c.Value:x}",
            Use or Ir.Entry => "v",
            Symbol s => s.Kind.ToString(),
            Load l => $"[{Shape(l.Address, depth + 1)}]",
            Binary b => $"({Shape(b.Left, depth + 1)} {b.Op} {Shape(b.Right, depth + 1)})",
            Ir.Convert c => Shape(c.Operand, depth + 1),
            _ => e.GetType().Name,
        };
    }

    /// <summary>定义表：把 SSA 变量展开为定义它的表达式（深度有限），用于比较与形状匹配。</summary>
    private sealed class Defs
    {
        private readonly Dictionary<Variable, Expr> values = new();

        public Defs(MachineFunction function)
        {
            foreach (var stmt in function.Blocks.SelectMany(b => b.Statements))
                if (stmt is Define define) values[define.Target] = define.Value;
            foreach (var (_, define) in function.Dead) values.TryAdd(define.Target, define.Value);
        }

        /// <summary>变量的定义表达式（不展开）；不是 Define 定义的为 null。</summary>
        public Expr? Raw(Variable variable) => values.GetValueOrDefault(variable);

        public Expr Expand(Expr expr, int depth = 8) => depth == 0 ? expr : Fold.Simplify(ExprMap.Map(expr, e =>
            e is Use use && values.TryGetValue(use.Variable, out var value)
                ? Fold.Convert(ConvKind.Truncate, Expand(value, depth - 1), use.Width)
                : null));
    }
}
