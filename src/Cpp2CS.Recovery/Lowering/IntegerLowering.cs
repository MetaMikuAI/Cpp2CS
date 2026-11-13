using System.Collections.Immutable;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Dispatch;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Lowering;

public enum LoweringFailureKind
{
    Binding, State, CallerValue, Call, RuntimeCall, SystemCall, IndirectCall, UnknownCall, AmbiguousCall, FoldedCall, NonReturningCall, ConditionalTrap, Trap, NonFrameRead, NonFrameWrite,
    FloatingOrVector, IndirectControl, Exception, DynamicAllocation, UndefinedValue, UnsupportedAtom, UnsupportedOperation, UnsupportedType, ConstructorInitialization,
}
public sealed record LoweringFailure(LoweringFailureKind Kind, ulong Position, Reason Reason)
{
    /// <summary>失败所需的结构体类型；仅携带诊断依据，不参与下降判定。</summary>
    public TypeRef? StructType { get; init; }
}
public sealed record LoweringResult(ManagedBody? Body, LoweringFailure? Failure);

/// <summary>标量位型的机械下降；绑定与状态查询提供原子的定义，不在下降中猜测来源。</summary>
public sealed partial class IntegerLowering
{
    private readonly NativeFunction function;
    private readonly MethodRef method;
    private readonly MethodRef? witness;
    private readonly IRgctxDecoder? rgctx;
    private readonly bool nestedExceptions;
    private readonly MethodBinder binder;
    private readonly ManagedTypes types;
    private readonly StateQueries state;
    private QueryContext context;
    private readonly RuntimeSpec? spec;
    private readonly NamingFacts names;
    private ManagedLocationQuery? locations;
    private DispatchQuery? dispatch;
    private readonly AccessorQuery? accessors;
    private readonly ConstructorQuery? constructors;
    private readonly Dictionary<Term, ManagedValue> arguments = [];
    private readonly Dictionary<(Term Term, int Low, int Width), LocalValue> merges = [];
    private readonly Dictionary<Term, ManagedValue> values = [];
    private readonly Dictionary<BlockIdentity, ulong> labels;
    private readonly Dictionary<MergeIdentity, (Block Block, Merge Merge)> definitions;
    private readonly List<(BlockIdentity Target, LocalValue Local, IReadOnlyList<Incoming> Inputs, int Low, int Width)> pending = [];
    private readonly Dictionary<(BlockIdentity From, BlockIdentity To), List<ManagedCopy>> copies = [];
    private SignatureBinding signature = null!;
    private bool hasIndirectParameters;
    private LoweringFailure? failure;
    private ulong position;
    private int nextLocal;
    private readonly List<ManagedBlock> extraBlocks = [];
    private ulong nextLabel;

    public IntegerLowering(NativeFunction function, MethodRef method, MethodBinder binder, ManagedTypes types,
        Cpp2CS.Native.Images.IImage? image = null, CallNamingQuery? calls = null, ICallEffectSource? effects = null, RuntimeSpec? spec = null, NamingFacts? names = null,
        AccessorQuery? accessors = null, ConstructorQuery? constructors = null, MethodRef? witness = null, IRgctxDecoder? rgctx = null,
        bool nestedExceptions = true)
    {
        this.nestedExceptions = nestedExceptions;
        this.function = function; this.method = method; this.witness = witness; this.rgctx = rgctx; this.binder = binder; this.types = types;
        this.calls = calls; this.spec = spec; this.names = names ?? NamingFacts.Empty;
        this.accessors = accessors;
        this.constructors = constructors;
        state = new(effects, image: image);
        boundSources = new(state);
        frameAddressUses = new(state);
        context = state.CreateContext(function);
        labels = function.Blocks.OrderByDescending(b => b.Identity == function.Entry)
            .Select((b, i) => (b.Identity, Label: (ulong)i)).ToDictionary(p => p.Identity, p => p.Label);
        nextLabel = (ulong)labels.Count;
        definitions = function.Blocks.SelectMany(b => b.Merges.Select(m => (Block: b, Merge: m)))
            .ToDictionary(p => p.Merge.Identity);
    }

    private T? Fail<T>(LoweringFailureKind kind, string detail, Reason? cause = null, string? code = null) where T : class
    {
        failure ??= new(kind, position, new(code ?? "lowering." + kind, detail, cause));
        return null;
    }

    public LoweringResult Run(BindingEntryKind kind = BindingEntryKind.Ordinary)
    {
        var bound = binder.Definition(method, kind, witness);
        if (bound.Value is not { } binding)
        { Fail<object>(LoweringFailureKind.Binding, bound.Failure!.Detail, code: GenericWitness.IsGeneric(method.Method) ? "lowering.Generic.Witness" : null); return new(null, failure); }
        signature = binding;
        hasIndirectParameters = binding.Slots.Parameters.Any(p => p.CopyAddress is not null);
        if (method.Method.Parameters.Select(p => method.Concrete(p.Type)).Append(method.Concrete(method.Method.ReturnType))
            .Append(method.DeclaringType).Any(GenericStruct))
        { GenericFailure<object>("Struct", "含类型参数的值类型签名尚未下降"); return new(null, failure); }
        if (spec is not null && calls is not null)
        {
            var naming = new ValueNamingQuery(state, calls, names, spec, binder, signature, rgctx, types.Layouts as GenericWitness, types.Object);
            valueNames = naming;
            locations = new(state, naming, types.Layouts, spec);
            dispatch = new(state, calls, naming, locations, binder, spec, types.Layouts as GenericWitness);
            context = locations.CreateContext(function);
        }
        PrepareExceptions();
        if (failure is not null) return new(null, failure);
        // 所有事件先检查，避免未使用的调用或访问被纯值下降遗漏。
        foreach (var b in function.Blocks)
        {
            SelectExceptionView(b.Identity);
            position = b.Trace?.NativeAddress ?? 0;
            if (exceptions?.Removed.Contains(b.Identity) == true) continue;
            for (int i = 0; i < b.Statements.Length; i++)
            {
                var s = b.Statements[i];
                position = s.Trace?.NativeAddress ?? b.Trace?.NativeAddress ?? 0;
                switch (s)
                {
                    case Call call when exceptions?.PrivateCalls.Contains(call.Identity) != true && exceptions?.Rethrows.ContainsKey(call.Identity) != true: PrepareCall(call, new(b.Identity, i)); break;
                    case TrapWhen: Fail<object>(LoweringFailureKind.ConditionalTrap, "条件陷阱尚未下降"); break;
                    case DynamicAllocation: Fail<object>(LoweringFailureKind.DynamicAllocation, "动态帧分配尚未下降"); break;
                }
                if (failure is not null) return new(null, failure);
            }
        }
        PrepareFrameObjects();
        if (failure is not null) return new(null, failure);
        PairUnboxes();
        if (failure is not null) return new(null, failure);
        var caller = context.Get(state.CallerUses, 0);
        if (!caller.IsSuccess) Fail<object>(LoweringFailureKind.State, "调用方值流向查询失败", caller.Why);
        else if (!caller.Value.IsEmpty)
        {
            var use = caller.Value[0]; position = function.Blocks.Single(b => b.Identity == use.Point.Block).Trace?.NativeAddress ?? 0;
            Fail<object>(LoweringFailureKind.CallerValue, use.Use, use.Reason);
        }
        if (failure is not null) return new(null, failure);
        var managed = signature.Managed!;
        for (int i = 0; i < managed.ParameterIndices.Length; i++) BindParameter(managed.ParameterIndices[i], i, method.Concrete(method.Method.Parameters[i].Type));
        if (managed.ThisIndex is { } self) BindParameter(self, -1, method.Method.Owner.IsValueType ? new ByRefRef(method.DeclaringType) : method.DeclaringType);
        if (failure is not null) return new(null, failure);
        PrepareStructs();
        foreach (var read in function.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>()) RegisterRead(read);
        PairConstructions();
        if (failure is not null) return new(null, failure);
        var blocks = new List<ManagedBlock>();
        foreach (var b in function.Blocks.OrderBy(b => labels[b.Identity]))
        {
            if (exceptions?.Removed.Contains(b.Identity) == true) continue;
            SelectExceptionView(b.Identity);
            position = b.Trace?.NativeAddress ?? 0;
            var statements = new List<ManagedStatement>();
            for (int i = 0; i < b.Statements.Length; i++)
            {
                var native = b.Statements[i];
                position = native.Trace?.NativeAddress ?? b.Trace?.NativeAddress ?? 0;
                if (native is Call call)
                {
                    if (exceptions?.PrivateCalls.Contains(call.Identity) == true) continue;
                    if (exceptions?.Rethrows.ContainsKey(call.Identity) == true)
                    {
                        var rethrow = new ManagedRethrow(position); statements.Add(rethrow);
                        exceptionCallStatements[rethrow] = call.Identity; break;
                    }
                    // 分配并入构造函数调用；接口查找只供分派使用，两者自己不产生语句。
                    if (allocations.TryGetValue(call.Identity, out var allocation))
                    {
                        if (allocation.InlinedConstructor is { } constructor)
                            statements.Add(new ManagedAssignment(position, allocation.Local!, new NewObjectValue(constructor, allocation.Arguments, types.PointerSize * 8) { Transparent = true }));
                        continue;
                    }
                    if (constructorCalls.Contains(call.Identity))
                    {
                        if (call.Identity == constructorInitializationCall)
                            statements.Add(new ManagedCall(position, new(constructorInitialization!.Method!,
                                new ArgumentValue(-1, method.DeclaringType, types.PointerSize * 8), constructorInitialization.Arguments, false), null) { Inlined = true });
                        continue;
                    }
                    if (interfaceLookups.Contains(call.Identity)) continue;
                    var statement = LowerCall(call, new(b.Identity, i));
                    if (statement is null) return new(null, failure);
                    statements.Add(statement);
                    if (FrameCallResult(call) is { } stored) statements.Add(stored);
                    if (failure is not null) return new(null, failure);
                    if (exceptions is not null) exceptionCallStatements[statement] = call.Identity;
                    // 不返回的托管调用之后没有后继；方法体以不可达的 throw null 收尾，依据是不返回分析对被调函数的证明。
                    if (call.DoesNotReturn && statement is ManagedCall)
                        statements.Add(new ManagedThrow(position, new ConstantValue(0, types.Object, types.PointerSize * 8)));
                }
                else if (native is MemoryWrite write)
                {
                    if (constructorWrites.Contains(write.Identity)) continue;
                    if (exceptions?.PrivateWrites.Contains(write.Identity) == true) continue;
                    statements.AddRange(LowerStores(write, new(b.Identity, i)));
                    if (failure is not null) return new(null, failure);
                }
                else if (native is MemoryRead read)
                {
                    if (!readInsertions.TryGetValue(labels[b.Identity], out var slots))
                        readInsertions.Add(labels[b.Identity], slots = []);
                    slots.Add((statements.Count, read.Identity, position));
                }
            }
            if (statements.LastOrDefault() is not (ManagedThrow or ManagedRethrow))
            {
                var end = End(b);
                if (end is null) return new(null, failure);
                statements.Add(end);
            }
            blocks.Add(new(labels[b.Identity], statements));
        }
        // 只给实际使用的合流建局部；循环先登记身份，入边随后下降。
        for (int i = 0; i < pending.Count; i++)
        {
            var merge = pending[i];
            foreach (var input in merge.Inputs)
            {
                position = function.Blocks.Single(b => b.Identity == input.Predecessor).Trace?.NativeAddress ?? 0;
                SelectExceptionView(input.Predecessor);
                var v = Part(input.Value, merge.Low, merge.Width, IsFloat(merge.Local.Type));
                if (v is null) return new(null, failure);
                // 引用值进入非引用的合流局部：这条边的路径事实已证明它为空时就是常量 0（编译器复用了已知为零的值），否则没有托管写法。
                if (ReferenceType(v.Type) && !ReferenceType(merge.Local.Type) && !Opaque(merge.Local.Type))
                {
                    var isNull = function.Terms.Apply(new CoreOperator(CoreOperation.Equal), 1, input.Value, function.Terms.Constant(0, input.Value.Width));
                    var fact = context.Get(new PathFactQuery(state), new PathFactKey(default, isNull, new FlowEdge(input.Predecessor, merge.Target)));
                    if (fact is not { IsSuccess: true, Value: PathTruth.True })
                    {
                        Fail<object>(LoweringFailureKind.UnsupportedType, "托管引用进入整数合流，这条边上没有它为空的路径事实", fact.IsSuccess ? null : fact.Why, "lowering.Merge.Reference");
                        return new(null, failure);
                    }
                    v = Constant(0, merge.Width);
                }
                var incoming = Opaque(merge.Local.Type) || Opaque(v.Type) || ReferenceType(merge.Local.Type) || ManagedTypes.IsNativePointer(merge.Local.Type) ? Coerce(v, merge.Local.Type) : IsFloat(merge.Local.Type) ? FloatBits(v, merge.Local.Width) : Convert(v, merge.Local.Width);
                if (ExceptionCopy(input.Predecessor, merge.Target, merge.Local, incoming)) continue;
                var edge = Edge(input.Predecessor, merge.Target);
                ((List<ManagedCopy>)edge.Copies).Add(new(merge.Local, incoming));
            }
        }
        if (exceptions is not null && arrivals.Keys.Except(exceptionCallStatements.Values).Any())
        {
            Fail<object>(LoweringFailureKind.Exception, "展开状态复制没有对应的托管抛出点，调用已被合并或消去", code: "lowering.Exception.State");
            return new(null, failure);
        }
        blocks = blocks.Select(InsertReads).ToList();
        if (failure is not null) return new(null, failure);
        // 展开合流在调用前赋值；临时局部先求全部源值，保持同时赋值语义。
        if (exceptions is not null) blocks = blocks.Select(b => b with { Statements = b.Statements.SelectMany(s =>
        {
            if (!exceptionCallStatements.TryGetValue(s, out var call) || !arrivals.TryGetValue(call, out var assigned)) return new[] { s };
            var temporaries = assigned.Select(copy => new LocalValue(new(nextLocal++), copy.Target.Type, copy.Target.Width)).ToArray();
            return assigned.Select((copy, i) => (ManagedStatement)new ManagedAssignment(s.Address, temporaries[i], copy.Value) { ExceptionArrival = true })
                .Concat(assigned.Select((copy, i) => (ManagedStatement)new ManagedAssignment(s.Address, copy.Target, temporaries[i]) { ExceptionArrival = true })).Append(s);
        }).ToArray() }).ToList();
        // 合流入边也可能首次使用调用结果，全部值下降后再回填结果局部。
        blocks = blocks.Select(b => b with { Statements = b.Statements.Select(s => s is ManagedCall c && callStatements.TryGetValue(c, out var definition)
            ? c with { Result = definition.Local } : s).ToArray() }).ToList();
        if (failure is not null) return new(null, failure);
        if (method.Method is { Name: ".ctor", IsStatic: false, Owner.IsValueType: false })
        {
            var initialization = constructorInitialization ?? constructors?.Initialization(method, blocks);
            if (initialization?.Failure is { } why)
            {
                position = 0;
                Fail<object>(LoweringFailureKind.ConstructorInitialization, why.Message, why.Cause, why.Code);
                return new(null, failure);
            }
            if (initialization?.Method is { } parent && constructorInitializationCall is null)
            {
                var entry = blocks[0];
                if (constructorInitialization is null)
                    entry = entry with { Statements = entry.Statements.Where((_, i) => !initialization.Writes.Contains(i)).ToArray() };
                blocks[0] = entry with { Statements = new ManagedStatement[] { new ManagedCall(0,
                    new(parent, new ArgumentValue(-1, method.DeclaringType, types.PointerSize * 8), initialization.Arguments, false), null) { Inlined = true } }.Concat(entry.Statements).ToArray() };
            }
            else if (constructors is null && ConstructorQuery.InitializationWitness(method, blocks) != 1)
            {
                position = 0;
                Fail<object>(LoweringFailureKind.ConstructorInitialization, "引用类型构造函数没有唯一的直接 this 初始化调用见证");
                return new(null, failure);
            }
        }
        var body = ExceptionBody([.. blocks, .. extraBlocks]);
        CheckGenericBody(body);
        CheckBody(body);
        return failure is null ? new(Materialize(body), null) : new(null, failure);
    }

    private void BindParameter(int cIndex, int index, TypeRef type)
    {
        var result = binder.Parameter(signature, cIndex, function.Terms, function.Inputs, function.IncomingArgumentArea);
        if (result.Value is not { } bound) { Fail<object>(LoweringFailureKind.Binding, result.Failure!.Detail); return; }
        // 原子按签名定型，槽位未指定的高位不参与绑定。
        if (types.Kind(type) == TypeKind.Struct && bound.Source is IndirectSource indirect)
        {
            var pointer = BoundTerm(indirect.Address, new(function.Entry, 0));
            if (pointer is null) return;
            var resolved = context.Get(state.Resolve, pointer);
            if (!resolved.IsSuccess) { Fail<object>(LoweringFailureKind.Binding, "间接形参地址查询失败", resolved.Why); return; }
            var parameter = new ArgumentValue(index, type, 0);
            indirectParameters.Add(resolved.Value, parameter);
            arguments[resolved.Value] = new AddressValue(parameter, types.PointerSize * 8);
        }
        else if (types.Kind(type) == TypeKind.Struct && bound.Source is { } aggregate)
            structParameters.Add(new(type, aggregate, new(function.Entry, 0), Parameter: index));
        else if (bound.Source is TermSource source)
            arguments[source.Term] = new ArgumentValue(index, type, source.Term.Width);
        else if (bound.Source is { } scalar && scalar is not IndirectSource)
        {
            var value = context.Get(boundSources, new(scalar, new(function.Entry, 0)));
            if (!value.IsSuccess) Fail<object>(LoweringFailureKind.Binding, "栈形参入口值查询失败", value.Why);
            else arguments[value.Value] = new ArgumentValue(index, type, value.Value.Width);
        }
    }

    private ManagedEdge Edge(BlockIdentity from, BlockIdentity to)
    {
        if (!copies.TryGetValue((from, to), out var list)) copies.Add((from, to), list = []);
        return new(labels[to], list);
    }

    private ManagedStatement? End(Block b)
    {
        switch (b.End)
        {
            case Jump j: return new ManagedJump(position, Edge(b.Identity, j.Target));
            case Branch branch:
                if (valueNames is not null && context.Get(state.Resolve, branch.Condition) is { IsSuccess: true } guard
                    && SnapshotRewrite.Dependencies([guard.Value]).Any(t => context.Get(valueNames, t) is
                        { IsSuccess: true, Value.Name: FieldName { Record: "MethodInfo", Field: "MethodInfo.rgctx_data", Owner: var owner } }
                        && valueNames.ContextEntity(owner)))
                    return Fail<ManagedStatement>(LoweringFailureKind.IndirectControl, "已知方法实体的 RGCTX 守卫未能消去，保留原控制流", code: "structure.rgctx-guard");
                var condition = Value(branch.Condition);
                if (condition is not null && Opaque(condition.Type))
                {
                    if (witness is null || !GenericWitness.IsCanonical(witness))
                        return GenericFailure<ManagedStatement>("Arithmetic", "值实例中的类型参数位型不能作为条件");
                    condition = new BoxValue(condition, condition.Type, types.Object, types.PointerSize * 8);
                }
                return condition is null ? null : new ManagedBranch(position, ManagedTypes.IsNativePointer(condition.Type) ? IntegerBits(condition) : condition, Edge(b.Identity, branch.True), Edge(b.Identity, branch.False));
            case Return r:
                if (ManagedTypes.IsVoid(method.Concrete(method.Method.ReturnType))) return new ManagedReturn(position, null);
                var returnType = method.Concrete(method.Method.ReturnType);
                var bound = binder.Return(r, signature, function.Terms, function.Inputs.Select(i => new SlotValue(i.Slot, i.Value)).ToImmutableArray(), function.IncomingArgumentArea);
                if (bound.Value?.Source is TermSource returned && RejectAddressUse([returned.Term], "返回值")) return null;
                if (types.Kind(returnType) == TypeKind.Struct)
                {
                    if (bound.Value?.Source is not { } aggregate) return Fail<ManagedStatement>(LoweringFailureKind.Binding, bound.Failure?.Detail ?? "结构体返回值绑定失败", code: "lowering.Struct.Binding");
                    var structure = StructValue(aggregate, returnType, new(b.Identity, b.Statements.Length));
                    return structure is null ? null : new ManagedReturn(position, structure);
                }
                if (bound.Value?.Source is not TermSource source)
                    return Fail<ManagedStatement>(LoweringFailureKind.Binding, bound.Failure?.Detail ?? "返回值不是标量项");
                var value = Value(source.Term, IsFloat(method.Concrete(method.Method.ReturnType)));
                if (value is null) return null;
                if (IsFloat(method.Concrete(method.Method.ReturnType)))
                    return new ManagedReturn(position, FloatBits(value, source.Term.Width));
                if (Opaque(value.Type) || Opaque(method.Concrete(method.Method.ReturnType)) || ReferenceType(method.Concrete(method.Method.ReturnType)) || ManagedTypes.IsNativePointer(method.Concrete(method.Method.ReturnType)))
                    return new ManagedReturn(position, Coerce(value, method.Concrete(method.Method.ReturnType)));
                value = IntegerBits(value);
                if (!IntegerType(method.Concrete(method.Method.ReturnType))) return Fail<ManagedStatement>(TypeFailure(method.Concrete(method.Method.ReturnType)), "返回类型不是整数");
                return new ManagedReturn(position, new ConversionValue(ManagedTypes.IsSigned(method.Concrete(method.Method.ReturnType)) ? ConversionKind.SignExtend : ConversionKind.ZeroExtend,
                    value, method.Concrete(method.Method.ReturnType), source.Term.Width));
            case JumpTable table:
                var selector = Value(table.Selector);
                if (selector is null) return null;
                selector = IntegerBits(selector);
                ManagedStatement tail = new ManagedJump(position, Edge(b.Identity, table.Default));
                foreach (var item in table.Cases.Reverse())
                {
                    ulong label = nextLabel++;
                    extraBlocks.Add(new(label, [tail]));
                    var test = new ComparisonValue(ComparisonKind.Equal, selector,
                        Constant((ulong)item.Value, table.Selector.Width), types.Boolean);
                    tail = new ManagedBranch(position, test, Edge(b.Identity, item.Target), new(label, []));
                }
                return tail;
            case Unreachable: return Fail<ManagedStatement>(LoweringFailureKind.Trap, "陷阱或不可达终结尚未下降");
            case ResumeUnwind: return Fail<ManagedStatement>(LoweringFailureKind.Exception, "不透明区域仍有继续展开", code: "lowering.Exception.Fault");
            default: return Fail<ManagedStatement>(LoweringFailureKind.IndirectControl, "跳转表或间接控制流尚未下降");
        }
    }

    private LocalValue? MergeValue(Term term, int low = 0, int? requestedWidth = null, bool floating = false)
    {
        int width = requestedWidth ?? term.Width;
        var key = (term, low, width);
        // 首个使用约束决定存储视图；后续不同解释在使用处重解释，不改写已建局部。
        if (merges.TryGetValue(key, out var local)) return local;
        if (width > 64) return Fail<LocalValue>(LoweringFailureKind.FloatingOrVector, "合流位宽超过整数栈宽度");
        var staticType = StaticType(term);
        local = new(new(nextLocal++), staticType is not null && (Opaque(staticType) || ReferenceType(staticType) || low == 0 && width == types.PointerSize * 8 && ManagedTypes.IsNativePointer(staticType)) ? staticType : floating && width is 32 or 64 ? FloatType(width) : StackType(width), StackWidth(width));
        merges.Add(key, local);
        if (term.Identity is ResultAtom { Definition: MergeIdentity id })
        {
            var d = definitions[id]; pending.Add((d.Block.Identity, local, d.Merge.Inputs, low, width));
        }
        else if (term.Identity is MemoryMerge memory)
        {
            var inputs = context.Get(state.MergeInputs, memory);
            if (!inputs.IsSuccess) return Fail<LocalValue>(LoweringFailureKind.State, "内存合流查询失败", inputs.Why);
            pending.Add((memory.Block, local, inputs.Value.Select(e => new Incoming(e.Predecessor, e.Value)).ToArray(), low, width));
        }
        return local;
    }
}
