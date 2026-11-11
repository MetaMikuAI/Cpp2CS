using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Lowering;

public enum LoweringFailureKind
{
    Binding, State, CallerValue, Call, RuntimeCall, SystemCall, IndirectCall, UnknownCall, AmbiguousCall, FoldedCall, NonReturningCall, ConditionalTrap, Trap, NonFrameRead, NonFrameWrite,
    FloatingOrVector, IndirectControl, Exception, DynamicAllocation, UndefinedValue, UnsupportedAtom, UnsupportedOperation, UnsupportedType, ConstructorInitialization,
}
public sealed record LoweringFailure(LoweringFailureKind Kind, ulong Position, Reason Reason);
public sealed record LoweringResult(ManagedBody? Body, LoweringFailure? Failure);

/// <summary>标量位型的机械下降；绑定与状态查询提供原子的定义，不在下降中猜测来源。</summary>
public sealed partial class IntegerLowering
{
    private readonly NativeFunction function;
    private readonly MethodRef method;
    private readonly MethodBinder binder;
    private readonly ManagedTypes types;
    private readonly StateQueries state;
    private readonly QueryContext context;
    private readonly Dictionary<Term, ManagedValue> arguments = [];
    private readonly Dictionary<(Term Term, int Low, int Width), LocalValue> merges = [];
    private readonly Dictionary<Term, ManagedValue> values = [];
    private readonly Dictionary<BlockIdentity, ulong> labels;
    private readonly Dictionary<MergeIdentity, (Block Block, Merge Merge)> definitions;
    private readonly List<(BlockIdentity Target, LocalValue Local, IReadOnlyList<Incoming> Inputs, int Low, int Width)> pending = [];
    private readonly Dictionary<(BlockIdentity From, BlockIdentity To), List<ManagedCopy>> copies = [];
    private SignatureBinding signature = null!;
    private LoweringFailure? failure;
    private ulong position;
    private int nextLocal;
    private readonly List<ManagedBlock> extraBlocks = [];
    private ulong nextLabel;

    public IntegerLowering(NativeFunction function, MethodRef method, MethodBinder binder, ManagedTypes types,
        Cpp2CS.Native.Images.IImage? image = null, CallNamingQuery? calls = null, ICallEffectSource? effects = null)
    {
        this.function = function; this.method = method; this.binder = binder; this.types = types;
        this.calls = calls;
        state = new(effects, image: image);
        boundSources = new(state);
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
        var bound = binder.Entry(method, kind);
        if (bound.Value is not { } binding)
        { Fail<object>(LoweringFailureKind.Binding, bound.Failure!.Detail); return new(null, failure); }
        signature = binding;
        // 所有事件先检查，避免未使用的调用或访问被纯值下降遗漏。
        foreach (var b in function.Blocks)
        {
            position = b.Trace?.NativeAddress ?? 0;
            if (b.Handler is not null) Fail<object>(LoweringFailureKind.Exception, "异常处理入口尚未下降");
            foreach (var s in b.Statements)
            {
                position = s.Trace?.NativeAddress ?? b.Trace?.NativeAddress ?? 0;
                switch (s)
                {
                    case Call call: PrepareCall(call); break;
                    case TrapWhen: Fail<object>(LoweringFailureKind.ConditionalTrap, "条件陷阱尚未下降"); break;
                    case DynamicAllocation: Fail<object>(LoweringFailureKind.DynamicAllocation, "动态帧分配尚未下降"); break;
                    case MemoryRead r: CheckMemory(r.Address, r.Width, true); break;
                    case MemoryWrite w: CheckMemory(w.Address, w.Width, false); break;
                }
                if (failure is not null) return new(null, failure);
            }
        }
        if (method.Method is { Name: ".ctor", IsStatic: false, Owner.IsValueType: false })
        {
            Fail<object>(LoweringFailureKind.ConstructorInitialization, "引用类型构造函数缺少基类初始化见证");
            return new(null, failure);
        }
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
        if (managed.ThisIndex is { } self) BindParameter(self, -1, method.DeclaringType);
        if (failure is not null) return new(null, failure);
        var blocks = new List<ManagedBlock>();
        foreach (var b in function.Blocks.OrderBy(b => labels[b.Identity]))
        {
            position = b.Trace?.NativeAddress ?? 0;
            var statements = new List<ManagedStatement>();
            for (int i = 0; i < b.Statements.Length; i++)
                if (b.Statements[i] is Call call)
                {
                    position = call.Trace?.NativeAddress ?? b.Trace?.NativeAddress ?? 0;
                    var statement = LowerCall(call, new(b.Identity, i));
                    if (statement is null) return new(null, failure);
                    statements.Add(statement);
                }
            var end = End(b);
            if (end is null) return new(null, failure);
            statements.Add(end);
            blocks.Add(new(labels[b.Identity], statements));
        }
        // 只给实际使用的合流建局部；循环先登记身份，入边随后下降。
        for (int i = 0; i < pending.Count; i++)
        {
            var merge = pending[i];
            foreach (var input in merge.Inputs)
            {
                position = function.Blocks.Single(b => b.Identity == input.Predecessor).Trace?.NativeAddress ?? 0;
                var v = Part(input.Value, merge.Low, merge.Width, IsFloat(merge.Local.Type));
                if (v is null) return new(null, failure);
                var edge = Edge(input.Predecessor, merge.Target);
                ((List<ManagedCopy>)edge.Copies).Add(new(merge.Local, IsFloat(merge.Local.Type) ? FloatBits(v, merge.Local.Width) : Convert(v, merge.Local.Width)));
            }
        }
        // 合流入边也可能首次使用调用结果，全部值下降后再回填结果局部。
        blocks = blocks.Select(b => b with { Statements = b.Statements.Select(s => s is ManagedCall c
            ? c with { Result = callStatements[c].Local } : s).ToArray() }).ToList();
        return new(Materialize(new(method, [.. blocks, .. extraBlocks])), null);
    }

    private void CheckMemory(Term address, int width, bool read)
    {
        var resolved = context.Get(state.Resolve, address);
        if (!resolved.IsSuccess) { Fail<object>(LoweringFailureKind.State, "地址查询失败", resolved.Why); return; }
        var location = context.Get(state.Locations, new(resolved.Value, width));
        if (!location.IsSuccess) Fail<object>(LoweringFailureKind.State, "位置查询失败", location.Why);
        else if (location.Value.Region != Region.Frame && !(read && state.Contents?.Read(function, location.Value) is not null))
            Fail<object>(read ? LoweringFailureKind.NonFrameRead : LoweringFailureKind.NonFrameWrite, "非帧内存访问尚未定位");
    }

    private void BindParameter(int cIndex, int index, TypeRef type)
    {
        var result = binder.Parameter(signature, cIndex, function.Terms, function.Inputs, function.IncomingArgumentArea);
        if (result.Value is not { } bound) { Fail<object>(LoweringFailureKind.Binding, result.Failure!.Detail); return; }
        // 原子按签名定型，槽位未指定的高位不参与绑定。
        if (bound.Source is TermSource source)
            arguments[source.Term] = new ArgumentValue(index, type, source.Term.Width);
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
                var condition = Value(branch.Condition);
                return condition is null ? null : new ManagedBranch(position, condition, Edge(b.Identity, branch.True), Edge(b.Identity, branch.False));
            case Return r:
                if (ManagedTypes.IsVoid(method.Concrete(method.Method.ReturnType))) return new ManagedReturn(position, null);
                var bound = binder.Return(r, signature, function.Terms);
                if (bound.Value?.Source is not TermSource source)
                    return Fail<ManagedStatement>(LoweringFailureKind.Binding, bound.Failure?.Detail ?? "返回值不是标量项");
                var value = Value(source.Term, IsFloat(method.Concrete(method.Method.ReturnType)));
                if (value is null) return null;
                if (IsFloat(method.Concrete(method.Method.ReturnType)))
                    return new ManagedReturn(position, FloatBits(value, source.Term.Width));
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
            case ResumeUnwind: return Fail<ManagedStatement>(LoweringFailureKind.Exception, "继续展开尚未下降");
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
        local = new(new(nextLocal++), floating && width is 32 or 64 ? FloatType(width) : StackType(width), StackWidth(width));
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
