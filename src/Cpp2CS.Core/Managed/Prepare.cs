using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Runtime;
using Cpp2CS.Ssa;

namespace Cpp2CS.Managed;

/// <summary>托管方法在某一架构上的调用约定。</summary>
public interface IManagedAbi
{
    AbiSignature? Classify(MethodRef method, out string? problem);
    /// <summary>独立分类返回值；void 返回 null 且 problem 为空。</summary>
    AbiValue? ClassifyReturn(TypeRef type, out string? problem);
}

/// <summary>直接调用目标的分类。</summary>
public abstract record Callee;

public sealed record HelperCallee(Helper Helper) : Callee;

/// <summary>
/// 托管方法。同一地址可能有多个所有者（共享泛型代码、相同代码折叠），具体是哪一个由调用处决定。
/// Copy 非空表示目标不在方法指针表中、按副本匹配归到这些方法（推测）。
/// </summary>
public sealed record ManagedCallee(IReadOnlyList<CodeOwner> Owners, CopyMatch? Copy) : Callee;

public sealed record UnknownCallee : Callee;

/// <summary>按地址分类调用目标：方法指针表 → 运行时辅助函数 → 托管方法副本（只接受编辑距离不超过 1 的）。</summary>
public sealed class CallResolver(ProgramModel model, RuntimeHelpers helpers, ManagedCopies copies)
{
    private const int CopyDistance = 1;
    private readonly Dictionary<ulong, Callee> cache = new();

    public ProgramModel Model => model;

    public Callee Resolve(ulong target)
    {
        if (cache.TryGetValue(target, out var cached)) return cached;
        Callee result;
        if (model.Code.TryGetValue(target, out var owners) && owners.Count > 0) result = new ManagedCallee(owners, null);
        else if (helpers.Identify(target) is { } helper) result = new HelperCallee(helper);
        else if (copies.Match(target) is { Distance: <= CopyDistance } copy)
        {
            var all = copy.Originals.SelectMany(o => model.Code[o]).Distinct().ToList();
            result = new ManagedCallee(all, copy);
        }
        else result = new UnknownCallee();
        return cache[target] = result;
    }

    public Callee? Resolve(Call call) => call is { Kind: CallKind.Direct or CallKind.Tail, Target: Const target } ? Resolve(target.Value) : null;
}

/// <summary>
/// 托管语义恢复之前对寄存器 SSA 的整理，删去 IL2CPP 运行时样板而不改变托管语义：
/// 1. 按被调用者签名收窄调用的参数与结果，签名之外的结果变量视为已删除（使用处成为 Unknown，φ 中成为未定义值）；
/// 2. 删除元数据初始化（InitMetadata 与方法内的 s_Il2CppMethodInitialized 标志）和写屏障，保留类初始化副作用；
/// 3. 删除通往判空/越界/数组类型不符抛出块的分支；InvalidCastException 抛出块前的 IsInst 标为 castclass；
/// 4. 每轮传播后删除常量分支和两侧等价的分支，按具体边维护 φ；
/// 5. 不逃逸、宽度一致的栈槽提升为 SSA 变量。
/// 依据：IL2CPP 生成代码的固定形态（il2cpp-codegen 的 NullCheck、IL2CPP_RUNTIME_CLASS_INIT、
/// il2cpp_codegen_initialize_runtime_metadata、Il2CppCodeGenWriteBarrier）；判空、越界、协变数组检查
/// 由 IL 指令本身保证；类初始化另行恢复为显式 CLR 初始化，保留调用位置。
/// </summary>
public sealed class Prepare(CallResolver resolver, ManagedCallModel calls, CallingConvention convention)
{
    /// <summary>整理结果：被标为 castclass 的 IsInst 调用地址；提升的栈槽数。</summary>
    public sealed class Result
    {
        public HashSet<ulong> Castclass { get; } = [];
        public int PromotedSlots { get; set; }
    }

    public Result Run(MachineFunction function)
    {
        var result = new Result();
        Narrow(function);
        RemoveRuntime(function);
        Settle(function);
        ClassInitialization.NormalizeGuards(resolver, function);
        Settle(function);
        RemoveThrowEdges(function, result);
        Settle(function);
        RemoveUnusedPure(function, result);
        Settle(function);
        result.PromotedSlots = PromoteFrame(function);
        Settle(function);
        return result;
    }

    /// <summary>删除不可达块、重算支配树并传播清理。</summary>
    private static void Settle(MachineFunction function)
    {
        do
        {
            function.Renumber();
            Propagate.Run(function, Dominators.Compute(function));
        } while (ControlFlow.Simplify(function));
    }

    // ---------- 1. 收窄调用 ----------

    private void Narrow(MachineFunction function)
    {
        var killed = new HashSet<Variable>();
        foreach (var block in function.Blocks)
        {
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call call || call.Sources.Length != call.Arguments.Length) continue;
                if (calls.Shape(call) is not { } shape) continue;
                var (reads, results) = shape;
                var keep = Enumerable.Range(0, call.Sources.Length).Where(k => reads.Contains(call.Sources[k])).ToArray();
                var defines = new List<Variable>();
                var storages = new List<Storage>();
                for (var r = 0; r < call.Results.Length; r++)
                {
                    var define = r < call.Defines.Length ? call.Defines[r] : null;
                    if (results.Contains(call.Results[r]))
                    {
                        storages.Add(call.Results[r]);
                        if (define is not null) defines.Add(define);
                    }
                    else if (define is not null) killed.Add(define);
                }
                block.Statements[i] = call with
                {
                    Arguments = keep.Select(k => call.Arguments[k]).ToArray(),
                    Sources = keep.Select(k => call.Sources[k]).ToArray(),
                    Results = storages.ToArray(),
                    Defines = call.Defines.Length == 0 ? [] : defines.ToArray(),
                };
            }
        }
        Kill(function, killed);
    }

    /// <summary>删除的变量：表达式中的使用成为 Unknown，φ 来源成为未定义值（版本 -1）。</summary>
    private static void Kill(MachineFunction function, HashSet<Variable> killed)
    {
        if (killed.Count == 0) return;
        Expr Rewrite(Expr e) => ExprMap.Map(e, x => x is Use use && killed.Contains(use.Variable) ? new Unknown($"{use.Variable} 已删除", use.Width) : null);
        foreach (var block in function.Blocks)
        {
            for (var i = 0; i < block.Statements.Count; i++)
            {
                block.Statements[i] = block.Statements[i] switch
                {
                    Phi phi when phi.Sources.Any(killed.Contains) => phi with { Sources = phi.Sources.Select(v => killed.Contains(v) ? new Variable(v.Storage, -1) : v).ToArray() },
                    Phi phi => phi,
                    var stmt => ExprMap.MapOperands(stmt, Rewrite),
                };
            }
        }
    }

    // ---------- 2. 运行时样板 ----------

    private void RemoveRuntime(MachineFunction function)
    {
        // 方法初始化标志：按常量地址读出、又按常量地址写入 1 的字节（托管静态字段总经 static_fields 访问，不会是常量地址）
        var loaded = new HashSet<ulong>();
        foreach (var e in function.Blocks.SelectMany(b => b.Statements).SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk))
            if (e is Load { Address: Const address, Width: 8 }) loaded.Add(address.Value);
        var killed = new HashSet<Variable>();
        foreach (var block in function.Blocks)
        {
            var output = new List<Stmt>(block.Statements.Count);
            foreach (var stmt in block.Statements)
            {
                if (stmt is Store { Target: Const flag, Value: Const { Value: 1, Width: 8 } } && loaded.Contains(flag.Value)) continue;
                if (stmt is not Call call || resolver.Resolve(call) is not HelperCallee { Helper: var helper })
                {
                    output.Add(stmt);
                    continue;
                }
                switch (helper.Kind)
                {
                    case HelperKind.ClassInit:
                        output.Add(call with { Results = [], Defines = [] });
                        if (helper.ReturnedArgument is { } argument && call.Defines is [var result])
                        {
                            var index = Array.IndexOf(call.Sources, convention.IntegerArguments[argument]);
                            if (index < 0 || index >= call.Arguments.Length) throw new InvalidOperationException("类初始化返回参数缺少来源");
                            output.Add(new Define(call.Address, result, call.Arguments[index]));
                        }
                        break;
                    case HelperKind.WriteBarrier:
                        killed.UnionWith(call.Defines.Where(v => v is not null));
                        if (call.Kind == CallKind.Tail) output.Add(new Return(call.Address));
                        break;
                    // 返回槽位中的运行时指针（槽位内容在托管语义下视为常量）；返回值通常不用
                    case HelperKind.InitMetadata when call.Kind == CallKind.Direct && call.Arguments.Length == 1 && call.Defines.Length == 1:
                        output.Add(new Define(call.Address, call.Defines[0], new Load(call.Arguments[0], 64)));
                        break;
                    // 判空后原样返回参数：判空由使用处的 IL 指令保证
                    case HelperKind.NullCheck when call.Kind == CallKind.Direct && call.Arguments.Length == 1 && call.Defines.Length == 1:
                        output.Add(new Define(call.Address, call.Defines[0], call.Arguments[0]));
                        break;
                    default:
                        output.Add(stmt);
                        break;
                }
            }
            block.Statements = output;
        }
        Kill(function, killed);
    }

    // ---------- 3. 运行时检查的抛出分支 ----------

    /// <summary>块是否只做运行时检查失败的抛出（判空、越界、数组类型不符、转换失败），返回抛出的异常类型名。</summary>
    private string? CheckThrow(Block block)
    {
        if (block.Successors.Count != 0) return null;
        string? thrown = null;
        foreach (var stmt in block.Statements)
        {
            switch (stmt)
            {
                case Phi or Define or Nop:
                    continue;
                case Call call when resolver.Resolve(call) is HelperCallee { Helper: var helper }:
                    if (thrown is null && helper is { Kind: HelperKind.Throw, Detail: "System.NullReferenceException" or "System.IndexOutOfRangeException" or "System.InvalidCastException" })
                        thrown = helper.Detail;
                    else if (thrown is null && helper is { Kind: HelperKind.GetException, Detail: "System.ArrayTypeMismatchException" })
                        thrown = "";
                    else if (thrown == "" && helper.Kind == HelperKind.Raise)
                        thrown = helper.Detail ?? "System.ArrayTypeMismatchException";
                    else return null;
                    continue;
                default:
                    return null;
            }
        }
        return thrown is "" ? null : thrown;
    }

    private void RemoveThrowEdges(MachineFunction function, Result result)
    {
        var defined = new Dictionary<Variable, Call>();
        foreach (var call in function.Blocks.SelectMany(b => b.Statements).OfType<Call>())
            foreach (var v in call.Defines.Where(v => v is not null)) defined[v] = call;
        foreach (var block in function.Blocks)
        {
            if (block.Statements.Count == 0 || block.Statements[^1] is not Branch branch) continue;
            var normal = block.NormalSuccessors.ToArray();
            if (normal.Length != 2 || normal[0] == normal[1]) continue;
            for (var side = 0; side < 2; side++)
            {
                if (CheckThrow(normal[side]) is not { } thrown) continue;
                if (CheckThrow(normal[1 - side]) is not null) break;
                if (thrown == "System.InvalidCastException")
                {
                    // castclass：r = IsInst(x, K); if (r == null) throw — 抛出侧必须是 r 为空的一侧
                    var nullSide = branch.Condition switch
                    {
                        Compare { Cond: Cond.Eq, Left: Use u, Right: Const { Value: 0 } } => (Use: u, Side: 0),
                        Compare { Cond: Cond.Ne, Left: Use u, Right: Const { Value: 0 } } => (Use: u, Side: 1),
                        _ => (Use: (Use?)null, Side: -1),
                    };
                    if (nullSide.Use is null || nullSide.Side != side || !defined.TryGetValue(nullSide.Use.Variable, out var isInst)
                        || resolver.Resolve(isInst) is not HelperCallee { Helper.Kind: HelperKind.IsInst }) break;
                    result.Castclass.Add(isInst.Address);
                }
                block.Statements[^1] = new Jump(branch.Address, normal[1 - side].Start);
                MachineFunction.RemoveEdge(block, normal[side]);
                break;
            }
        }
    }

    // ---------- 纯辅助调用 ----------

    /// <summary>结果无人使用的纯辅助调用（类型检查、取异常对象）；castclass 结果不用时只能是写屏障宏重复求值的那一次。</summary>
    private void RemoveUnusedPure(MachineFunction function, Result result)
    {
        var used = new HashSet<Variable>();
        foreach (var stmt in function.Blocks.SelectMany(b => b.Statements))
        {
            if (stmt is Phi phi) used.UnionWith(phi.Sources);
            else foreach (var e in ExprMap.Operands(stmt).SelectMany(ExprMap.Walk)) if (e is Use u) used.Add(u.Variable);
        }
        foreach (var block in function.Blocks)
            block.Statements.RemoveAll(s => s is Call call && call.Defines.All(v => v is null || !used.Contains(v)) && call.Kind == CallKind.Direct
                && resolver.Resolve(call) is HelperCallee { Helper.Kind: HelperKind.IsInst or HelperKind.IsAssignableFrom or HelperKind.GetException or HelperKind.InitMetadata });
    }

    // ---------- 5. 栈槽提升 ----------

    /// <summary>
    /// 提升入口 SP 以下、只以同一宽度按 FrameAddress 直接读写、且不在逃逸区内的槽位。
    /// 逃逸区：地址被当作值使用的 FrameAddress(e) 起，到下一个逃逸地址或下一个保存入口寄存器值的槽位为止
    /// （被调用者保存寄存器存在帧顶，局部变量在其下；逃逸对象的大小未知，按此保守估计）。
    /// </summary>
    private int PromoteFrame(MachineFunction function)
    {
        var widths = new Dictionary<long, HashSet<int>>();
        var escapes = new SortedSet<long>();
        var boundaries = new SortedSet<long>();
        void Visit(Expr e)
        {
            switch (e)
            {
                case Load { Address: FrameAddress frame } load:
                    Access(frame.Offset, load.Width);
                    return;
                case FrameAddress frame:
                    escapes.Add(frame.Offset);
                    return;
            }
            foreach (var child in ExprMap.Children(e)) Visit(child);
        }
        void Access(long offset, int width)
        {
            if (!widths.TryGetValue(offset, out var set)) widths[offset] = set = [];
            set.Add(width);
        }
        var arguments = convention.IntegerArguments.Concat(convention.FloatArguments).ToHashSet();
        foreach (var stmt in function.Blocks.SelectMany(b => b.Statements))
        {
            if (stmt is Store { Target: FrameAddress frame } store)
            {
                Access(frame.Offset, store.Value.Width);
                if (store.Value is Use { Variable.Version: 0 } entry && !arguments.Contains(entry.Variable.Storage)) boundaries.Add(frame.Offset);
                Visit(store.Value);
            }
            else foreach (var operand in ExprMap.Operands(stmt)) Visit(operand);
        }

        var promoted = new HashSet<long>();
        var ordered = widths.Keys.Order().ToArray();
        for (var k = 0; k < ordered.Length; k++)
        {
            var offset = ordered[k];
            if (offset >= 0 || widths[offset].Count != 1) continue;
            var bytes = widths[offset].Single() / 8;
            if (bytes == 0) continue;
            if (k + 1 < ordered.Length && ordered[k + 1] < offset + bytes) continue;
            if (k > 0 && ordered[k - 1] + widths[ordered[k - 1]].Max() / 8 > offset) continue;
            if (Escaped(offset)) continue;
            promoted.Add(offset);
        }
        bool Escaped(long offset)
        {
            var escape = escapes.GetViewBetween(long.MinValue, offset);
            if (escape.Count == 0) return false;
            var start = escape.Max;
            if (start == offset) return true;
            var end = Math.Min(escapes.GetViewBetween(start + 1, long.MaxValue).DefaultIfEmpty(0).Min(), boundaries.GetViewBetween(start + 1, long.MaxValue).DefaultIfEmpty(0).Min());
            return offset < end;
        }
        if (promoted.Count == 0) return 0;

        Expr Rewrite(Expr e) => ExprMap.Map(e, x => x is Load { Address: FrameAddress frame } load && promoted.Contains(frame.Offset) ? new Read(Storage.Slot((int)frame.Offset), load.Width) : null);
        foreach (var block in function.Blocks)
        {
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var stmt = block.Statements[i];
                block.Statements[i] = stmt is Store { Target: FrameAddress frame } store && promoted.Contains(frame.Offset)
                    ? new Assign(store.Address, Storage.Slot((int)frame.Offset), Rewrite(store.Value))
                    : ExprMap.MapOperands(stmt, Rewrite);
            }
        }
        var dominators = Dominators.Compute(function);
        SsaBuilder.Build(function, dominators, s => s.Bank == Bank.Stack, new ConservativeCallModel(convention), convention.StackPointer);
        Propagate.Run(function, dominators);
        return promoted.Count;
    }
}
