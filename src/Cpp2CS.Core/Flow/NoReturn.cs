using Cpp2CS.Functions;
using Cpp2CS.Ir;

namespace Cpp2CS.Flow;

/// <summary>
/// 判定被调用者是否不返回。证据来源：导入桩指向已知不返回的外部函数；
/// 调用指令恰好是某函数范围内最后一条指令；在被调用者内找不到一条到达返回的路径。
/// 路径搜索先走不经过调用的边，只在需要时才递归判定路径上的被调用者，所以只触及少量函数。
/// 无法判断的情形（寄存器跳转、顺序执行越界、递归、深度超限）一律按“会返回”处理。
/// </summary>
public sealed class NoReturnOracle(IMachine machine, FunctionTable functions)
{
    private const int MaxDepth = 64;
    private readonly Dictionary<ulong, bool> known = new();
    private readonly Dictionary<ulong, string?> imports = new();
    private readonly List<ulong> stack = [];
    /// <summary>本轮递归中被假设为“会返回”的最浅栈位置；比它深的帧得出的“会返回”不能缓存。</summary>
    private int assumedAt = int.MaxValue;

    private static readonly HashSet<string> NoReturnImports =
    [
        "__cxa_throw", "__cxa_rethrow", "_Unwind_Resume", "__cxa_bad_cast", "__cxa_bad_typeid", "__cxa_throw_bad_array_new_length",
        "__cxa_call_unexpected", "__cxa_pure_virtual", "__cxa_deleted_virtual", "abort", "exit", "_exit", "_Exit", "quick_exit",
        "__stack_chk_fail", "__assert2", "__assert_fail", "__fortify_fail", "pthread_exit", "longjmp", "siglongjmp", "_longjmp",
        "_ZSt9terminatev", "__std_terminate", "_CxxThrowException", "ExitProcess", "_invalid_parameter_noinfo_noreturn",
        "__report_gsfailure", "terminate", "_ZNSt6__ndk122__libcpp_verbose_abortEPKcz",
    ];

    public static bool IsNoReturnName(string name)
    {
        var at = name.IndexOf('@');
        if (at > 0) name = name[..at];
        return NoReturnImports.Contains(name) || name.StartsWith("_ZSt") && name.Contains("__throw_") || name.StartsWith("_ZNSt6__ndk120__throw_");
    }

    public IReadOnlyDictionary<ulong, bool> Known => known;

    /// <summary>为判定而搜索过的函数数（统计用）。</summary>
    public int Analyzed { get; private set; }

    public void AddEvidence(ulong target) => known[target] = true;

    /// <summary>以导入桩开头的函数返回其符号名（PLT 桩，含指向本模块已定义符号的；x64 IAT 跳转）。</summary>
    public string? ImportName(ulong target)
    {
        if (imports.TryGetValue(target, out var cached)) return cached;
        string? name = null;
        var state = new SymbolicState(machine.Convention);
        var address = target;
        for (var i = 0; i < 4; i++)
        {
            var statements = new List<Stmt>();
            var size = machine.Lift(address, statements);
            if (size == 0) break;
            var last = statements.LastOrDefault();
            if (last is IndirectJump jump)
            {
                foreach (var stmt in statements.Take(statements.Count - 1)) state.Step(stmt);
                if (state.Eval(jump.Target) is Load { Address: Const slot } && machine.Image.SymbolSlots.TryGetValue(slot.Value, out var import)) name = import;
                break;
            }
            if (last is Jump or Branch or Call or Return or Trap or Opaque) break;
            foreach (var stmt in statements) state.Step(stmt);
            address += (ulong)size;
        }
        imports[target] = name;
        return name;
    }

    public bool IsNoReturn(ulong target)
    {
        if (known.TryGetValue(target, out var cached)) return cached;
        if (ImportName(target) is { } import) return known[target] = IsNoReturnName(import);
        if (!machine.Image.IsExecutable(target)) return known[target] = false;
        var position = stack.IndexOf(target);
        if (position >= 0)
        {
            assumedAt = Math.Min(assumedAt, position);
            return false;
        }
        // 深度超限：按“会返回”近似，调用帧的结论照常缓存（保守方向）
        if (stack.Count >= MaxDepth) return false;
        var range = functions.At(target);
        if (range is null)
        {
            var next = functions.Next(target);
            range = new FunctionRange(target, next is null ? target + 0x400 : Math.Min(next.Start, target + 0x400), BoundaryEvidence.SymbolCandidate, "无展开表的桩");
        }
        var depth = stack.Count;
        stack.Add(target);
        Analyzed++;
        var result = !Returns(target, range);
        stack.RemoveAt(depth);
        // 假设“会返回”只会增加返回路径，所以“不返回”的结论总成立；“会返回”只在不依赖外层假设时缓存
        if (result || assumedAt >= depth) known[target] = result;
        if (assumedAt >= depth) assumedAt = int.MaxValue;
        return result;
    }

    private bool Returns(ulong entry, FunctionRange range)
    {
        bool InRange(ulong a) => range.Contains(a) || range.Fragments.Any(f => f.Contains(a));
        ulong? PadAt(ulong a)
        {
            foreach (var region in range.ExceptionRegions)
                if (a >= region.Start && a < region.End && region.LandingPad != 0 && InRange(region.LandingPad)) return region.LandingPad;
            return null;
        }

        var seen = new HashSet<ulong>();
        var ready = new Stack<ulong>();
        // 等待判定的调用：(调用之后的地址, 被调用者)；尾调用的“之后”为 null
        var deferred = new Queue<(ulong? After, ulong Callee)>();
        ready.Push(entry);
        var statements = new List<Stmt>();
        while (true)
        {
            while (ready.Count > 0)
            {
                var address = ready.Pop();
                if (!seen.Add(address)) continue;
                statements.Clear();
                var size = machine.Lift(address, statements);
                if (size == 0) continue;
                var next = address + (ulong)size;
                switch (statements[^1])
                {
                    case Return:
                    case IndirectJump:
                    case Call { Kind: CallKind.TailIndirect }:
                        return true;
                    case Trap:
                        break;
                    case Jump jump when InRange(jump.Target):
                        ready.Push(jump.Target);
                        break;
                    case Jump jump:
                        deferred.Enqueue((null, jump.Target));
                        break;
                    case Call { Kind: CallKind.Tail, Target: Const tail }:
                        deferred.Enqueue((null, tail.Value));
                        break;
                    case Branch branch:
                        if (InRange(branch.Target)) ready.Push(branch.Target);
                        else deferred.Enqueue((null, branch.Target));
                        if (!InRange(next)) return true;
                        ready.Push(next);
                        break;
                    case Call call:
                        if (PadAt(address) is { } pad) ready.Push(pad);
                        if (!InRange(next))
                        {
                            // 调用是展开表给出的函数范围内最后一条指令：被调用者不返回
                            if (range.Evidence != BoundaryEvidence.SymbolCandidate && call is { Kind: CallKind.Direct, Target: Const evidence }) known[evidence.Value] = true;
                            break;
                        }
                        if (call is { Kind: CallKind.Direct, Target: Const callee }) deferred.Enqueue((next, callee.Value));
                        else ready.Push(next);
                        break;
                    default:
                        if (!InRange(next)) return true;
                        ready.Push(next);
                        break;
                }
            }
            if (deferred.Count == 0) return false;
            var (after, target) = deferred.Dequeue();
            if (IsNoReturn(target)) continue;
            if (after is null) return true;
            ready.Push(after.Value);
        }
    }
}
