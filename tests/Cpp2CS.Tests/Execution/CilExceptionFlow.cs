using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

/// <summary>
/// ECMA-335 I.12.4.2、III.3.35/3.46/4.24：先搜索 catch，再从内到外执行 fault。
/// 保存每个活动 catch 的对象身份；重抛从当前指令的外层 try 搜索，不能重新进入自身 handler。
/// 不读取原生代码、LSDA 或 ManagedRegion，不支持 finally/filter。
/// </summary>
internal sealed class CilExceptionFlow(MethodBody body)
{
    private readonly Dictionary<Instruction, int> positions = body.Instructions.Select((i, n) => (i, n)).ToDictionary(p => p.i, p => p.n);
    private readonly Dictionary<ExceptionHandler, CilThrow> caught = [];
    private readonly Stack<(ExceptionHandler Handler, CilThrow Exception, Queue<ExceptionHandler> Remaining)> faults = [];
    private int End(Instruction? instruction) => instruction is null ? body.Instructions.Count : positions[instruction];
    private bool Contains(Instruction start, Instruction? end, int at) => positions[start] <= at && at < End(end);
    public bool Protected(int at) => body.ExceptionHandlers.Any(h => Contains(h.TryStart, h.TryEnd, at));

    public (int Pc, ulong? Object)? Throw(int at, CilThrow exception, Func<ExceptionHandler, bool> matches)
    {
        foreach (var handler in caught.Keys.Where(h => !Contains(h.HandlerStart, h.HandlerEnd, at)).ToArray()) caught.Remove(handler);
        var candidates = body.ExceptionHandlers.Where(h => Contains(h.TryStart, h.TryEnd, at))
            .OrderBy(h => End(h.TryEnd) - positions[h.TryStart]).ToArray();
        var route = new Queue<ExceptionHandler>();
        foreach (var handler in candidates)
        {
            if (handler.HandlerType == ExceptionHandlerType.Fault) route.Enqueue(handler);
            else if (handler.HandlerType == ExceptionHandlerType.Catch)
            {
                if (!matches(handler)) continue;
                route.Enqueue(handler); break;
            }
            else throw new Unsupported($"异常处理程序 {handler.HandlerType}");
        }
        // ECMA-335 I.12.4.2.5：新异常离开活动 fault 时替换旧展开。只有实际选中的
        // catch 仍在 fault 内，旧展开才挂起；仅有嵌套 try 并不足以证明它能截住新异常。
        var destination = route.LastOrDefault(h => h.HandlerType == ExceptionHandlerType.Catch);
        while (faults.TryPeek(out var active) && (destination is null ||
            !Contains(active.Handler.HandlerStart, active.Handler.HandlerEnd, positions[destination.HandlerStart]))) faults.Pop();
        return Continue(exception, route);
    }

    private (int Pc, ulong? Object)? Continue(CilThrow exception, Queue<ExceptionHandler> route)
    {
        if (!route.TryDequeue(out var handler)) return null;
        if (handler.HandlerType == ExceptionHandlerType.Fault)
        {
            faults.Push((handler, exception, route));
            return (positions[handler.HandlerStart], null);
        }
        caught[handler] = exception;
        return (positions[handler.HandlerStart], exception.Object);
    }

    public (int Pc, ulong? Object)? EndFault(int at, out CilThrow exception)
    {
        if (!faults.TryPop(out var active) || !Contains(active.Handler.HandlerStart, active.Handler.HandlerEnd, at))
            throw new InvalidProgramException("endfinally 不在活动 fault 中");
        exception = active.Exception;
        return Continue(exception, active.Remaining);
    }

    public CilThrow Rethrow(int at) => caught.Where(p => Contains(p.Key.HandlerStart, p.Key.HandlerEnd, at))
        .OrderBy(p => End(p.Key.HandlerEnd) - positions[p.Key.HandlerStart]).Select(p => p.Value).FirstOrDefault()
        ?? throw new InvalidProgramException("rethrow 不在活动 catch 中");

    public void Leave(int target)
    {
        // fault 仅在异常离开时运行；leave 清空求值栈，由解释器完成。
        foreach (var handler in caught.Keys.Where(h => !Contains(h.HandlerStart, h.HandlerEnd, target)).ToArray()) caught.Remove(handler);
    }
}
