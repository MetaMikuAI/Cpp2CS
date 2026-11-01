namespace Cpp2CS.Tests.Execution;

internal sealed record NativeException(ulong Unwind, ulong Wrapper, ulong Object, ulong TypeInfo);
/// <summary>抽象的 __cxa_allocate_exception / wrapper+0 / __cxa_throw 配对；不伪造 libc++abi 头布局。</summary>
internal sealed class NativeExceptionObjects(ulong start, ulong wrapperType)
{
    private ulong next = start;
    private readonly Dictionary<ulong, (ulong Unwind, ulong? Object)> wrappers = [];
    public ulong Allocate(ulong size)
    {
        if (size != 8) throw new NotSupportedException("本模型只接受 E1 的 8 字节 wrapper");
        var address = next; next = checked(next + 0x40);
        wrappers.Add(address, (address + 0x20, null)); return address;
    }
    public void StoreObject(ulong wrapper, ulong exception)
    {
        if (!wrappers.TryGetValue(wrapper, out var value) || exception == 0) throw new InvalidOperationException("没有分配或异常对象为空");
        wrappers[wrapper] = (value.Unwind, exception);
    }
    public NativeException Throw(ulong wrapper, ulong type, ulong destructor)
    {
        if (type != wrapperType || destructor != 0) throw new NotSupportedException("不在 E1 已证明的抛出域内");
        if (!wrappers.TryGetValue(wrapper, out var value) || value.Object is not { } exception) throw new InvalidOperationException("wrapper 未初始化或重复抛出");
        wrappers.Remove(wrapper);
        return new(value.Unwind, wrapper, exception, type);
    }
}
internal sealed record UnwindFrame(UnwindTable Table, ulong CallSite);
internal sealed record UnwindTransfer(NativeException Exception, int Frame, ulong Landing, long Selector)
{
    public bool Escaped => Landing == 0;
}

/// <summary>
/// 原生展开状态机。依据 Itanium EH ABI 1.3/1.6、2.4/2.5；不查询恢复器区域。
/// 一个 frame 的 cleanup 返回 _Unwind_Resume 后继续上一帧，不能用 Resume 的 PC 重新查当前帧。
/// 同一函数内的外层 selector 门由编译出的正常跳转到达；重新 throw 才从新的调用点搜索。
/// NativeMachine 的适配只安装上下文；落地块里的普通代码继续由 Unicorn 执行。
/// </summary>
[ShapeModel("异常", Basis = "Itanium C++ ABI 的异常处理与 LSDA 格式（IndependentLsda 独立解码，与 L0 交叉核对）；ECMA-335 第 I 部分 12.4.2 节的 try/catch/fault 语义")]
internal sealed class NativeUnwinder
{
    private readonly Stack<NativeException> caught = new();
    private IReadOnlyList<UnwindFrame> frames = [];
    private UnwindTransfer? pending;

    public UnwindTransfer Throw(NativeException exception, IReadOnlyList<UnwindFrame> stack)
    {
        if (pending is not null) throw new InvalidOperationException("正在 cleanup 的展开不能被静默覆盖");
        frames = stack;
        return Continue(exception, 0);
    }

    private UnwindTransfer Continue(NativeException exception, int from)
    {
        for (var i = from; i < frames.Count; i++)
        {
            var site = frames[i].Table.Sites.SingleOrDefault(s => s.Start <= frames[i].CallSite && frames[i].CallSite < s.End);
            // libc++abi scan_eh_tab 对非空 LSDA 中缺失的 call-site 执行 terminate；不能当成 landing=0。
            if (site is null && frames[i].Table.Lsda != 0) throw new InvalidOperationException("LSDA 未覆盖调用点（personality 会 terminate）");
            if (site is null || site.Landing == 0) continue;
            var cleanup = site.ActionOffset == 0;
            foreach (var action in site.Actions)
            {
                if (action.Filter < 0) throw new NotSupportedException("exception specification");
                if (action.Filter == 0) { cleanup = true; continue; }
                if (action.TypeInfo is null) throw new InvalidDataException("未解析的异常类型");
                if (action.TypeInfo == 0 || action.TypeInfo == exception.TypeInfo)
                    return pending = new(exception, i, site.Landing, action.Filter);
            }
            if (cleanup) return pending = new(exception, i, site.Landing, 0);
        }
        pending = null;
        return new(exception, frames.Count, 0, 0);
    }

    public ulong BeginCatch(ulong unwind)
    {
        if (pending is not { Selector: > 0 } transfer || transfer.Exception.Unwind != unwind)
            throw new InvalidOperationException("BeginCatch 没有匹配的 typed/catch-all 展开");
        caught.Push(transfer.Exception); pending = null;
        return transfer.Exception.Wrapper;
    }

    public void EndCatch()
    {
        if (!caught.TryPop(out _)) throw new InvalidOperationException("EndCatch 栈为空");
    }

    public UnwindTransfer Rethrow(IReadOnlyList<UnwindFrame> stack)
    {
        if (!caught.TryPeek(out var exception)) throw new InvalidOperationException("rethrow 不在 catch 中");
        return Throw(exception, stack);
    }

    public UnwindTransfer Resume(ulong unwind)
    {
        if (pending is not { Selector: 0 } transfer || transfer.Exception.Unwind != unwind)
            throw new InvalidOperationException("Resume 没有匹配的 cleanup 展开");
        return Continue(transfer.Exception, transfer.Frame + 1);
    }

    /// <summary>AAPCS64：保留 x19–x29/SP；EH 数据寄存器 x0/x1 由 personality 安装（Itanium 1.6.3）。</summary>
    public static void Install(UnwindTransfer transfer, Action<int, ulong> gpr, Action<int, ulong> vectorLow,
        Action<int, ulong> vectorHigh, Action<ulong> pc, Action<ulong> flags)
    {
        if (transfer.Escaped) throw new InvalidOperationException("离开方法不安装落地上下文");
        for (var i = 0; i <= 18; i++) gpr(i, 0xdead000000000000UL | (uint)i);
        gpr(30, 0xdead00000000001eUL);
        for (var i = 0; i < 32; i++)
        {
            if (i is < 8 or > 15) vectorLow(i, 0xdead000000001000UL | (uint)i);
            vectorHigh(i, 0xdead000000002000UL | (uint)i);
        }
        flags(0xf0000000);
        gpr(0, transfer.Exception.Unwind); gpr(1, unchecked((ulong)transfer.Selector)); pc(transfer.Landing);
    }
}
