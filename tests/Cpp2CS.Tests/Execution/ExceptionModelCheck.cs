using System.Buffers.Binary;

namespace Cpp2CS.Tests.Execution;

/// <summary>手写 LSDA 和抽象帧，不取任何被测方法的机器码或恢复后的区域作为预期。</summary>
internal static class ExceptionModelCheck
{
    [Command("eh-unit", "手写 LSDA 和展开状态机边界检查", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        foreach (var large in new[] { false, true })
        {
            // offset 相对 ULEB128 结束位置。两字节的 130 是旧基址错误的定向回归。
            var bytes = new byte[256];
            var prefix = large ? new byte[] { 0xff, 0, 0x82, 1, 1, 4, 0, 4, 32, 1, 1, 0 }
                : new byte[] { 0xff, 0, 16, 1, 4, 0, 4, 32, 1, 1, 0 };
            prefix.CopyTo(bytes, 0);
            var typeBase = large ? 134 : 19;
            BinaryPrimitives.WriteUInt64LittleEndian(bytes.AsSpan(typeBase - 8), 0x5678);
            var reader = new IndependentLsda.Reader((at, n) => bytes.AsSpan((int)at, n).ToArray(), at => BinaryPrimitives.ReadUInt64LittleEndian(bytes.AsSpan((int)at)));
            var table = IndependentLsda.Read(reader, 0, 0x1000, 0x1100);
            a.Equal(0x5678UL, table.Sites[0].Actions[0].TypeInfo!.Value, $"LSDA 类型基址（{(large ? 2 : 1)} 字节 ULEB128）");
            a.Equal(0x1020UL, table.Sites[0].Landing, "相对 LPStart");
        }
        var chain = new byte[128];
        new byte[] { 0xff, 0x9c, 37, 1, 4, 0, 4, 32, 5, 0, 0, 2, 0x7d, 1, 0x7d }.CopyTo(chain, 0);
        BinaryPrimitives.WriteInt64LittleEndian(chain.AsSpan(32), 96 - 32);
        BinaryPrimitives.WriteUInt64LittleEndian(chain.AsSpan(96), 0x5678);
        IndependentLsda.Reader ChainReader() => new((at, n) => chain.AsSpan((int)at, n).ToArray(), at => BinaryPrimitives.ReadUInt64LittleEndian(chain.AsSpan((int)at)));
        var decoded = IndependentLsda.Read(ChainReader(), 0, 0x1000, 0x1100);
        a.True(decoded.Sites[0].Actions.Select(s => s.Filter).SequenceEqual(new long[] { 1, 2, 0 }), "带负偏移的 action 链顺序");
        a.Equal(0x5678UL, decoded.Sites[0].Actions[0].TypeInfo!.Value, "pcrel signed64 indirect 类型指针");
        a.Equal("catch-all", decoded.Sites[0].Actions[1].Kind, "空类型指针是 catch-all");
        chain[12] = 1;
        var cycleRejected = false;
        try { _ = IndependentLsda.Read(ChainReader(), 0, 0x1000, 0x1100); } catch (InvalidDataException) { cycleRejected = true; }
        a.True(cycleRejected, "拒绝 action 环");

        const ulong wrapperType = 0x5678;
        var exception = new NativeException(0x10000, 0x10020, 0x20000, wrapperType);
        UnwindAction Action(long filter, ulong? type) => new(0, filter, 0, null, type);
        UnwindFrame Frame(ulong call, ulong landing, params UnwindAction[] actions) =>
            new(new(0x1000, 0x2000, 1, 0, [new(0x1100, 0x1104, landing, actions.Length == 0 ? 0UL : 1UL, actions), new(0x1104, 0x1108, 0, 0, [])]), call);

        var unwinder = new NativeUnwinder();
        var caught = unwinder.Throw(exception, [Frame(0x1100, 0x1200, Action(0, null), Action(1, wrapperType), Action(2, 0))]);
        a.Equal(1L, caught.Selector, "cleanup 后继续搜索，首个匹配的 typed action");
        a.Equal(exception.Wrapper, unwinder.BeginCatch(exception.Unwind), "BeginCatch 返回 wrapper，不返回异常对象");
        var rethrow = unwinder.Rethrow([Frame(0x1100, 0x1300), Frame(0x1100, 0x1400, Action(1, wrapperType))]);
        a.Equal(0L, rethrow.Selector, "重抛可以进入 cleanup");
        unwinder.EndCatch();
        var outer = unwinder.Resume(exception.Unwind);
        a.Equal(0x1400UL, outer.Landing, "Resume 继续上一帧而非按 Resume PC 重入原 cleanup");
        a.Equal(exception.Object, outer.Exception.Object, "重抛保留托管对象身份");
        _ = unwinder.BeginCatch(exception.Unwind); unwinder.EndCatch();
        var all = unwinder.Throw(exception, [Frame(0x1103, 0x1200, Action(1, 0x9999), Action(2, 0))]);
        a.Equal(2L, all.Selector, "不匹配的 typed action 后进入 catch-all");
        _ = unwinder.BeginCatch(exception.Unwind); unwinder.EndCatch();
        var cleanup = unwinder.Throw(exception, [Frame(0x1100, 0x1200, Action(0, null))]);
        a.Equal(0L, cleanup.Selector, "只有 cleanup 的 action 链");
        a.True(unwinder.Resume(exception.Unwind).Escaped, "最外层 cleanup 完成后离开方法");
        a.True(unwinder.Throw(exception, [Frame(0x1104, 0x1200)]).Escaped, "调用区间右边界不命中");
        a.True(unwinder.Throw(exception, [Frame(0x1100, 0)]).Escaped, "landing=0 向外传播");
        var at = unwinder.Throw(exception, [Frame(0x1100, 0x1200, Action(1, wrapperType))]);
        var gpr = Enumerable.Repeat(7UL, 32).ToArray(); var lo = Enumerable.Repeat(7UL, 32).ToArray(); var hi = (ulong[])lo.Clone();
        ulong pc = 0, flags = 0;
        NativeUnwinder.Install(at, (i, v) => gpr[i] = v, (i, v) => lo[i] = v, (i, v) => hi[i] = v, v => pc = v, v => flags = v);
        a.True(gpr.Skip(19).Take(11).All(v => v == 7) && gpr[31] == 7, "x19–x29 与 SP 不变");
        a.True(gpr.Skip(2).Take(17).All(v => v != 7) && gpr[30] != 7, "调用者保存的 GPR 写毒值");
        a.True(lo.Skip(8).Take(8).All(v => v == 7) && hi.All(v => v != 7), "v8–v15 只保留低 64 位");
        a.Equal(exception.Unwind, gpr[0], "x0 为 unwind 异常"); a.Equal(1UL, gpr[1], "x1 为选择子");
        a.Equal(at.Landing, pc, "PC 为落地地址"); a.True(flags != 0, "NZCV 失效");
        bool Reject(Action operation) { try { operation(); return false; } catch (InvalidOperationException) { return true; } }
        a.True(Reject(() => unwinder.Resume(exception.Unwind)), "typed catch 不能冒充 cleanup 恢复展开");
        a.True(Reject(() => unwinder.BeginCatch(0)), "拒绝错误 unwind 指针");
        var missing = new NativeUnwinder();
        a.True(Reject(() => missing.Throw(exception, [Frame(0x1110, 0x1200)])), "缺失 call-site 不能伪装成无落地块");
        var objects = new NativeExceptionObjects(0x30000, wrapperType);
        var first = objects.Allocate(8); objects.StoreObject(first, exception.Object);
        var raised = objects.Throw(first, wrapperType, 0);
        var second = objects.Allocate(8); objects.StoreObject(second, exception.Object);
        var raisedAgain = objects.Throw(second, wrapperType, 0);
        a.True(raised.Wrapper != raisedAgain.Wrapper && raised.Unwind != raisedAgain.Unwind, "内联重抛可以重新分配 wrapper");
        a.Equal(raised.Object, raisedAgain.Object, "新 wrapper 不改变托管异常对象身份");
        a.True(Reject(() => objects.Throw(first, wrapperType, 0)), "不重复消费同一 allocate");
        var empty = objects.Allocate(8);
        a.True(Reject(() => objects.Throw(empty, wrapperType, 0)), "allocate 后必须写 wrapper+0");
        return a.Finish("eh-unit");
    }
}
