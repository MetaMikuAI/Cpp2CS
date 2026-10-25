using Cpp2CS.Facts;

namespace Cpp2CS.Tests.Execution;

internal sealed partial class NativeMachine
{
    private Dictionary<ulong, UnwindTable>? unwindTables;
    private NativeUnwinder unwinder = new();
    private NativeExceptionObjects exceptionObjects = null!;
    private ulong wrapperType;
    // libc++abi 私有头不映射成托管对象；保留一段独立的、不可观察的原生 scratch 区。
    private const ulong WrapperBase = World.StackBase + 0x1000;
    private (ulong Site, ulong Sp, ulong[] Saved, ulong[] Floats)? helperFrame;

    private void EnterHelperFrame() => helperFrame ??= (uc.Reg(Unicorn.X(30)) - 4, uc.Reg(Unicorn.RegSp),
        Enumerable.Range(19, 11).Select(i => uc.Reg(Unicorn.X(i))).ToArray(),
        Enumerable.Range(8, 8).Select(i => uc.Reg(Unicorn.D(i))).ToArray());

    private void ResetUnwind()
    {
        unwindTables ??= IndependentLsda.ReadImage(facts.Model.Image).ToDictionary(t => t.Start);
        if (wrapperType == 0)
            wrapperType = unwindTables.Values.SelectMany(t => t.Sites).SelectMany(s => s.Actions).Select(a => a.TypeInfo)
                .OfType<ulong>().Where(t => t != 0).Distinct().Single(t => ExceptionFacts.TypeName(facts.Model.Image, t) == ExceptionFacts.WrapperName);
        unwinder = new NativeUnwinder();
        exceptionObjects = new NativeExceptionObjects(WrapperBase, wrapperType);
        helperFrame = null;
    }

    private IReadOnlyList<UnwindFrame> ExceptionFrames()
    {
        var site = uc.Reg(Unicorn.X(30)) - 4;
        if (helperFrame is { } frame && !function.Contains(site))
        {
            // AAPCS64 的 callee-saved 契约：从普通 helper 展开回被测帧，恢复调用时的保存寄存器和 SP。
            // 仅捕获 helper 入口状态；不从被测方法的指令猜 CFI。
            site = frame.Site;
            uc.SetReg(Unicorn.RegSp, frame.Sp);
            for (var i = 0; i < frame.Saved.Length; i++) uc.SetReg(Unicorn.X(19 + i), frame.Saved[i]);
            for (var i = 0; i < frame.Floats.Length; i++) uc.SetReg(Unicorn.D(8 + i), frame.Floats[i]);
            helperFrame = null;
        }
        if (!function.Contains(site))
        {
            // 真尾调用已释放本帧，方法外的哨兵没有本帧落地块。
            if (site + 4 == World.Sentinel) return [];
            throw new Unsupported($"异常展开 调用点不在被测帧 0x{site:x}");
        }
        return [new(unwindTables!.GetValueOrDefault(function.Start) ?? new UnwindTable(function.Start, function.End, 0, 0, []), site)];
    }

    private void RaiseObject(ulong value)
    {
        if (value == 0) value = side.ExceptionObject(side.World.Types.Corlib("System.NullReferenceException"));
        var wrapper = exceptionObjects.Allocate(8);
        side.Synthesized(wrapper, StructAbi.Bytes(value, 8));
        exceptionObjects.StoreObject(wrapper, value);
        Transfer(unwinder.Throw(exceptionObjects.Throw(wrapper, wrapperType, 0), ExceptionFrames()));
    }

    private void Transfer(UnwindTransfer transfer)
    {
        if (transfer.Escaped) { side.ThrowObject(transfer.Exception.Object); uc.Stop(); return; }
        // Qn 的上半部同时置毒，Dn 的 callee-saved 下半部按 AAPCS64 保留。
        NativeUnwinder.Install(transfer, (i, v) => uc.SetReg(Unicorn.X(i), v),
            (i, v) => uc.SetReg(Unicorn.D(i), v), (i, v) => uc.SetVectorHigh(i, v),
            v => uc.SetReg(Unicorn.RegPc, v), v => uc.SetReg(Unicorn.RegNzcv, v));
    }

    private bool ExceptionHelper(RuntimeHelper helper)
    {
        ulong X(int i) => uc.Reg(Unicorn.X(i));
        switch (helper.Kind)
        {
            case HelperKind.Raise or HelperKind.Rethrow: RaiseObject(X(0)); return true;
            case HelperKind.Throw: RaiseObject(side.ExceptionObject(side.World.Types.Corlib(helper.Detail!))); return true;
            case HelperKind.UnwindResume: Transfer(unwinder.Resume(X(0))); return true;
            case HelperKind.Terminate: throw new InvalidDataException("异常展开 可达 terminate，不能当成托管异常离开");
            case HelperKind.Import:
                switch (helper.Detail)
                {
                    case "__cxa_allocate_exception": uc.SetReg(Unicorn.X(0), exceptionObjects.Allocate(X(0))); Back(); return true;
                    case "__cxa_throw":
                        exceptionObjects.StoreObject(X(0), side.Read64(X(0)));
                        Transfer(unwinder.Throw(exceptionObjects.Throw(X(0), X(1), X(2)), ExceptionFrames())); return true;
                    case "__cxa_begin_catch": uc.SetReg(Unicorn.X(0), unwinder.BeginCatch(X(0))); Back(); return true;
                    case "__cxa_end_catch": unwinder.EndCatch(); Back(); return true;
                    case "__cxa_rethrow": Transfer(unwinder.Rethrow(ExceptionFrames())); return true;
                    case "_Unwind_Resume": Transfer(unwinder.Resume(X(0))); return true;
                }
                break;
        }
        return false;
    }
}
