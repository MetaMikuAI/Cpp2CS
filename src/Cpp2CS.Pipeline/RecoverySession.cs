namespace Cpp2CS.Pipeline;

/// <summary>按 profile 的阶段表（<see cref="StageTables"/>）运行一次恢复。</summary>
public static class RecoverySession
{
    public static RecoveryRunResult Run(RecoveryRequest request, Action<string>? progress = null)
    {
        request.Validate();
        var run = new RecoveryRun(request, progress, new RunManifest(request));
        foreach (var stage in StageTables.For(request.Profile)) stage.Run(run);
        run.Manifest!.Complete(run.Outcome);
        return run.Outcome;
    }

    /// <summary>
    /// 按请求的 profile 重新运行到写出为止（不写文件、不建运行清单）。执行对照用它复现产物所属 profile 的写出，
    /// 再与磁盘上的 CIL 逐项比较。
    /// </summary>
    internal static RecoveryRun Emit(RecoveryRequest request, Action<string>? progress = null)
    {
        request.Validate();
        var run = new RecoveryRun(request, progress, null);
        foreach (var stage in StageTables.For(request.Profile).TakeWhile(s => !s.Writes)) stage.Run(run);
        return run;
    }
}
