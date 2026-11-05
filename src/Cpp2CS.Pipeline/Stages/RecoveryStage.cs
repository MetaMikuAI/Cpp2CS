using System.Diagnostics;
using Cpp2CS.Facts;
using Cpp2CS.Recovery;

namespace Cpp2CS.Pipeline;

internal static class RecoveryStage
{
    internal sealed record RecoveryBatch(MethodDecompiler Recovery, MethodRecoveryResult[] Targets);

    internal static RecoveryBatch RecoverMethods(RecoveryTarget[] selected, ProgramFacts facts, ManagedTypes types, int jobs, Action<string> Log, MethodGuard? guard = null)
    {
        var methods = selected;
        var watch = Stopwatch.StartNew();
        var recovery = new MethodDecompiler(facts, types);
        var targets = new MethodRecoveryResult[methods.Length];
        var completed = 0;
        var active = new System.Collections.Concurrent.ConcurrentDictionary<int, long>();
        using var timer = new Timer(_ =>
        {
            foreach (var (index, started) in active.ToArray().OrderBy(p => p.Key))
            {
                var elapsed = Stopwatch.GetElapsedTime(started).TotalSeconds;
                if (elapsed >= 30) Log($"恢复中 {elapsed:F1} s：0x{selected[index].Entry:x} {selected[index].Instance}");
            }
        }, null, TimeSpan.FromSeconds(30), TimeSpan.FromSeconds(30));
        void Recover(int i, ref MethodDecompiler worker)
        {
            active[i] = Stopwatch.GetTimestamp();
            targets[i] = guard is null ? selected[i].Recover(worker) : guard.Run(selected[i].Method, selected[i].Entry, ref worker, selected[i].Recover);
            active.TryRemove(i, out _);
            var count = Interlocked.Increment(ref completed);
            if (count % 1000 == 0 || count == methods.Length)
                Log($"恢复进度 {count}/{methods.Length}，{watch.Elapsed.TotalSeconds:F1} s");
        }
        Log($"方法恢复并行度：{jobs}");
        if (jobs == 1 && guard is null)
            for (var i = 0; i < methods.Length; i++) Recover(i, ref recovery);
        else
        {
            // 工作线程独享恢复器和分析缓存；结果按原清单索引汇总。
            using var workers = new ThreadLocal<MethodDecompiler>(() => new(facts, types), trackAllValues: true);
            Parallel.For(0, methods.Length, new ParallelOptions { MaxDegreeOfParallelism = jobs }, i =>
            {
                var worker = workers.Value!;
                Recover(i, ref worker);
                workers.Value = worker;
            });
        }
        return new(recovery, targets);
    }
}
