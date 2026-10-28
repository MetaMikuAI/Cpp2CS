using System.Diagnostics;
using System.Text;
using System.Text.Encodings.Web;
using System.Text.Json;
using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;

namespace Cpp2CS.Pipeline;

public static partial class RecoverySession
{
    private sealed record RecoveryBatch(MethodRecovery Recovery, MethodRecoveryResult[] Targets, MethodRecovery.StackCallWitness[] StackCalls);

    private static RecoveryBatch RecoverMethods(RecoveryTarget[] selected, ProgramFacts facts, ManagedTypes types, int jobs, Action<string> Log)
    {
        var methods = selected;
        var watch = Stopwatch.StartNew();
        var recovery = new MethodRecovery(facts, types);
        var targets = new MethodRecoveryResult[methods.Length];
        var completed = 0;
        void Recover(int i, MethodRecovery worker)
        {
            targets[i] = selected[i].Recover(worker);
            var count = Interlocked.Increment(ref completed);
            if (count % 1000 == 0 || count == methods.Length)
                Log($"恢复进度 {count}/{methods.Length}，{watch.Elapsed.TotalSeconds:F1} s");
        }
        Log($"方法恢复并行度：{jobs}");
        MethodRecovery.StackCallWitness[] stackCalls = [];
        if (jobs == 1)
            for (var i = 0; i < methods.Length; i++) Recover(i, recovery);
        else
        {
            // 工作线程独享恢复器和分析缓存；结果按原清单索引汇总。
            using var workers = new ThreadLocal<MethodRecovery>(() => new(facts, types), trackAllValues: true);
            Parallel.For(0, methods.Length, new ParallelOptions { MaxDegreeOfParallelism = jobs }, i => Recover(i, workers.Value!));
            stackCalls = workers.Values.SelectMany(w => w.StackCalls).Distinct().ToArray();
        }
        return new(recovery, targets, stackCalls);
    }
}
