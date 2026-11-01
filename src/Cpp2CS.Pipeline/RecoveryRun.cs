using System.Diagnostics;
using System.Text;
using Cpp2CS.Facts;
using Cpp2CS.Recovery;

namespace Cpp2CS.Pipeline;

/// <summary>
/// 一次 recover 运行在阶段之间传递的产物，阶段表（<see cref="StageTables"/>）按 profile 依次填写。
/// 没有运行清单的运行（执行对照复用阶段表重新写出）只执行不写文件的阶段。
/// </summary>
internal sealed class RecoveryRun(RecoveryRequest request, Action<string>? progress, RunManifest? manifest)
{
    public RecoveryRequest Request { get; } = request;
    public RunManifest? Manifest { get; } = manifest;
    public void Log(string message) => progress?.Invoke(message);

    /// <summary>有运行清单时记入清单的阶段，否则直接执行。</summary>
    public T Step<T>(string name, Func<T> action) => Manifest is null ? action() : Manifest.Step(name, action);
    public void Begin(string name) => Manifest?.Begin(name);
    public void End() => Manifest?.End();

    public ProgramFacts Facts { get; set; } = null!;
    public ManagedTypes Types { get; set; } = null!;
    public SelectionStage.Selection Selection { get; set; } = null!;
    public RecoveryStage.RecoveryBatch Batch { get; set; } = null!;
    public MethodSummaryService Summaries { get; set; } = null!;
    public MethodRecoveryResult[] Targets => Batch.Targets;

    /// <summary>范围方法与依赖方法的恢复结果（core：依赖闭包；full：访问器闭包）。</summary>
    public MethodRecoveryResult[] Results { get; set; } = null!;
    public HashSet<MethodDef> Dependencies { get; set; } = null!;
    public int DependencyCount { get; set; }
    public Dictionary<ulong, long> Bytes { get; set; } = null!;
    public Skeleton Skeleton { get; set; } = null!;
    public BodyEmitter Emitter { get; set; } = null!;
    /// <summary>写出检查发现的问题（core：写出器检查与依赖闭包核对；full：访问器闭包的结论）。</summary>
    public Dictionary<ManagedBody, EmissionProblem> Problems { get; set; } = null!;
    public PublishedMethods Published { get; set; } = null!;

    /// <summary>full：访问器闭包、候选描述与证据。</summary>
    public AccessorRecovery? Closure { get; set; }
    public Dictionary<MethodDef, string> Descriptions { get; set; } = [];
    public Dictionary<MethodDef, string> InlineDescriptions { get; set; } = [];
    public HashSet<string> Evidence { get; set; } = [];

    public StringBuilder Report { get; set; } = null!;
    public Stopwatch Clock { get; } = new();
    public RecoveryRunResult Outcome { get; set; } = null!;
}
