using System.Diagnostics;
using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Idioms;

namespace Cpp2CS.Recovery;

/// <summary>Prepare 步骤的结果：继续，或中止整个方法的恢复（失败已记洞）。</summary>
internal enum PrepareOutcome
{
    Continue,
    Stop,
}

/// <summary>Prepare 各步骤之间传递的中间数据。</summary>
[Flags]
internal enum PreparedData
{
    None = 0,
    /// <summary>签名绑定的结果（<see cref="PreparedMethod.Signature"/>、<see cref="PreparedMethod.ReturnValue"/>）。</summary>
    Signature = 1,
    /// <summary>提升得到的机器函数（<c>scope.function</c>）。</summary>
    Function = 2,
    /// <summary>L2 的结果（<see cref="PreparedMethod.Idioms"/>）。</summary>
    Idioms = 4,
    /// <summary>帧常量下标是否有改写（<see cref="PreparedMethod.ConstantFrameIndices"/>）。</summary>
    ConstantFrameIndices = 8,
    /// <summary>提升所用的机器模型：托管 ABI、调用模型与栈指针（<see cref="PreparedMethod.Abi"/> 等），由内核从方法恢复器取得。</summary>
    Lifting = 16,
}

/// <summary>Prepare 的中间数据，由计划表中声明为产物的步骤写入、声明为输入的步骤读取。</summary>
internal sealed class PreparedMethod
{
    public AbiSignature Signature { get; set; } = null!;
    public Expr? ReturnValue { get; set; }
    public IdiomResult Idioms { get; set; } = null!;
    public bool ConstantFrameIndices { get; set; }
    public ManagedAbi Abi { get; set; } = null!;
    public Cpp2CS.Machine.Ssa.ICallModel Calls { get; set; } = null!;
    public Storage StackPointer { get; set; }
}

/// <summary>
/// 计划表的一个条目：步骤 Id、输入、产物、执行条件与是否允许中止。
/// <paramref name="Unattached"/> 的条目在机器函数交给步骤列表之前运行：不挂接改写器，只记录追踪。
/// </summary>
internal sealed record PrepareEntry(string Id, PreparedData Reads = PreparedData.None, PreparedData Writes = PreparedData.None,
    Func<MethodSession, PreparedMethod, bool>? When = null, bool CanStop = false, bool Unattached = false);

/// <summary>
/// Prepare 的计划表：这张表就是 Prepare 的规格。步骤注册在各族（包装机器层与 L2 算法的步骤注册在 Kernel），
/// 执行顺序由表给出。启动时核对：表中每个 Id 恰好对应一个 Prepare 阶段的注册步骤，注册的 Prepare 步骤都在表中；
/// 输入在之前的条目中产生；只有声明了 CanStop 的条目可以返回中止。
/// </summary>
internal static class PreparePlan
{
    private const PreparedData F = PreparedData.Function;

    internal static readonly PrepareEntry[] Entries =
    [
        new("signature.bind", Writes: PreparedData.Signature, CanStop: true, Unattached: true),
        new("kernel.lift", Reads: PreparedData.Signature, Writes: F | PreparedData.Lifting, CanStop: true, Unattached: true),
        new("kernel.idioms", Reads: F, Writes: PreparedData.Idioms, Unattached: true),
        new("generics.bind-shared-references", Reads: F, When: (scope, _) => scope.SharedDefinition),
        new("kernel.promote-private-frame-slots", Reads: F,
            When: (scope, _) => scope.method.TypeArguments.Concat(scope.method.MethodArguments).Any(t => t is GenericParameterRef { NativeAggregate: not null })),
        new("generics.shared-fields", Reads: F),
        new("generics.shared-values", Reads: F),
        new("control.stack-canary", Reads: F | PreparedData.Lifting),
        new("calls.split-identity-choices", Reads: F),
        new("kernel.idiom-errors", Reads: PreparedData.Idioms, CanStop: true),
        new("values.narrow-scalar-vectors", Reads: F),
        new("structs.vector-phi-projection", Reads: F),
        new("structs.call-argument-projection", Reads: F),
        new("calls.trim-indirect-arguments", Reads: F),
        new("structs.scalar-phi-projection", Reads: F),
        new("kernel.remove-dead", Reads: F),
        // 库内存操作归一后也可能产生新栈读写；普通方法与异常方法采用同一有界提升规则。
        new("kernel.frame-writebacks", Reads: F),
        new("kernel.frame-constant-indices", Reads: F, Writes: PreparedData.ConstantFrameIndices),
        new("frames.managed-promotion", Reads: F | PreparedData.Signature | PreparedData.Lifting),
        new("kernel.propagate-constant-indices", Reads: F | PreparedData.ConstantFrameIndices, When: (_, prepared) => prepared.ConstantFrameIndices),
        new("calls.cleanup-thunks", Reads: F),
        new("calls.outlined-calls", Reads: F | PreparedData.Idioms),
        // 清理 thunk 拆开后，栈上的 this 可回代为参数；用同一套委托证明消费新出现的类型证据。
        new("kernel.delegate-calls", Reads: F | PreparedData.Idioms),
        new("exceptions.null-branches", Reads: F, When: (scope, _) => scope.function.Blocks.Any(b => b.IsLandingPad)),
        new("kernel.residual-holes", Reads: F | PreparedData.Idioms),
        new("exceptions.regions", Reads: F),
        new("kernel.problem-holes", Reads: F),
    ];

    private static readonly RegisteredPrepareStep[] Steps = Check();

    /// <summary>按计划表运行 Prepare；某一步中止时返回 false。</summary>
    internal static bool Prepare(this MethodSession ctx)
    {
        var prepared = new PreparedMethod();
        for (var i = 0; i < Entries.Length; i++)
        {
            var (entry, step) = (Entries[i], Steps[i]);
            var outcome = PrepareOutcome.Continue;
            void Run()
            {
                if (entry.When?.Invoke(ctx, prepared) ?? true)
                    outcome = step.Run(ctx, prepared);
            }

            // 步骤列表在第一次访问时捕获机器函数，因此只在提升之后的条目中访问。
            if (entry.Unattached)
                Unattached(ctx, entry.Id, Run);
            else
            {
                ctx.Passes.Run(entry.Id, Run);
                ctx.trace.Add(TraceEntry.Of(ctx.passSteps[^1], entry.Id));
            }
            if (outcome == PrepareOutcome.Stop)
                return false;
        }

        return true;
    }

    /// <summary>不挂接改写器地运行一步并记录追踪（机器函数尚未交给步骤列表）。</summary>
    private static void Unattached(MethodSession ctx, string id, Action run)
    {
        ctx.currentStep = id;
        var before = ctx.function?.Blocks.SelectMany(b => b.Statements).ToArray() ?? [];
        var started = Stopwatch.GetTimestamp();
        run();
        var after = ctx.function?.Blocks.SelectMany(b => b.Statements).ToArray() ?? [];
        ctx.trace.Add(TraceEntry.Of(new(id, !before.SequenceEqual(after, ReferenceEqualityComparer.Instance), before.Length, after.Length,
            1, PassConvergence.Single, Stopwatch.GetElapsedTime(started).TotalMilliseconds), id));
    }

    private static RegisteredPrepareStep[] Check()
    {
        var registered = RuleRegistry.Prepares;
        var produced = PreparedData.None;
        var steps = new List<RegisteredPrepareStep>();
        foreach (var entry in Entries)
        {
            var step = registered.GetValueOrDefault(entry.Id) ?? throw new InvalidOperationException($"Prepare 计划表中的 {entry.Id} 没有注册为 Prepare 步骤");
            if ((entry.Reads & ~produced) is var missing and not PreparedData.None)
                throw new InvalidOperationException($"Prepare 步骤 {entry.Id} 的输入 {missing} 在之前的条目中没有产生");
            if (step.CanStop != entry.CanStop)
                throw new InvalidOperationException($"Prepare 步骤 {entry.Id} 的中止声明与方法的返回类型不一致");
            produced |= entry.Writes;
            steps.Add(step);
        }

        var ids = Entries.Select(e => e.Id).ToArray();
        if (ids.GroupBy(id => id, StringComparer.Ordinal).FirstOrDefault(g => g.Count() > 1) is { } repeated)
            throw new InvalidOperationException($"Prepare 计划表中的 {repeated.Key} 重复");
        if (registered.Keys.Except(ids, StringComparer.Ordinal).FirstOrDefault() is { } unlisted)
            throw new InvalidOperationException($"注册的 Prepare 步骤 {unlisted} 不在计划表中");
        return steps.ToArray();
    }
}
