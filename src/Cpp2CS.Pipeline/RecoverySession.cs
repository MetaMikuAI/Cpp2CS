using System.Collections.Immutable;
using System.Buffers.Binary;
using System.Diagnostics;
using Cpp2CS.Input;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Output;
using Cpp2CS.Runtime;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64;
using Cpp2CS.Targets.Frontend;
using Cpp2CS.Targets.Elf;

namespace Cpp2CS.Pipeline;

public sealed record RecoveryRequest(string Image, string Metadata, string Output)
{
    /// <summary>只恢复并导出这个程序集（文件名，如 X.dll）的方法；全局事实仍按整个映像计算。</summary>
    public string? Assembly { get; init; }
    public string? Method { get; init; }
    /// <summary>相对映像首选基址的入口偏移；可匹配该方法的任意注册入口。</summary>
    public ulong? Address { get; init; }
    public int Jobs { get; init; } = 1;
    public bool Source { get; init; }
    /// <summary>已处理的方法数（含洞）与总数；可从工作线程调用，不参与判定。</summary>
    public Action<int, int>? Progress { get; init; }
    /// <summary>可选：同一次构建里未去符号的映像文件。只取它的函数符号，作为运行时函数定位的一种证据。</summary>
    public string? Symbols { get; init; }
    public string UnityVersion { get; init; } = "2022.3.62f2";
}
public sealed class RecoverySession
{
    // 架构实现只在此处装配，目标工程不反向引用 Pipeline。
    private sealed class AnalysisTiming(int jobs)
    {
        internal int Jobs { get; } = jobs;
        internal double? Seconds { get; set; }
    }
    // 按全局事实登记，供默认组件（含运行时函数定位的取用）共用；键随全局事实回收。
    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<GlobalFacts, AnalysisTiming> analysisTimings = [];
    private static readonly IFrontendProvider[] DefaultProviders =
    [
        new FrontendProvider("arm64", facts => RuntimeLocationAssembly.Components(facts, facts =>
        {
            var instructions = new Arm64InstructionSet(facts.Image);
            var catalog = RuntimeFunctionCatalog.Select(facts.Spec.Layout.UnityVersion, facts.Spec.Layout.Triple, facts.Spec.Layout.DataModel);
            var seeds = catalog.Functions.Where(f => f.Recognition.Import is not null && f.Operation.DoesNotReturn)
                .Select(f => f.Recognition.Import!).ToHashSet(StringComparer.Ordinal);
            var timing = analysisTimings.GetValue(facts, _ => new(1));
            var analysisWatch = Stopwatch.StartNew();
            var flow = NoReturnAnalysis.Analyze(facts.Image, instructions, Arm64Registers.Convention, facts.Image.Functions,
                facts.Image.Imports.Where(i => seeds.Contains(i.Name)), new Arm64FlowFacts(), jobs: timing.Jobs);
            timing.Seconds = analysisWatch.Elapsed.TotalSeconds;
            return new(instructions, Arm64Registers.Convention, flow);
        })),
    ];
    internal static int AnalysisJobs(GlobalFacts facts) => analysisTimings.TryGetValue(facts, out var timing) ? timing.Jobs : 1;
    internal static FrontendComponents DefaultComponents(GlobalFacts facts) => DefaultProviders.Single(p => p.Architecture == facts.Architecture).Create(facts);
    private readonly IMethodStage<CodeEntry, NativeFunction> frontend;
    private readonly IMethodStage<NativeFunction, ManagedBody> recovery;
    public RecoverySession(IEnumerable<IFrontendProvider>? providers = null,
        IMethodStage<CodeEntry, NativeFunction>? frontend = null, IMethodStage<NativeFunction, ManagedBody>? recovery = null)
    {
        this.frontend = frontend ?? new FrontendStage(providers ?? DefaultProviders);
        this.recovery = recovery ?? new IntegerRecoveryStage(this.frontend);
    }
    public static string Identity(MethodDef method) => $"{method.Owner.Assembly}:0x{method.Token:x8}";
    public RecoveryReport Run(RecoveryRequest request)
    {
        ArgumentOutOfRangeException.ThrowIfLessThan(request.Jobs, 1);
        var watch = Stopwatch.StartNew();
        var image = ElfImage.Load(request.Image);
        // IImage 尚不公开架构；装配处只读取 ELF 的机器标记，格式校验由 ElfImage 完成。
        using var stream = File.OpenRead(request.Image);
        Span<byte> header = stackalloc byte[20];
        stream.ReadExactly(header);
        var architecture = BinaryPrimitives.ReadUInt16LittleEndian(header[18..]) switch
        {
            183 => "arm64", 62 => "x64", _ => throw new NotSupportedException("尚无该 ELF 架构的运行时规格选择")
        };
        var spec = RuntimeSpec.Select(request.UnityVersion, architecture == "arm64" ? "aarch64-linux-android" : "x86_64-linux-android", "LP64");
        var (model, registration) = ModelBuilder.Load(image, request.Metadata, spec);
        var (map, problems) = RegistrationReader.Read(image, model, spec, registration.CodeRegistration, registration.MetadataRegistration);
        if (problems.Count != 0) throw new InvalidDataException("代码地图不完整：" + string.Join("；", problems));
        var facts = new GlobalFacts(image, model, map, spec, architecture);
        if (request.Symbols is not null) facts = facts with { Symbols = CompanionSymbols(image, ElfImage.Load(request.Symbols)) };
        return Run(facts, request, watch.Elapsed.TotalSeconds);
    }
    /// <summary>伴随文件必须与映像出自同一次构建：映像自己带的函数符号（动态符号）在伴随文件里必须同名同址。</summary>
    public static ImmutableArray<FunctionSymbol> CompanionSymbols(IImage image, IImage companion)
    {
        var known = companion.FunctionSymbols.Select(s => (s.Name, s.Offset)).ToHashSet();
        if (image.FunctionSymbols.IsEmpty || image.FunctionSymbols.Any(s => !known.Contains((s.Name, s.Offset))))
            throw new InvalidDataException("符号文件与映像不是同一次构建：映像的动态符号在符号文件里没有同名同址的定义");
        return companion.FunctionSymbols;
    }
    /// <summary>供已有全局事实的调用方使用；不重新读文件。</summary>
    public RecoveryReport Run(GlobalFacts facts, RecoveryRequest request, double inputSeconds = 0)
    {
        ArgumentOutOfRangeException.ThrowIfLessThan(request.Jobs, 1);
        var watch = Stopwatch.StartNew();
        var analysisTiming = analysisTimings.GetValue(facts, _ => new(request.Jobs));
        bool analysisAlreadyCached = analysisTiming.Seconds is not null;
        var groups = facts.CodeMap.Entries.Where(e => e.Method is not null).GroupBy(e => e.Method!.Method)
            .Where(g => (request.Method is null || g.Key.ToString().Contains(request.Method, StringComparison.Ordinal)
                    || Identity(g.Key) == request.Method)
                && (request.Assembly is null || g.Key.Owner.Assembly == request.Assembly)
                && (request.Address is null || g.Any(e => e.Address == request.Address)))
            .OrderBy(g => Identity(g.Key), StringComparer.Ordinal).ToArray();
        var rows = new MethodReport[groups.Length];
        var programErrors = new System.Collections.Concurrent.ConcurrentBag<string>();
        var bodies = new ManagedBody?[groups.Length];
        long frontTicks = 0, recoveryTicks = 0;
        int processed = 0;
        void Advance()
        {
            if (request.Progress is not { } progress) return;
            int count = Interlocked.Increment(ref processed);
            if (count % 10000 == 0 || count == groups.Length) progress(count, groups.Length);
        }
        request.Progress?.Invoke(0, groups.Length);
        Parallel.For(0, groups.Length, new ParallelOptions { MaxDegreeOfParallelism = request.Jobs }, i =>
        {
            var entries = groups[i].OrderBy(e => e.Kind).ThenBy(e => e.Address).ThenBy(e => e.Index).ToArray();
            var method = groups[i].Key;
            // 泛型定义优先全 object 规范实例；全部候选仍保留供报告与调用核对。
            var entry = SelectEntry(method, entries);
            if (!method.DeclaresCilBody)
            {
                rows[i] = new(Identity(method), method.ToString(), entry.Address,
                    entries.Select(e => new EntryReport(e.Address, e.Kind.ToString(), e.Method!.ToString())).ToArray(), MethodStatus.NoBody, null);
                Advance();
                return;
            }
            if (GenericWitness.IsGeneric(method) && (entry.Kind != EntryKind.GenericMethod || entry.Method is null || !GenericWitness.IsCanonical(entry.Method)))
            {
                rows[i] = new(Identity(method), method.ToString(), entry.Address,
                    entries.Select(e => new EntryReport(e.Address, e.Kind.ToString(), e.Method!.ToString())).ToArray(), MethodStatus.Hole,
                    new("恢复", entry.Address, "绑定", new("lowering.Generic.Witness", "没有全 object 的规范实例；已有入口：" +
                        string.Join("；", entries.Select(e => $"{e.Kind}: {e.Method}")))));
                Advance();
                return;
            }
            StageResult<ManagedBody> Recover(CodeEntry candidate)
            {
                var context = new MethodContext(method, candidate, facts);
                var lifted = Invoke(frontend, candidate, context, programErrors, out var ticks);
                Interlocked.Add(ref frontTicks, ticks);
                if (lifted is Missing<NativeFunction> missing) return new Missing<ManagedBody>(missing.Hole);
                var result = Invoke(recovery, ((Completed<NativeFunction>)lifted).Value, context, programErrors, out ticks);
                Interlocked.Add(ref recoveryTicks, ticks);
                if (result is Completed<ManagedBody> { Value: var body } && body.Method != MethodRef.Open(method))
                    throw new InvalidOperationException($"{Identity(method)}：恢复层未返回开放定义体");
                return result;
            }
            var reference = Recover(entry);
            var hole = (reference as Missing<ManagedBody>)?.Hole;
            bodies[i] = (reference as Completed<ManagedBody>)?.Value;
            CodeEntry? valueEntry = null;
            if (bodies[i] is { } referenceBody && GenericWitness.IsGeneric(method))
            {
                valueEntry = SelectValueEntry(entries);
                if (valueEntry is not null)
                {
                    var value = Recover(valueEntry);
                    if (value is Missing<ManagedBody> missing)
                        hole = new("恢复", valueEntry.Address, "值见证", new("lowering.Generic.ValueWitness",
                            "值见证恢复失败：" + valueEntry.Method + "；" + missing.Hole.Reason.Message, missing.Hole.Reason));
                    else if (GenericBodyComparison.Compare(referenceBody, ((Completed<ManagedBody>)value).Value) is { } difference)
                        hole = new("恢复", valueEntry.Address, "值见证", difference);
                    else bodies[i] = referenceBody with { WitnessCoverage = GenericWitnessCoverage.ReferenceAndValue };
                    if (hole is not null) bodies[i] = null;
                }
            }
            rows[i] = new(Identity(method), method.ToString(), entry.Address,
                entries.Select(e => new EntryReport(e.Address, e.Kind.ToString(), e.Method!.ToString())).ToArray(),
                hole is null ? MethodStatus.Complete : MethodStatus.Hole, hole)
                { WitnessCoverage = bodies[i]?.WitnessCoverage,
                    ValueWitness = valueEntry is null ? null : new(valueEntry.Address, valueEntry.Kind.ToString(), valueEntry.Method!.ToString()) };
            Advance();
        });
        for (int i = 0; i < rows.Length; i++)
            rows[i] = rows[i] with { HasValueTypeInstance = groups[i].Any(e => e.Kind == EntryKind.GenericMethod
                && e.Method is { } instance && GenericWitness.IsValueInstance(instance)) };
        var outputWatch = Stopwatch.StartNew();
        var skeleton = new Skeleton(facts.Model, checked((int)facts.Spec.Layout.ObjectHeaderSize));
        var pointer = facts.Spec.Layout.Primitive("void *");
        var types = new ManagedTypes(facts.Model, new FieldLayouts(facts.Spec, (int)pointer.Size, (int)pointer.Alignment), (int)pointer.Size);
        var emitter = new BodyEmitter(skeleton, types);
        var contractFailures = new List<string>();
        for (var i = 0; i < rows.Length; i++)
        {
            if (bodies[i] is { } body)
            {
                Dictionary<ManagedBody, EmissionProblem> problems;
                try { problems = emitter.Emit([body]); }
                catch (Exception error) when (error is not OutOfMemoryException)
                {
                    // 与恢复阶段相同：输出层的异常是程序错误，单列并继续。
                    var text = $"{rows[i].Identity}，层 输出：{error.GetType().Name}：{error.Message}";
                    programErrors.Add(text);
                    Console.Error.WriteLine("程序错误：" + text);
                    rows[i] = rows[i] with { Status = MethodStatus.Hole,
                        Hole = new("输出", rows[i].Entry, "程序错误", new("internal.error", error.GetType().Name + "：" + error.Message)) };
                    continue;
                }
                if (problems.Count != 0)
                {
                    // 契约失败是恢复层的程序错误：方法保留占位体并记入报告，运行照常写出结果，由调用方以失败收尾。
                    var problem = problems.First().Value.ToString();
                    contractFailures.Add($"{rows[i].Identity}：输出层契约失败：{problem}");
                    rows[i] = rows[i] with { Status = MethodStatus.Hole,
                        Hole = new("输出", rows[i].Entry, "契约", new("output.contract", problem)) };
                }
            }
            // 洞保留 Skeleton 的标准占位体；报告是是否写出的唯一依据。
        }
        if (request.Source) DecompileStage.Mark(facts.Model, rows, emitter);
        skeleton.Write(request.Output);
        RuntimeLocationAssembly.Write(facts, Path.Combine(request.Output, "runtime-functions.json"));
        SourceReport? source = null;
        using var process = Process.GetCurrentProcess();
        RecoveryReport Build()
        {
            var holes = rows.Where(r => r.Hole is { Derived: false }).Select(r => r.Hole!).ToArray();
            return new RecoveryReport(1, rows, new(rows.Length, rows.Count(r => r.Status == MethodStatus.Complete), rows.Count(r => r.Status == MethodStatus.Hole),
                holes.GroupBy(h => h.Layer).ToDictionary(g => g.Key, g => g.Count()), holes.GroupBy(h => h.Reason.Code).ToDictionary(g => g.Key, g => g.Count()),
                new() { ["输入"] = inputSeconds, [frontend.Name] = (double)frontTicks / Stopwatch.Frequency,
                    [recovery.Name] = (double)recoveryTicks / Stopwatch.Frequency, ["输出"] = outputWatch.Elapsed.TotalSeconds,
                    ["不返回分析"] = analysisAlreadyCached ? 0 : analysisTiming.Seconds ?? 0,
                    ["运行时定位"] = RuntimeLocationAssembly.Seconds(facts) },
                inputSeconds + watch.Elapsed.TotalSeconds, process.PeakWorkingSet64) { NoBody = rows.Count(r => r.Status == MethodStatus.NoBody), ContractFailures = [.. contractFailures], ProgramErrors = [.. programErrors.Order(StringComparer.Ordinal)], RuntimeFunctionsByEvidence = RuntimeLocationAssembly.Evidence(facts) }) { Source = source };
        }
        void Save(RecoveryReport value)
        {
            using var destination = File.Create(Path.Combine(request.Output, "recovery.json"));
            RecoveryReport.Write(destination, value);
        }
        if (request.Source)
        {
            // 源码导出耗时且可能失败；方法级的结果先落盘，不随它丢失。
            Save(Build());
            try { source = DecompileStage.Write(request.Output, skeleton, facts.Model, request.Assembly); }
            catch (Exception error) when (error is not OutOfMemoryException)
            {
                var text = $"源码导出：{error.GetType().Name}：{error.Message}";
                programErrors.Add(text);
                Console.Error.WriteLine("程序错误：" + text);
            }
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
        outputWatch.Stop();
        var report = Build();
        Save(report);
        return report;
    }
    public static CodeEntry SelectEntry(MethodDef method, IEnumerable<CodeEntry> entries) => entries
        .OrderBy(e => GenericWitness.IsGeneric(method) && e.Kind == EntryKind.GenericMethod && e.Method is { } witness && GenericWitness.IsCanonical(witness) ? 0 : 1)
        .ThenBy(e => e.Kind).ThenBy(e => e.Address).ThenBy(e => e.Index).First();

    public static CodeEntry? SelectValueEntry(IEnumerable<CodeEntry> entries) => entries
        .Where(e => e.Kind == EntryKind.GenericMethod && e.Method is { } instance && GenericWitness.IsValueInstance(instance))
        .OrderBy(e => e.Method!.TypeArguments.Concat(e.Method.MethodArguments).All(t => ManagedTypes.PrimitiveName(t) is
            "Boolean" or "Char" or "SByte" or "Byte" or "Int16" or "UInt16" or "Int32" or "UInt32" or "Int64" or "UInt64" or "Single" or "Double" or "IntPtr" or "UIntPtr") ? 0 : 1)
        .ThenBy(e => e.Address).ThenBy(e => e.Index).FirstOrDefault();

    private static StageResult<TOut> Invoke<TIn, TOut>(IMethodStage<TIn, TOut> stage, TIn input, MethodContext context,
        System.Collections.Concurrent.ConcurrentBag<string> programErrors, out long ticks) where TOut : class
    {
        var started = Stopwatch.GetTimestamp();
        try { return stage.Run(input, context); }
        catch (Exception error) when (error is not OutOfMemoryException)
        {
            // 程序错误不是恢复的结论：该方法记为未写出并在汇总里单列，命令以失败退出；一次全量不因单个方法作废。
            var where = error.StackTrace?.Split('\n').Select(l => l.Trim()).FirstOrDefault(l => l.StartsWith("at Cpp2CS", StringComparison.Ordinal));
            var text = $"{Identity(context.Method)}，层 {stage.Name}：{error.GetType().Name}：{error.Message}；{where}";
            programErrors.Add(text);
            Console.Error.WriteLine("程序错误：" + text);
            return new Missing<TOut>(new(stage.Name, context.Entry.Address, "程序错误", new("internal.error", error.GetType().Name + "：" + error.Message)));
        }
        finally { ticks = Stopwatch.GetTimestamp() - started; }
    }
}
