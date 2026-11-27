using System.Diagnostics;
using System.Globalization;
using System.Reflection;
using System.Text.Json;

namespace Cpp2CS.Tools.ForwardCheck;

internal static class Sample
{
    internal sealed record Item(long Key, ulong Address, string Name)
    {
        public override string ToString() => $"{Name} 0x{Address:x} [方法 {Key}]";
    }
    internal sealed record Plan(int Population, int Entries, int Count, int Audit, Item[] Items, long[] Shown,
        string? Admission, Dictionary<string, long>? Calls);
    internal sealed record Group(int Count, string First);
    internal sealed record OutputRequest(Item[] Complete, long[] Main);
    internal sealed record Generation(Dictionary<long, string> Endpoints, int Assemblies, int Signatures, double Seconds,
        long Peak, int Verified, Dictionary<string, int> VerificationIssues, string[] MetadataHoles);

    internal sealed class Result
    {
        [System.Text.Json.Serialization.JsonIgnore(Condition = System.Text.Json.Serialization.JsonIgnoreCondition.WhenWritingNull)]
        public SampleCauseCounts? Causes { get; set; }
        public Dictionary<string, Group> Holes { get; set; } = [];
        public string? First { get; set; }
        public string? Error { get; set; }
        public string? Endpoint { get; set; }
        public string? FirstNativeOperation { get; set; }
        public void Hole(string layer, string reason)
        {
            First ??= reason;
            Holes[layer] = Holes.TryGetValue(layer, out var g) ? g with { Count = g.Count + 1 } : new(1, reason);
        }
    }
    private sealed class Measurement(Item item)
    {
        public Item Item => item;
        public Result Result = new();
        public bool Lifted, Complete, Written, Timeout;
        public int? Effects;
        public int Covered;
        public double Milliseconds;
        public string Status => Timeout ? "超时" : Result.Error != null ? "异常" : Complete ? "完整" : "有洞";
        public string Detail => Result.Error ?? Result.First ?? (Timeout ? "达到 10 秒上限" : "—");
        public void Progress(string message)
        {
            switch (message)
            {
                case "提升": Lifted = true; break;
                case "完整": Complete = true; break;
                case "写出": Written = true; break;
                default:
                    string[] fields = message.Split(' ');
                    if (fields[0] == "效果") Effects = int.Parse(fields[1], CultureInfo.InvariantCulture);
                    else if (fields[0] == "选中") Covered = int.Parse(fields[1], CultureInfo.InvariantCulture);
                    else throw new InvalidDataException($"未知工作进程消息 {message}");
                    break;
            }
        }
    }

    public static int Run(string[] args)
    {
        var options = new Dictionary<string, string>();
        bool causes = false;
        for (int i = 1; i < args.Length; i++)
        {
            string option = args[i];
            if (option == "--causes" && !causes) { causes = true; continue; }
            if (i + 1 == args.Length || option is not ("--binary" or "--metadata" or "--symbols" or "--fingerprint" or "--count" or "--seed" or "--show" or "--batch-size" or "--out" or "--rows")
                || !options.TryAdd(option, args[++i])) return Usage();
        }
        if (!options.TryGetValue("--binary", out var binary) || !options.TryGetValue("--metadata", out var metadata)
            || !int.TryParse(options.GetValueOrDefault("--count", "2000"), out int count) || count < 1
            || !int.TryParse(options.GetValueOrDefault("--seed", "202211"), out int seed)) return Usage();
        if (!int.TryParse(options.GetValueOrDefault("--batch-size", "0"), out int batchSize) || batchSize < 0) return Usage();
        if (args[0] == "assemblies" && !options.ContainsKey("--out")) return Usage();
        if (Environment.GetEnvironmentVariable("CPP2CS_SAMPLE_WORKER") == "1")
        {
            var input = new SampleInput(binary, metadata, options.GetValueOrDefault("--symbols"), options.GetValueOrDefault("--fingerprint"));
            Console.WriteLine("就绪");
            while (Console.ReadLine() is { } line)
            {
                if (line == "抽样")
                {
                    Console.WriteLine(JsonSerializer.Serialize(input.Draw(count, seed, options.GetValueOrDefault("--show"))));
                    continue;
                }
                if (line.StartsWith("生成 ", StringComparison.Ordinal))
                {
                    var request = JsonSerializer.Deserialize<OutputRequest>(line[3..])!;
                    Console.WriteLine(JsonSerializer.Serialize(input.Generate(request.Complete, request.Main, options.GetValueOrDefault("--out"))));
                    continue;
                }
                var item = JsonSerializer.Deserialize<Item>(line)!;
                var result = new Result { Causes = causes ? new() : null };
                // 在方法边界保留第一条异常，余下方法继续独立核对。
                try { input.Recover(item, result, Console.WriteLine); }
                catch (Exception e) { result.Error = $"{e.GetType().Name}：{e.Message}"; }
                Console.WriteLine(JsonSerializer.Serialize(result));
            }
            return 0;
        }
        return Measure(args, seed, options.ContainsKey("--show"), batchSize, causes, options.GetValueOrDefault("--rows")).GetAwaiter().GetResult();
    }

    private static int Usage()
    {
        Console.Error.WriteLine("用法：ForwardCheck sample --binary 原生库 --metadata 元数据 [--symbols 符号库] [--fingerprint 参照表] [--count 个数] [--seed 种子] [--show 地址|方法名] [--batch-size 批量] [--causes] [--rows 逐方法明细]");
        Console.Error.WriteLine("分批时，每批结束输出“批次暂停”，从标准输入收到“继续”后处理下一批。");
        Console.Error.WriteLine("ForwardCheck assemblies --binary 原生库 --metadata 元数据 --out 目录，抽样选项同 sample。");
        return 2;
    }

    // 主线没有取消入口。每次只运行一个方法；超时或工作进程崩溃后重新载入全局事实。
    private sealed class Worker : IDisposable
    {
        public readonly Process Process;
        private readonly Task<string?> firstError;
        public Worker(string[] args)
        {
            var start = new ProcessStartInfo(Environment.ProcessPath!)
            {
                RedirectStandardInput = true, RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false,
            };
            if (Path.GetFileNameWithoutExtension(start.FileName).Equals("dotnet", StringComparison.OrdinalIgnoreCase))
                start.ArgumentList.Add(Assembly.GetExecutingAssembly().Location);
            foreach (string arg in args) start.ArgumentList.Add(arg);
            start.Environment["CPP2CS_SAMPLE_WORKER"] = "1";
            Process = Process.Start(start) ?? throw new IOException("不能启动工作进程");
            firstError = Drain(Process.StandardError);
        }
        private static async Task<string?> Drain(StreamReader reader)
        {
            string? first = null;
            while (await reader.ReadLineAsync() is { } line) first ??= line;
            return first;
        }
        public async Task<string> Read(CancellationToken cancellation = default) => await Process.StandardOutput.ReadLineAsync(cancellation) ??
            throw new EndOfStreamException(await firstError ?? $"工作进程退出，退出码 {ExitCode()}");
        private int ExitCode() { Process.WaitForExit(); return Process.ExitCode; }
        public void Dispose()
        {
            if (!Process.HasExited) Process.Kill();
            Process.WaitForExit();
            Process.Dispose();
        }
    }

    private static async Task<int> Measure(string[] args, int seed, bool show, int batchSize, bool causes, string? rowsPath)
    {
        var clock = Stopwatch.StartNew();
        var records = new List<Measurement>();
        Worker? worker = null;
        long peak = 0;
        void Peak()
        {
            if (worker == null || worker.Process.HasExited) return;
            worker.Process.Refresh();
            peak = Math.Max(peak, worker.Process.PeakWorkingSet64);
        }
        void Stop() { Peak(); worker?.Dispose(); worker = null; }
        async Task<Worker> Ready()
        {
            if (worker != null) return worker;
            worker = new Worker(args);
            if (await worker.Read() != "就绪") throw new InvalidDataException("工作进程未就绪");
            Peak();
            return worker;
        }
        try
        {
            var first = await Ready();
            first.Process.StandardInput.WriteLine("抽样");
            var plan = JsonSerializer.Deserialize<Plan>(await first.Read())!;
            foreach (var item in plan.Items)
            {
                if (batchSize > 0 && records.Count != 0 && records.Count % batchSize == 0)
                {
                    // 工作进程正在等待下一个方法。外部调度可在此处释放互斥锁。
                    Console.WriteLine("批次暂停");
                    if (Console.ReadLine() != "继续") throw new EndOfStreamException("分批抽样缺少继续指令");
                }
                var current = await Ready();
                var row = new Measurement(item);
                var method = Stopwatch.StartNew();
                using var deadline = new CancellationTokenSource(TimeSpan.FromSeconds(10));
                current.Process.StandardInput.WriteLine(JsonSerializer.Serialize(item));
                try
                {
                    while (true)
                    {
                        var line = await current.Read(deadline.Token);
                        if (line.StartsWith('{')) { row.Result = JsonSerializer.Deserialize<Result>(line)!; break; }
                        row.Progress(line);
                    }
                }
                catch (OperationCanceledException) when (deadline.IsCancellationRequested) { row.Timeout = true; }
                catch (EndOfStreamException e) { row.Result.Error = e.Message; }
                row.Milliseconds = method.Elapsed.TotalMilliseconds;
                if (row.Timeout || current.Process.HasExited) Stop();
                records.Add(row);
                if (records.Count % 100 == 0) Console.Error.WriteLine($"已测 {records.Count}/{plan.Items.Length}，用时 {clock.Elapsed.TotalSeconds:F1} 秒");
            }
            var complete = records.Where(r => r.Complete).ToArray();
            var main = records.Take(plan.Count).Where(r => r.Complete).Select(r => r.Item.Key).ToArray();
            var writer = await Ready();
            writer.Process.StandardInput.WriteLine("生成 " + JsonSerializer.Serialize(new OutputRequest(complete.Select(r => r.Item).ToArray(), main)));
            var generated = JsonSerializer.Deserialize<Generation>(await writer.Read())!;
            foreach (var row in complete)
            {
                row.Written = true;
                row.Result.Endpoint = generated.Endpoints[row.Item.Key];
            }
            Console.WriteLine($"全量生成 {generated.Assemblies} 个程序集，生成用时 {generated.Seconds:F3} 秒，生成期间工作集峰值 {generated.Peak} 字节；全部回读，解码方法签名 {generated.Signatures}");
            Console.WriteLine($"ILVerify 通过 {generated.Verified}/{main.Length}，问题 {generated.VerificationIssues.Values.Sum()}");
            foreach (var issue in generated.VerificationIssues) Console.WriteLine($"  ILVerify {issue.Key} {issue.Value}");
            foreach (var hole in generated.MetadataHoles) Console.WriteLine($"  元数据洞 {hole}");
            Stop();
            Report(plan, records, seed, clock.Elapsed, peak);
            if (rowsPath != null)
                File.WriteAllLines(rowsPath, records.Take(plan.Count).Select(r => JsonSerializer.Serialize(new
                {
                    r.Item.Key, r.Item.Address, r.Complete, r.Status, r.Result.First, r.Result.FirstNativeOperation, r.Result.Error, r.Effects, r.Result.Causes
                })));
            if (causes)
            {
                var measured = records.Take(plan.Count).Where(r => !r.Timeout && r.Result.Error == null).ToArray();
                Console.WriteLine($"赋值相容拒绝次数：变体接口 {measured.Sum(r => r.Result.Causes!.VariantInterfaceRejections)}，数组到泛型接口 {measured.Sum(r => r.Result.Causes!.ArrayInterfaceRejections)}");
                SampleCauseCounts.Report(measured.Where(r => !r.Complete).Select(r => (r.Item, r.Result.Causes!)));
            }
            if (show && plan.Shown.Length == 0) Console.Error.WriteLine("总体中没有匹配的方法");
            return records.Any(r => r.Complete && r.Result.Endpoint != "通过") ? 1 : show && plan.Shown.Length == 0 ? 2 : 0;
        }
        finally { Stop(); }
    }

    private static void Report(Plan plan, List<Measurement> records, int seed, TimeSpan elapsed, long peak)
    {
        var main = records.Take(plan.Count).ToArray();
        var complete = main.Where(r => r.Complete).ToArray();
        if (plan.Calls != null)
        {
            Console.WriteLine(plan.Admission);
            Console.WriteLine("全映像托管入口对地图外的直接调用点：" +
                string.Join("，", plan.Calls.Select(p => $"{p.Key} {p.Value}")) + $"，合计 {plan.Calls.Values.Sum()}");
        }
        var times = main.Select(r => r.Milliseconds).Order().ToArray();
        Console.WriteLine($"总体方法 {plan.Population}，去重入口 {plan.Entries}；抽样 {main.Length}，种子 {seed}");
        Console.WriteLine($"提升 {main.Count(r => r.Lifted)}；完整恢复 {complete.Length}/{main.Length}（{(main.Length == 0 ? 0 : 100.0 * complete.Length / main.Length):F2}%）；CIL 写出 {main.Count(r => r.Written)}");
        Console.WriteLine($"效果覆盖 {main.Sum(r => (long)r.Covered)}/{main.Sum(r => (long)(r.Effects ?? 0))}，取得效果总数的方法 {main.Count(r => r.Effects.HasValue)}");
        Console.WriteLine($"终点核对通过 {complete.Count(r => r.Result.Endpoint == "通过")}/{complete.Length}");
        foreach (var r in complete.Where(r => r.Result.Endpoint != "通过")) Console.WriteLine($"  终点未通过 {r.Item}　{r.Result.Endpoint}");
        foreach (var g in main.SelectMany(r => r.Result.Holes.Select(h => (Row: r, h.Key, h.Value))).GroupBy(h => h.Key)
            .OrderByDescending(g => g.Sum(h => h.Value.Count)).ThenBy(g => g.Key, StringComparer.Ordinal).Take(5))
            Console.WriteLine($"  独立洞 {g.Key} {g.Sum(h => h.Value.Count)}　{g.First().Row.Item}　{g.First().Value.First}");
        foreach (var status in new[] { "超时", "异常" })
        {
            var rows = main.Where(r => r.Status == status).ToArray();
            Console.WriteLine($"{status} {rows.Length}" + (rows.Length == 0 ? "" : $"　{rows[0].Item}　{rows[0].Detail}"));
        }
        using var parent = Process.GetCurrentProcess();
        Console.WriteLine($"总用时 {elapsed.TotalSeconds:F3} 秒，中位数 {(times.Length == 0 ? 0 : (times[(times.Length - 1) / 2] + times[times.Length / 2]) / 2):F3} 毫秒，最大 {times.LastOrDefault():F3} 毫秒，工作进程峰值 {peak} 字节，汇总进程峰值 {parent.PeakWorkingSet64} 字节");
        foreach (var r in records.Skip(main.Length).Take(plan.Audit)) Console.WriteLine($"  抽查 {r.Item}　{r.Status}　{r.Detail}" + End(r));
        foreach (var r in records.Where(r => plan.Shown.Contains(r.Item.Key))) Console.WriteLine($"  指定 {r.Item}　{r.Status}　{r.Detail}" + End(r));
        static string End(Measurement r) => r.Complete ? $"　终点 {r.Result.Endpoint}" : "";
    }
}
