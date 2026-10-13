using System.Collections.Immutable;
using System.Diagnostics;
using System.Globalization;
using System.Security.Cryptography;
using System.Text.Json;
using System.Text.Json.Serialization;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Cpp2CS.Native;
using Cpp2CS.Nir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Validation;

public sealed record NirCorpusOptions(int MaxInstructions = 512, int MaxMachineDiagnosticInstructions = 32,
    int MaxNormalizationRounds = 64, int DecodeCacheCapacity = 8192, int ProgressInterval = 100,
    string? SourceRoot = null);

// 入口清单是分母；机器图诊断与有依据的逻辑接口恢复分别记账。
public static class NirCorpusChecks
{
    public const string Format = "cpp2cs.nir-corpus/1";
    private static readonly JsonSerializerOptions JsonOptions = CreateJsonOptions();
    private sealed record Diagnostic(ulong Address, string Code, string Message);
    private sealed record MachineDiagnostic(int Blocks, int Instructions, int Operations, bool StructureValidated,
        string SsaStatus, string SourceInstructionsSha256, ImmutableArray<Diagnostic> Boundaries);
    private sealed record EntryResult(ulong Address, string Entry, string SignatureStatus, string Status,
        string Stage, bool NirValidated, bool JsonRoundTripValidated, JsonElement InventoryEntry,
        MachineDiagnostic Machine, ImmutableArray<Diagnostic> Diagnostics,
        NirRecoveryStatistics? Statistics, ImmutableArray<NirRecoveryEvidence> RecoveryEvidence,
        ImmutableArray<string> GraphDependencies, ImmutableArray<ulong> Callees, double ElapsedMilliseconds);
    private sealed record PendingContract(bool CandidateComplete, bool Contradicted, ImmutableArray<ulong> Callees);

    public static int RunSelfChecks()
    {
        var graph = new Dictionary<ulong, PendingContract>
        {
            [0x10] = new(true, false, []), [0x20] = new(true, false, [0x30]),
            [0x30] = new(false, false, [0x40]), [0x40] = new(false, true, [0x20]),
            [0x50] = new(true, false, [0x10]), [0x60] = new(false, false, [0x70]),
            [0x70] = new(false, false, [0x60])
        };
        Require(PropagateContradictions(graph).SetEquals([0x20UL, 0x30UL, 0x40UL]),
            "反证须传递经过 draft 和循环，不得撤回无关联合同");
        Require(PropagateContradictions([]).Count == 0, "无合同图不得产生反证");
        Require(PropagateContradictions(new() { [1] = new(true, false, [1]) }).Count == 0,
            "单独递归不等于合同反证");
        Require(PropagateContradictions(new() { [1] = new(false, true, [1]) }).SetEquals([1UL]),
            "自递归合同反证须停止在固定点");
        return 4;
    }

    public static bool Run(string binaryPath, string inventoryPath, string outputDirectory, NirCorpusOptions? options = null)
    {
        options ??= new();
        if (options.MaxInstructions < 1 || options.MaxMachineDiagnosticInstructions < 1 ||
            options.MaxNormalizationRounds < 1 || options.DecodeCacheCapacity < 1 || options.ProgressInterval < 1)
            throw new ArgumentOutOfRangeException(nameof(options));
        var started = DateTimeOffset.UtcNow;
        var timer = Stopwatch.StartNew();
        var image = ImageDocument.Load(binaryPath);
        var inventory = new Inventory(inventoryPath, image);
        var assemblyHash = HashFile(typeof(NirCorpusChecks).Assembly.Location);
        var sourceRoot = Path.GetFullPath(options.SourceRoot ?? Path.Combine(AppContext.BaseDirectory, "../../../../.."));
        var sources = SourceIdentity(sourceRoot);
        var source = new CachedSource(image, options.DecodeCacheCapacity);
        Directory.CreateDirectory(outputDirectory);
        var summaryPath = Path.Combine(outputDirectory, "summary.json");
        if (File.Exists(summaryPath)) throw new IOException("输出目录已有 corpus summary，请选择新目录以保留原始记录");
        var identity = new
        {
            binaryPath = Path.GetFullPath(binaryPath), binarySha256 = image.Sha256,
            architecture = image.Architecture.ToString(), implementationAssemblySha256 = assemblyHash,
            inventoryPath = Path.GetFullPath(inventoryPath), inventorySha256 = inventory.ManifestHash,
            inventoryEntriesSha256 = inventory.EntriesHash, inventoryManifest = inventory.Manifest,
            sourceRoot, sources
        };
        WriteJson(summaryPath, new { format = Format, status = "running", started, identity, options });

        var addresses = new HashSet<ulong>();
        var contracts = new List<FunctionContract>();
        var signatureCounts = new Dictionary<string, long>(StringComparer.Ordinal);
        foreach (var item in inventory.ReadEntries())
        {
            var address = Address(item);
            if (!addresses.Add(address)) throw new InvalidDataException($"清单入口重复: 0x{address:X}");
            var signatureStatus = SignatureStatus(item);
            Increment(signatureCounts, signatureStatus);
            if (ReadContract(item) is { } contract) contracts.Add(contract);
        }
        if (addresses.Count != inventory.EntryCount)
            throw new InvalidDataException($"入口数与清单不符: {addresses.Count} != {inventory.EntryCount}");
        var contractIndex = new FunctionContractIndex(contracts);
        var byAddress = contracts.ToDictionary(contract => contract.EntryAddress);
        var pending = new Dictionary<ulong, PendingContract>();
        var candidatePath = Path.Combine(outputDirectory, "entry-candidates.jsonl");
        var moduleCandidatePath = Path.Combine(outputDirectory, "module-candidates.jsonl");
        var recoveryOptions = new NirRecoveryOptions(options.MaxInstructions, options.MaxNormalizationRounds);
        long processed = 0;
        using (var candidates = new StreamWriter(candidatePath, false))
        using (var modules = new StreamWriter(moduleCandidatePath, false))
        {
            foreach (var item in inventory.ReadEntries())
            {
                var entryTimer = Stopwatch.StartNew();
                var address = Address(item);
                var signatureStatus = SignatureStatus(item);
                WriteJson(Path.Combine(outputDirectory, "current-entry.json"), new
                {
                    address, entry = $"0x{address:X}", signatureStatus, image.Sha256,
                    processed, knownEntryAddresses = inventory.EntryCount, options
                });
                EntryResult result;
                if (byAddress.TryGetValue(address, out var contract))
                {
                    var recovered = NirRecovery.RecoverOne(source, contract, contractIndex, recoveryOptions);
                    var function = recovered.Functions.Single();
                    var validation = NirValidator.Validate(recovered.Module);
                    Require(validation.IsValid, "恢复模块验证失败: " + string.Join("; ", validation.Diagnostics));
                    var serialized = NirJson.Serialize(recovered.Module);
                    var roundTrip = NirJson.Deserialize(serialized);
                    var secondValidation = NirValidator.Validate(roundTrip);
                    Require(secondValidation.IsValid && NirJson.Serialize(roundTrip) == serialized,
                        "恢复模块 JSON 往返不稳定或验证失败");
                    var callees = function.Graph.Blocks.SelectMany(block => block.Edges).Where(edge => edge.Call is not null)
                        .Select(edge => edge.Call!.Callee.EntryAddress).Distinct().Order().ToImmutableArray();
                    var diagnostics = function.Diagnostics.Select(diagnostic =>
                        new Diagnostic(diagnostic.Address, diagnostic.Code, diagnostic.Message)).ToImmutableArray();
                    var machineInstructions = function.Graph.Blocks.Where(block => block.Instruction is not null)
                        .Select(block => block.Instruction!).ToArray();
                    var graphBoundaries = function.Graph.Gaps.Select(gap =>
                        new Diagnostic(gap.Address, "graph." + gap.Kind, gap.Reason)).ToImmutableArray();
                    result = new(address, $"0x{address:X}", signatureStatus, function.Complete ? "complete" : "draft",
                        function.Complete ? "nir" : RecoveryStage(function), function.Complete, function.Complete,
                        item, new(function.Graph.Blocks.Length, machineInstructions.Length,
                            machineInstructions.Sum(instruction => instruction.Operations.Length), true,
                            function.Statistics.MachineValues > 0 ? "built" : "not-reached",
                            InstructionIdentity(machineInstructions), graphBoundaries), diagnostics,
                        function.Statistics, function.Evidence, function.Graph.Dependencies, callees,
                        entryTimer.Elapsed.TotalMilliseconds);
                    pending.Add(address, new(function.Complete,
                        diagnostics.Any(diagnostic => diagnostic.Code.StartsWith("contract.", StringComparison.Ordinal)), callees));
                    if (function.Complete)
                    {
                        using var moduleDocument = JsonDocument.Parse(serialized);
                        modules.WriteLine(JsonSerializer.Serialize(new { address, entry = result.Entry, module = moduleDocument.RootElement }, JsonOptions));
                    }
                }
                else
                {
                    var region = RegionBuilder.Build(source,
                        [new(address, "inventory entry evidence; logical signature is unavailable or unusable")],
                        options.MaxMachineDiagnosticInstructions);
                    var errors = RegionValidator.Validate(region);
                    Require(errors.Count == 0, "机器诊断图无效: " + string.Join("; ", errors));
                    var boundaries = region.Blocks.SelectMany(block =>
                        (block.Stop is { } stop ? new[] { new Diagnostic(block.Address, "machine." + stop.Kind, stop.Reason) } : [])
                        .Concat(block.Edges.Where(edge => edge.Boundary is not null).Select(edge =>
                            new Diagnostic(block.Address, "machine." + edge.Boundary!.Kind, edge.Boundary.Reason))))
                        .ToImmutableArray();
                    var instructions = region.Blocks.Where(block => block.Instruction is not null).Select(block => block.Instruction!).ToArray();
                    var status = signatureStatus switch
                    {
                        "unsupported" => "unsupported-signature", "conflict" => "signature-conflict", _ => "unknown-signature"
                    };
                    result = new(address, $"0x{address:X}", signatureStatus, status, "machine-diagnostic", false, false,
                        item, new(region.Blocks.Length, instructions.Length,
                            instructions.Sum(instruction => instruction.Operations.Length), true, "not-attempted-without-contract",
                            InstructionIdentity(instructions), boundaries),
                        [new(address, "signature." + signatureStatus, "未采用有依据且可表达的完整逻辑接口；机器图诊断不计入 NIR 完整率")],
                        null, [], [], [], entryTimer.Elapsed.TotalMilliseconds);
                }
                candidates.WriteLine(JsonSerializer.Serialize(result, JsonOptions));
                processed++;
                if (processed % options.ProgressInterval == 0)
                {
                    candidates.Flush();
                    modules.Flush();
                    Console.WriteLine($"NIR corpus {image.Architecture}: {processed}/{inventory.EntryCount}; {timer.Elapsed}");
                }
            }
        }
        Require(processed == inventory.EntryCount, "跑批入口数与清单不符");

        var contradicted = PropagateContradictions(pending);
        var statusCounts = new Dictionary<string, long>(StringComparer.Ordinal);
        var gapCounts = new Dictionary<string, long>(StringComparer.Ordinal);
        var boundaryCounts = new Dictionary<string, long>(StringComparer.Ordinal);
        var stageCounts = new Dictionary<string, long>(StringComparer.Ordinal);
        var accepted = new HashSet<ulong>();
        var entriesPath = Path.Combine(outputDirectory, "entries.jsonl");
        using (var entries = new StreamWriter(entriesPath, false))
        {
            foreach (var line in File.ReadLines(candidatePath))
            {
                var result = JsonSerializer.Deserialize<EntryResult>(line, JsonOptions)
                    ?? throw new InvalidDataException("空的入口候选记录");
                if (contradicted.Contains(result.Address) && result.Status == "complete")
                    result = result with
                    {
                        Status = "draft", Stage = "dependency-revoked",
                        NirValidated = false, JsonRoundTripValidated = false,
                        Diagnostics = result.Diagnostics.Add(new(result.Address, "contract.dependency",
                            "当前函数或传递被调合同已被真实机器体反证；此前候选 NIR 不能作为最终结果"))
                    };
                if (result.Status == "complete") accepted.Add(result.Address);
                Increment(statusCounts, result.Status);
                Increment(stageCounts, result.Stage);
                foreach (var code in result.Diagnostics.Select(diagnostic => diagnostic.Code).Distinct()) Increment(gapCounts, code);
                foreach (var code in result.Machine.Boundaries.Select(diagnostic => diagnostic.Code).Distinct()) Increment(boundaryCounts, code);
                entries.WriteLine(JsonSerializer.Serialize(result, JsonOptions));
            }
        }
        var modulesPath = Path.Combine(outputDirectory, "modules.jsonl");
        using (var modules = new StreamWriter(modulesPath, false))
            foreach (var line in File.ReadLines(moduleCandidatePath))
            {
                using var document = JsonDocument.Parse(line);
                if (accepted.Contains(document.RootElement.GetProperty("address").GetUInt64())) modules.WriteLine(line);
            }
        Require(HashFile(typeof(NirCorpusChecks).Assembly.Location) == assemblyHash, "跑批期间程序集发生变化");
        Require(SameSources(sources, SourceIdentity(sourceRoot)), "跑批期间源码身份发生变化");
        Require(HashFile(binaryPath) == image.Sha256, "跑批期间二进制发生变化");
        inventory.VerifyIdentity();
        var complete = accepted.Count == inventory.EntryCount;
        WriteJson(summaryPath, new
        {
            format = Format, status = "completed", started, finished = DateTimeOffset.UtcNow,
            elapsedSeconds = timer.Elapsed.TotalSeconds, identity, options,
            denominator = new { knownEntryAddresses = inventory.EntryCount, processedEntries = processed,
                adoptedContractEntries = contracts.Count, signatureCounts },
            statusCounts, gapCounts, boundaryCounts, stageCounts,
            completeEntries = accepted.Count, completeRate = inventory.EntryCount == 0 ? (double?)null : (double)accepted.Count / inventory.EntryCount,
            completeRateAmongAdoptedContracts = contracts.Count == 0 ? (double?)null : (double)accepted.Count / contracts.Count,
            allKnownEntriesClassified = processed == inventory.EntryCount, allKnownEntriesNirComplete = complete,
            contradictedContracts = contradicted.Count, source.DecodeRequests, source.Decodes, source.CacheHits,
            artifacts = new[] { candidatePath, moduleCandidatePath, entriesPath, modulesPath }
                .ToDictionary(path => Path.GetFileName(path), HashFile),
            meaning = "Every inventoried address is attempted and classified. Complete means conditional recovery under the recorded signature, ABI and domain, valid NIR and stable JSON round trip, after transitive contract contradiction propagation. Unknown signatures only receive bounded machine graph diagnostics. Graph budget exhaustion remains explicit. This is not machine/NIR execution equivalence, complete entry discovery, game execution or ManagedIR recovery."
        });
        Console.WriteLine(JsonSerializer.Serialize(new { summary = Path.GetFullPath(summaryPath), processed, complete = accepted.Count,
            allKnownEntriesNirComplete = complete, statusCounts }, JsonOptions));
        return complete;
    }

    private static HashSet<ulong> PropagateContradictions(Dictionary<ulong, PendingContract> pending)
    {
        var reverse = new Dictionary<ulong, List<ulong>>();
        foreach (var (caller, item) in pending)
            foreach (var callee in item.Callees)
            {
                if (!reverse.TryGetValue(callee, out var callers)) reverse.Add(callee, callers = []);
                callers.Add(caller);
            }
        var contradicted = pending.Where(pair => pair.Value.Contradicted).Select(pair => pair.Key).ToHashSet();
        var queue = new Queue<ulong>(contradicted);
        while (queue.TryDequeue(out var callee))
            if (reverse.TryGetValue(callee, out var callers))
                foreach (var caller in callers)
                    if (contradicted.Add(caller)) queue.Enqueue(caller);
        return contradicted;
    }

    private static string RecoveryStage(NirFunctionRecovery function) => function.Diagnostics.Any(d => d.Code.StartsWith("graph.", StringComparison.Ordinal))
        ? "function-graph" : function.Statistics.MachineValues == 0 ? "interface" : "recovery";

    private static FunctionContract? ReadContract(JsonElement item)
    {
        if (SignatureStatus(item) != "known") return null;
        if (!item.TryGetProperty("signatureSynthetic", out var synthetic) || synthetic.ValueKind != JsonValueKind.False)
            throw new InvalidDataException("known 签名必须明确声明 signatureSynthetic=false");
        if (!item.TryGetProperty("signatureEvidence", out var evidence) || evidence.ValueKind != JsonValueKind.Array || evidence.GetArrayLength() == 0)
            throw new InvalidDataException("known 签名缺少独立 signatureEvidence；入口地址证据不等于签名证据");
        var contract = item.GetProperty("contract").Deserialize<FunctionContract>(JsonOptions)
            ?? throw new InvalidDataException("known 签名缺少函数合同");
        if (contract.EntryAddress != Address(item)) throw new InvalidDataException("函数合同地址与清单入口不一致");
        if (contract.Assumptions.IsDefaultOrEmpty) throw new InvalidDataException("函数合同缺少采用依据");
        return contract;
    }

    private static string SignatureStatus(JsonElement item)
    {
        var status = item.GetProperty("signatureStatus").GetString();
        return status is "known" or "unknown" or "unsupported" or "conflict" ? status :
            throw new InvalidDataException("未知的 signatureStatus");
    }

    private static ulong Address(JsonElement item)
    {
        var text = item.GetProperty("entry").GetString() ?? throw new InvalidDataException("缺少入口地址");
        if (!text.StartsWith("0x", StringComparison.OrdinalIgnoreCase)) throw new InvalidDataException("入口地址必须为 0x 十六进制字符串");
        if (!item.TryGetProperty("evidence", out var evidence) || evidence.ValueKind != JsonValueKind.Array || evidence.GetArrayLength() == 0)
            throw new InvalidDataException("入口缺少 evidence");
        return ulong.Parse(text.AsSpan(2), NumberStyles.HexNumber, CultureInfo.InvariantCulture);
    }

    private static string InstructionIdentity(IEnumerable<MirInstruction> instructions)
    {
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        foreach (var instruction in instructions.OrderBy(instruction => instruction.Origin.Address))
        {
            hash.AppendData(System.Text.Encoding.UTF8.GetBytes($"{instruction.Origin.Address:X16}:{instruction.Origin.Bytes.Length}:"));
            hash.AppendData(instruction.Origin.Bytes.Span);
        }
        return Convert.ToHexString(hash.GetHashAndReset());
    }

    private static Dictionary<string, string> SourceIdentity(string root)
    {
        var sourceDirectory = Path.Combine(root, "src", "Cpp2CS");
        if (!Directory.Exists(sourceDirectory)) throw new DirectoryNotFoundException("需要源码根目录以保存源码身份: " + root);
        return Directory.EnumerateFiles(sourceDirectory, "*", SearchOption.AllDirectories)
            .Where(path => !Path.GetRelativePath(sourceDirectory, path).Split(Path.DirectorySeparatorChar)
                .Any(part => part is "bin" or "obj"))
            .Concat(Directory.EnumerateFiles(root))
            .Where(path => Path.GetExtension(path) is ".cs" or ".csproj" or ".props" or ".targets" or ".slnx" ||
                Path.GetFileName(path) is "global.json" or "nuget.config")
            .Order(StringComparer.Ordinal).ToDictionary(path => Path.GetRelativePath(root, path), HashFile, StringComparer.Ordinal);
    }

    private static bool SameSources(Dictionary<string, string> left, Dictionary<string, string> right) =>
        left.Count == right.Count && left.All(pair => right.TryGetValue(pair.Key, out var hash) && hash == pair.Value);

    private static void Increment(Dictionary<string, long> values, string key) => values[key] = values.GetValueOrDefault(key) + 1;
    private static void Require(bool condition, string message) { if (!condition) throw new InvalidDataException(message); }
    private static string HashFile(string path)
    {
        using var stream = File.OpenRead(path);
        return Convert.ToHexString(SHA256.HashData(stream));
    }
    private static void WriteJson(string path, object value) => File.WriteAllText(path,
        JsonSerializer.Serialize(value, new JsonSerializerOptions(JsonOptions) { WriteIndented = true }) + Environment.NewLine);
    private static JsonSerializerOptions CreateJsonOptions()
    {
        var options = new JsonSerializerOptions { PropertyNameCaseInsensitive = true, PropertyNamingPolicy = JsonNamingPolicy.CamelCase,
            RespectNullableAnnotations = true, RespectRequiredConstructorParameters = true };
        options.Converters.Add(new JsonStringEnumConverter());
        return options;
    }

    private sealed class Inventory
    {
        private readonly string path;
        private readonly string? entriesPath;
        public JsonElement Manifest { get; }
        public string ManifestHash { get; }
        public string EntriesHash { get; }
        public int EntryCount { get; }
        public Inventory(string path, ImageDocument image)
        {
            this.path = Path.GetFullPath(path);
            ManifestHash = HashFile(path);
            using var document = JsonDocument.Parse(File.ReadAllText(path), new JsonDocumentOptions { AllowDuplicateProperties = false });
            Manifest = document.RootElement.Clone();
            Require(Manifest.GetProperty("format").GetString() == "cpp2cs.nir-contract-inventory.v1", "入口清单格式不匹配");
            var binary = Manifest.GetProperty("binary");
            Require(string.Equals(binary.GetProperty("sha256").GetString(), image.Sha256, StringComparison.OrdinalIgnoreCase), "入口清单二进制 SHA-256 不匹配");
            Require(binary.GetProperty("architecture").GetString() == image.Architecture.ToString(), "入口清单架构不匹配");
            if (Manifest.TryGetProperty("entriesFile", out var file))
                entriesPath = Path.GetFullPath(Path.Combine(Path.GetDirectoryName(this.path)!, file.GetString()!));
            EntryCount = Manifest.GetProperty("entryCount").GetInt32();
            Require(EntryCount > 0, "入口清单不得为空");
            EntriesHash = entriesPath is null ? ManifestHash : HashFile(entriesPath);
            if (Manifest.TryGetProperty("entriesSha256", out var expectedEntriesHash))
                Require(string.Equals(expectedEntriesHash.GetString(), EntriesHash, StringComparison.OrdinalIgnoreCase),
                    "入口 JSONL 与清单记录的 SHA-256 不匹配");
        }
        public IEnumerable<JsonElement> ReadEntries()
        {
            if (entriesPath is null)
            {
                foreach (var entry in Manifest.GetProperty("entries").EnumerateArray()) yield return entry;
                yield break;
            }
            foreach (var line in File.ReadLines(entriesPath))
            {
                using var document = JsonDocument.Parse(line, new JsonDocumentOptions { AllowDuplicateProperties = false });
                yield return document.RootElement.Clone();
            }
        }
        public void VerifyIdentity()
        {
            Require(HashFile(path) == ManifestHash, "跑批期间入口清单发生变化");
            Require(entriesPath is null || HashFile(entriesPath) == EntriesHash, "跑批期间入口 JSONL 发生变化");
        }
    }

    private sealed class CachedSource(ImageDocument image, int capacity) : IRegionInstructionSource
    {
        private readonly InstructionDecoder decoder = new(image);
        private readonly Dictionary<ulong, InstructionDecodeResult> cache = [];
        private readonly Queue<ulong> insertionOrder = [];
        public string ImageId => image.Sha256;
        public Architecture Architecture => image.Architecture;
        public long DecodeRequests { get; private set; }
        public long Decodes { get; private set; }
        public long CacheHits { get; private set; }
        public InstructionDecodeResult Decode(ulong address)
        {
            DecodeRequests++;
            if (cache.TryGetValue(address, out var found)) { CacheHits++; return found; }
            var result = decoder.Decode(address);
            Decodes++;
            if (cache.Count == capacity) cache.Remove(insertionOrder.Dequeue());
            cache.Add(address, result);
            insertionOrder.Enqueue(address);
            return result;
        }
    }
}
