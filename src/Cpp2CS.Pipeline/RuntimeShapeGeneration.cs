using System.Text.Json;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Recovery.RuntimeFunctions;
using Cpp2CS.Runtime;
using Cpp2CS.Targets.Arm64;
using Cpp2CS.Targets.Elf;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Pipeline;

/// <summary>离线生成器使用同一次构建的符号指定身份；产物只有形状与目录名称，不含地址。</summary>
public static class RuntimeShapeGeneration
{
    private static string Hash(string path)
    {
        using var stream = File.OpenRead(path);
        return Convert.ToHexString(System.Security.Cryptography.SHA256.HashData(stream)).ToLowerInvariant();
    }
    public static void Generate(string imagePath, string symbolsPath, string output, string unityVersion = "2022.3.62f2")
    {
        const string triple = "aarch64-linux-android";
        const string dataModel = "LP64";
        using (var stream = File.OpenRead(imagePath))
        {
            Span<byte> header = stackalloc byte[20];
            stream.ReadExactly(header);
            if (System.Buffers.Binary.BinaryPrimitives.ReadUInt16LittleEndian(header[18..]) != 183)
                throw new NotSupportedException("参考形状生成器目前只装配 ARM64 前端");
        }
        var image = ElfImage.Load(imagePath);
        var symbols = RecoverySession.CompanionSymbols(image, ElfImage.Load(symbolsPath));
        var catalog = RuntimeFunctionCatalog.Select(unityVersion, triple, dataModel);
        var instructions = new Arm64InstructionSet(image, orderedMemory: true);
        var seeds = catalog.Functions.Where(f => f.Recognition.Import is not null && f.Operation.DoesNotReturn)
            .Select(f => f.Recognition.Import!).ToHashSet(StringComparer.Ordinal);
        var flow = NoReturnAnalysis.Analyze(image, new Arm64InstructionSet(image), Arm64Registers.Convention, image.Functions,
            image.Imports.Where(i => seeds.Contains(i.Name)), new Arm64FlowFacts(), jobs: Environment.ProcessorCount);
        var directory = RuntimeFunctionLocations.Locate(image, symbols, catalog, target => instructions.ResolveCallTarget(image, target));
        var exceptionFlow = new ExceptionFlowFacts(flow, target =>
            directory.Find(target)?.Function.Operation.Termination == RuntimeTermination.ResumeUnwind);
        var ranges = image.Functions.ToDictionary(r => r.Start);
        var failures = new Dictionary<ulong, string>();
        var cache = new Dictionary<ulong, RuntimeReferenceShape?>();
        RuntimeReferenceShape? Shape(ulong entry)
        {
            if (cache.TryGetValue(entry, out var found)) return found;
            if (!ranges.TryGetValue(entry, out var range)) { failures[entry] = "没有函数范围"; return cache[entry] = null; }
            if (!range.HasConsistentExtent) { failures[entry] = "函数范围证据冲突或缺失"; return cache[entry] = null; }
            var result = FunctionLifter.Lift(instructions, Arm64Registers.Convention, exceptionFlow, range, entry);
            var shapeFailures = new HashSet<string>(StringComparer.Ordinal);
            var shape = result.Function is { } function ? RuntimeReferenceShape.Create(function,
                target => instructions.ResolveCallTarget(image, target), image, reason => shapeFailures.Add(reason)) : null;
            if (shape is null) failures[entry] = result.Failure is { } failure
                ? $"提升不完整：{failure.Reason.Code}" : shapeFailures.Count == 0 ? "没有完整参考形状" : string.Join("；", shapeFailures.Order(StringComparer.Ordinal));
            return cache[entry] = shape;
        }
        // 按层、再按路径字典序遍历；每个入口只保留最短的规范路径。
        var anchors = new Dictionary<ulong, string>();
        var anchorShapes = new Dictionary<string, RuntimeAnchorShape>(StringComparer.Ordinal);
        var exportedFunctions = symbols.Select(s => (s.Name, s.Offset)).ToHashSet();
        var frontier = image.Exports.GroupBy(e => e.Name, StringComparer.Ordinal)
            .Where(g => g.Select(e => e.Target).Distinct().Count() == 1 && g.First().Target is PointerTarget.Internal target
                && exportedFunctions.Contains((g.Key, target.Offset)))
            .Select(g => (Entry: ((PointerTarget.Internal)g.First().Target).Offset, Path: "export:" + g.Key)).ToList();
        for (int depth = 0; depth <= 2; depth++)
        {
            var next = new List<(ulong Entry, string Path)>();
            foreach (var (entry, path) in frontier.OrderBy(p => p.Path, StringComparer.Ordinal))
            {
                if (anchors.ContainsKey(entry)) continue;
                var shape = Shape(entry);
                // 导出起点必须可完整提升；调用末端可不提升。
                if (depth == 0 && shape is null) continue;
                anchors.Add(entry, path);
                if (shape is null) continue;
                anchorShapes.Add(path, new(path, ranges[entry].Length, shape.Text));
                if (depth == 2) continue;
                for (int index = 0; index < shape.Calls.Length; index++)
                    next.Add((shape.Calls[index], path + ">" + index.ToString(System.Globalization.CultureInfo.InvariantCulture)));
            }
            frontier = next;
        }
        var names = catalog.Functions.Where(f => f.Recognition.Symbol).Select(f => f.MangledName).ToHashSet(StringComparer.Ordinal);
        var calleeNames = symbols.Where(s => names.Contains(s.Name)).GroupBy(s => s.Offset)
            .ToDictionary(g => g.Key, g => g.Select(s => s.Name).Distinct().Order(StringComparer.Ordinal).ToArray());
        RuntimeCalleeShape Reference(ulong entry, RuntimeReferenceShape? shape, bool expand)
        {
            var result = new RuntimeCalleeShape(ranges.GetValueOrDefault(entry)?.Length ?? 0, shape?.Text)
            { Anchor = anchors.GetValueOrDefault(entry), Functions = calleeNames.GetValueOrDefault(entry) ?? [] };
            if (!expand || shape is null || shape.Calls.Length == 0) return result;
            var children = shape.Calls.Select(Shape).ToArray();
            // 只补充完整的一层；没有形状的节点必须有独立锚点凭据。
            if (children.Where((child, index) => child is null && !anchors.ContainsKey(shape.Calls[index])).Any()) return result;
            return result with { Callees = shape.Calls.Select((address, index) => Reference(address, children[index], false)).ToArray() };
        }
        var entries = new List<RuntimeShapeEntry>();
        var missing = new List<RuntimeShapeMissing>();
        void Missing(RuntimeFunction function, string reason)
        {
            missing.Add(new(function.MangledName, reason));
            Console.WriteLine($"未生成 | {function.Name} | {reason}");
        }
        foreach (var function in catalog.Functions.Where(f => f.Recognition.Symbol))
        {
            var addresses = symbols.Where(s => s.Name == function.MangledName).Select(s => s.Offset).Distinct().ToArray();
            if (addresses.Length != 1) { Missing(function, $"参考构建的独立入口数 {addresses.Length}"); continue; }
            var address = addresses[0];
            var anchor = anchors.GetValueOrDefault(address);
            var shape = Shape(address);
            string? shapeMissing = shape is null ? failures[address] : null;
            var callees = new List<RuntimeCalleeShape>();
            if (shape is not null)
                foreach (var call in shape.Calls)
                {
                    var callee = Shape(call);
                    if (callee is null && !anchors.ContainsKey(call))
                    { shapeMissing = "直接被调函数：" + failures[call]; break; }
                    callees.Add(Reference(call, callee, true));
                }
            if (shapeMissing is not null && anchor is null) { Missing(function, shapeMissing); continue; }
            entries.Add(new(function.MangledName, ranges.GetValueOrDefault(address)?.Length ?? 0,
                shapeMissing is null ? shape!.Text : null, shapeMissing is null ? callees.ToArray() : [])
            { Anchor = anchor, ShapeMissing = shapeMissing, HasImportCalls = shape?.HasImportCalls ?? false });
        }
        // 只保存实际引用锚点及其前缀的形状，避免写入无关的导出子图。
        var used = new HashSet<string>(StringComparer.Ordinal);
        void Use(string? path)
        {
            while (path is not null)
            {
                used.Add(path);
                int separator = path.LastIndexOf('>');
                path = separator < 0 ? null : path[..separator];
            }
        }
        void UseCallee(RuntimeCalleeShape callee)
        {
            Use(callee.Anchor);
            foreach (var child in callee.Callees ?? []) UseCallee(child);
        }
        foreach (var entry in entries) { Use(entry.Anchor); foreach (var callee in entry.Callees) UseCallee(callee); }
        File.WriteAllText(output, JsonSerializer.Serialize(new RuntimeShapeCatalog(2, unityVersion, triple, dataModel,
            entries.ToArray()) { AnchorShapes = anchorShapes.Values.Where(s => used.Contains(s.Path)).OrderBy(s => s.Path, StringComparer.Ordinal).ToArray(), Missing = missing.ToArray(), ReferenceImageSha256 = Hash(imagePath), ReferenceSymbolsSha256 = Hash(symbolsPath) }, RuntimeShapeCatalog.JsonOptions) + "\n");
        Console.WriteLine($"参考条目 {entries.Count}，完整形状 {entries.Count(e => e.Shape is not null)}，自身锚点 {entries.Count(e => e.Anchor is not null)}，路径节点 {anchorShapes.Keys.Count(used.Contains)}");
    }
}
