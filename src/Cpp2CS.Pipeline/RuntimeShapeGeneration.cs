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
        var handlers = new TryRegionIndex(image.TryRegions);
        var ranges = image.Functions.ToDictionary(r => r.Start);
        var failures = new Dictionary<ulong, string>();
        var cache = new Dictionary<ulong, RuntimeReferenceShape?>();
        RuntimeReferenceShape? Shape(ulong entry)
        {
            if (cache.TryGetValue(entry, out var found)) return found;
            if (!ranges.TryGetValue(entry, out var range)) { failures[entry] = "没有函数范围"; return null; }
            if (!range.HasConsistentExtent) { failures[entry] = "函数范围证据冲突或缺失"; return cache[entry] = null; }
            if (handlers.HasHandlerInRange(range.Start, range.Length))
            { failures[entry] = "异常区域尚未接入原生 IR"; return cache[entry] = null; }
            var result = FunctionLifter.Lift(instructions, Arm64Registers.Convention, flow, range, entry);
            var shapeFailures = new HashSet<string>(StringComparer.Ordinal);
            var shape = result.Function is { } function ? RuntimeReferenceShape.Create(function,
                target => instructions.ResolveCallTarget(image, target), image, reason => shapeFailures.Add(reason)) : null;
            if (shape is null) failures[entry] = result.Failure is { } failure
                ? $"提升不完整：{failure.Reason.Code}" : shapeFailures.Count == 0 ? "没有完整参考形状" : string.Join("；", shapeFailures.Order(StringComparer.Ordinal));
            return cache[entry] = shape;
        }
        var names = catalog.Functions.Where(f => f.Recognition.Symbol).Select(f => f.MangledName).ToHashSet(StringComparer.Ordinal);
        var calleeNames = symbols.Where(s => names.Contains(s.Name)).GroupBy(s => s.Offset)
            .ToDictionary(g => g.Key, g => g.Select(s => s.Name).Distinct().Order(StringComparer.Ordinal).ToArray());
        RuntimeCalleeShape Reference(ulong entry, RuntimeReferenceShape shape, bool expand)
        {
            var result = new RuntimeCalleeShape(ranges[entry].Length, shape.Text) { Functions = calleeNames.GetValueOrDefault(entry) ?? [] };
            if (!expand || shape.Calls.Length == 0) return result;
            var children = shape.Calls.Select(Shape).ToArray();
            // 只补充完整的一层；缺少子形状时不把不完整提升当作依据。
            if (children.Any(child => child is null)) return result;
            return result with { Callees = shape.Calls.Select((address, index) => Reference(address, children[index]!, false)).ToArray() };
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
            if (Shape(addresses[0]) is not { } shape)
            { Missing(function, failures[addresses[0]]); continue; }
            var callees = new List<RuntimeCalleeShape>();
            foreach (var call in shape.Calls)
            {
                if (Shape(call) is not { } callee)
                { Missing(function, "直接被调函数：" + failures[call]); break; }
                callees.Add(Reference(call, callee, true));
            }
            if (callees.Count != shape.Calls.Length) continue;
            entries.Add(new(function.MangledName, ranges[addresses[0]].Length, shape.Text, callees.ToArray()) { HasImportCalls = shape.HasImportCalls });
        }
        File.WriteAllText(output, JsonSerializer.Serialize(new RuntimeShapeCatalog(1, unityVersion, triple, dataModel,
            entries.ToArray()) { Missing = missing.ToArray(), ReferenceImageSha256 = Hash(imagePath), ReferenceSymbolsSha256 = Hash(symbolsPath) }, RuntimeShapeCatalog.JsonOptions) + "\n");
        Console.WriteLine($"参考形状 {entries.Count}，含直接调用关系 {entries.Count(e => e.Callees.Length > 0)}");
    }
}
