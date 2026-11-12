using System.Globalization;
using Cpp2CS.Native.Images;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.RuntimeFunctions;

/// <summary>只复核路径的来源节点；末端目标不必能提升。调用方在并行匹配前解析并缓存全部路径。</summary>
public sealed class RuntimeExportAnchorResolver
{
    private sealed record Resolution(ulong? Entry, string? Reason);
    private readonly Dictionary<string, Resolution> cache = new(StringComparer.Ordinal);
    private readonly IReadOnlyDictionary<string, RuntimeAnchorShape> shapes;
    private readonly IReadOnlyDictionary<string, ulong[]> exports;
    private readonly IReadOnlyDictionary<ulong, FunctionRange> ranges;
    private readonly Func<ulong, RuntimeReferenceShape?> shape;

    public RuntimeExportAnchorResolver(IImage image, RuntimeShapeCatalog references, Func<ulong, RuntimeReferenceShape?> shape)
    {
        this.shape = shape;
        shapes = references.AnchorShapes.ToDictionary(s => s.Path, StringComparer.Ordinal);
        exports = image.Exports.GroupBy(e => e.Name, StringComparer.Ordinal).ToDictionary(g => g.Key,
            g => g.Select(e => e.Target).Distinct().Count() == 1 && g.First().Target is PointerTarget.Internal target
                ? new[] { target.Offset } : [], StringComparer.Ordinal);
        ranges = image.Functions.ToDictionary(r => r.Start);
    }

    public ulong? Resolve(string path, out string? reason)
    {
        if (!cache.TryGetValue(path, out var result))
        {
            var parts = path.Split('>');
            if (parts.Length > 3 || !parts[0].StartsWith("export:", StringComparison.Ordinal) || parts[0].Length == 7
                || parts.Skip(1).Any(p => !int.TryParse(p, NumberStyles.None, CultureInfo.InvariantCulture, out _)))
                throw new InvalidDataException("无效导出锚点路径：" + path);
            if (parts.Length == 1)
                result = exports.TryGetValue(parts[0][7..], out var targets) && targets.Length == 1
                    ? new(targets[0], null) : new(null, "导出不存在或目标不唯一");
            else
            {
                var prefix = path[..path.LastIndexOf('>')];
                var source = Resolve(prefix, out var sourceReason);
                if (source is not { } entry) result = new(null, sourceReason);
                else if (!shapes.TryGetValue(prefix, out var expected)) result = new(null, "路径来源节点没有登记形状");
                else if (!ranges.TryGetValue(entry, out var range) || range.Length != expected.Length
                    || shape(entry) is not { } actual || actual.Text != expected.Shape)
                    result = new(null, "路径来源节点无法完整提升或形状不同");
                else
                {
                    var index = int.Parse(parts[^1], CultureInfo.InvariantCulture);
                    result = index < actual.Calls.Length ? new(actual.Calls[index], null) : new(null, "直接调用序号越界");
                }
            }
            cache.Add(path, result);
        }
        reason = result.Reason;
        return result.Entry;
    }
}
