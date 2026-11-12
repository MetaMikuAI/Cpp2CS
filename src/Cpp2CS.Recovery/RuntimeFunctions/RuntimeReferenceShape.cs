using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.RuntimeFunctions;

/// <summary>按首次使用编号映像引用与内部调用；保持引用相等关系，不抹去普通常量。</summary>
public sealed record RuntimeReferenceShape(string Text, ulong[] Calls)
{
    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<IImage, Dictionary<ulong, string>> typeExportCache = new();
    public bool HasImportCalls { get; init; }
    public static RuntimeReferenceShape? Create(NativeFunction function, Func<CallTarget, CallTarget> normalize, IImage? source = null, Action<string>? missing = null)
    {
        var references = new Dictionary<ulong, int>();
        var calls = new Dictionary<ulong, int>();
        bool supported = true;
        void Reject(string reason) { supported = false; missing?.Invoke(reason); }
        bool hasImportCalls = false;
        // 子句已经是异常表解析后的目标，不能把类型表槽位或匿名数据序号当作类型身份。
        string Reference(ulong address)
        {
            if (!references.TryGetValue(address, out int index)) references.Add(address, index = references.Count);
            var identity = index.ToString(System.Globalization.CultureInfo.InvariantCulture);
            if (source is null) return identity;
            var storage = source.Query(address);
            if (storage.Storage == StorageKind.Unmapped) Reject("映像引用未映射");
            return $"{identity}/{storage.Storage}/{storage.Executable}/{storage.Writable}";
        }
        string? TermDescription(Term term)
        {
            if (term.Kind == TermKind.Unknown) Reject("原生 IR 含未知项");
            ulong? address = term.Identity is RootAtom { Kind: AddressRoot.Image } ? 0 : null;
            if (term.Operator is CoreOperator { Operation: CoreOperation.Add } && term.Operands.Length == 2)
            {
                var root = term.Operands.FirstOrDefault(t => t.Identity is RootAtom { Kind: AddressRoot.Image });
                var offset = term.Operands.FirstOrDefault(t => t.Kind == TermKind.Constant);
                if (root is not null && offset?.ConstantValue is { } value && value <= ulong.MaxValue)
                    address = (ulong)value;
            }
            if (address is not { } a) return null;
            return $"image-reference[{Reference(a)}]:{term.Width}";
        }
        string? TargetDescription(CallTarget target)
        {
            target = normalize(target);
            if (target is ImportedTarget import)
            { hasImportCalls = true; return "import " + System.Text.Json.JsonSerializer.Serialize(import.Symbol); }
            // 间接目标仍由转储按完整项表示写出；未知项由项检查拒绝。
            if (target is ComputedTarget computed)
            {
                if (computed.Value.ContainsUndefined) Reject("间接调用目标含未定义位");
                return null;
            }
            if (target is not ImageFunction image) throw new InvalidOperationException("未知调用目标种类");
            if (!calls.TryGetValue(image.EntryOffset, out int index)) calls.Add(image.EntryOffset, index = calls.Count);
            return $"image-call[{index}]=image-reference[{Reference(image.EntryOffset)}]";
        }
        string MatchDescription(PointerTarget target)
        {
            if (target is PointerTarget.Import import)
                return "import " + System.Text.Json.JsonSerializer.Serialize(import.Symbol)
                    + "+" + import.Addend.ToString(System.Globalization.CultureInfo.InvariantCulture);
            if (target is PointerTarget.Internal data && source is not null
                && source.Query(data.Offset) is { Storage: not StorageKind.Unmapped, Executable: false }
                && typeExportCache.GetValue(source, image => image.Exports.GroupBy(e => e.Name, StringComparer.Ordinal)
                    .Where(g => g.Select(e => e.Target).Distinct().Count() == 1 && g.First().Target is PointerTarget.Internal)
                    .Select(g => (g.Key, Offset: ((PointerTarget.Internal)g.First().Target).Offset))
                    .GroupBy(e => e.Offset).ToDictionary(g => g.Key, g => g.Select(e => e.Key).Order(StringComparer.Ordinal).First()))
                    .TryGetValue(data.Offset, out var name))
                return "export:" + System.Text.Json.JsonSerializer.Serialize(name) + " image-reference[" + Reference(data.Offset) + "]";
            Reject("异常子句的类型信息目标没有唯一导出身份");
            return "unresolved-type";
        }
        var text = TextDump.Write(function, termDescription: TermDescription, targetDescription: TargetDescription,
            matchDescription: MatchDescription);
        return supported ? new(text, calls.OrderBy(p => p.Value).Select(p => p.Key).ToArray()) { HasImportCalls = hasImportCalls } : null;
    }
}
