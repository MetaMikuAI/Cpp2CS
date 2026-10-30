using System.Security.Cryptography;
using Cpp2CS.Facts;

namespace Cpp2CS.Extensions.Closure;

/// <summary>访问器身份与方法体指纹；执行证据必须匹配原生字节及 CIL。无原生代码单列语言定义，不写入 verified。</summary>
public static class AccessorEvidence
{
    public static string Describe(ProgramFacts facts, Skeleton skeleton, FieldAccessor accessor, byte[]? preview = null)
    {
        var method = accessor.Method.Method;
        var cil = Convert.ToHexString(SHA256.HashData(preview ?? CilBodyFingerprint.Describe(skeleton.Method(method))));
        if (method.Address == 0 && accessor.LanguageDefined)
            return $"0x0\t{accessor.Method}\tlanguage-defined\t{cil}";
        var function = facts.Code.At(method.Address) ?? throw new InvalidDataException($"访问器 0x{method.Address:x} 无 L0 边界");
        var native = Convert.ToHexString(SHA256.HashData(facts.Code.Image.Read(method.Address, checked((int)function.Size))));
        return $"0x{method.Address:x}\t{accessor.Method}\t{native}\t{cil}";
    }

    /// <summary>内联认回的被调方法：与访问器相同的身份与指纹格式，执行证据共用一个文件。</summary>
    public static string Describe(ProgramFacts facts, Skeleton skeleton, MethodRef method, byte[]? preview = null)
    {
        var cil = Convert.ToHexString(SHA256.HashData(preview ?? CilBodyFingerprint.Describe(skeleton.Method(method.Method))));
        var function = facts.Code.At(method.Method.Address) ?? throw new InvalidDataException($"方法 0x{method.Method.Address:x} 无 L0 边界");
        var native = Convert.ToHexString(SHA256.HashData(facts.Code.Image.Read(method.Method.Address, checked((int)function.Size))));
        return $"0x{method.Method.Address:x}\t{method}\t{native}\t{cil}";
    }

    public static HashSet<string> Read(string? path) => path is null ? [] : File.ReadLines(path).Where(l => l.Length > 0 && !l.StartsWith('#')).ToHashSet(StringComparer.Ordinal);

    public static void Write(string path, IEnumerable<string> evidence) => File.WriteAllLines(path,
        new[] { "# F9：访问器自身全部 32 用例 verified；入口、身份、原生 SHA256、CIL SHA256" }.Concat(evidence.Distinct().Order(StringComparer.Ordinal)));
}
