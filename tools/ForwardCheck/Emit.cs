using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Engine;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Output;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>只收恢复主线已判等价的用例。写入副本后，从该副本的 MethodDef、签名和指令重新建立对照。</summary>
internal sealed class Emit(string directory, string assemblies, SrmMetadata metadata, BridgeFacts facts)
{
    internal sealed record Case(Module Module, int Token, string Name, string Signature, ManagedBody Input,
        MethodBody Real, TermPool Terms, int PointerBits);
    public List<Case> Cases { get; } = [];
    private int holes, methods, instructions, pairs, unchanged, absent, nextGraph = 1;
    private readonly SortedDictionary<int, int> peaks = [];

    public void CheckHoles(Module module, ManagedBody body)
    {
        var tokens = new SrmMetadata.EmitTokens(metadata, module, body.Host.Entity);
        var rejected = CilWriter.Write(body, tokens, metadata.Facts,
            _ => throw new InvalidDataException("有洞的方法登记了局部签名"), tokens.TypeSignature);
        if (rejected.Body != null || string.IsNullOrEmpty(rejected.Reason) || !rejected.Holes.SequenceEqual(body.Holes))
            throw new InvalidDataException("有洞的方法没有带原因和原洞列表返回");
        holes++;
    }

    public bool Run(int equivalent, int crossPairs)
    {
        var staged = new List<(string Temp, string Destination)>();
        try
        {
            Directory.CreateDirectory(directory);
            if (PhysicalPath(new(directory)) == PhysicalPath(new(assemblies))) throw new InvalidDataException("写出副本需要与输入不同的目录");
            foreach (var group in Cases.GroupBy(c => c.Module))
            {
                var source = group.Key;
                var output = new EmitAssembly(source);
                foreach (var item in group)
                {
                    var tokens = new SrmMetadata.EmitTokens(metadata, source, item.Input.Host.Entity);
                    var result = CilWriter.Write(item.Input, tokens, metadata.Facts, output.RegisterLocals, tokens.TypeSignature);
                    output.Replace(item.Token, result.Body ?? throw new InvalidDataException($"{item.Name}：{result.Reason}"));
                }
                string path = Path.Combine(directory, Guid.NewGuid() + ".local.tmp");
                staged.Add((path, Path.Combine(directory, source.Image)));
                output.Write(path);
                using var copy = new Module(path);
                output.CheckMetadata(copy);
                CheckBodies(source, copy, output);
                foreach (var item in group) CheckCase(item, copy);
            }
            if (methods != equivalent || pairs != crossPairs)
                throw new InvalidDataException($"回读用例 {methods}/{equivalent}，交叉对照 {pairs}/{crossPairs} 对");
            foreach (var (path, destination) in staged) File.Move(path, destination, overwrite: true);
            Console.WriteLine($"CIL 回读等价 {methods}/{equivalent}，交叉反驳 {pairs}/{crossPairs}；有洞拒写 {holes}");
            Console.WriteLine($"编码往返 {methods}/{Cases.Count}，逐条相同 {instructions} 条；栈深 {methods}/{Cases.Count}，峰值分布（栈深:方法数）{string.Join("，", peaks.Select(p => $"{p.Key}:{p.Value}"))}");
            Console.WriteLine($"程序集读回 {staged.Count} 个，替换体及签名相同 {methods} 个，未替换体字节相同 {unchanged} 个，另有无体 MethodDef {absent} 个");
            return true;
        }
        catch (InvalidDataException e) { Console.Error.WriteLine($"CIL 写出失败：{e.Message}"); }
        catch (ExpansionException e) { Console.Error.WriteLine($"CIL 元数据或展开失败：{e.Message}"); }
        catch (BadImageFormatException e) { Console.Error.WriteLine($"CIL 副本格式无效：{e.Message}"); }
        finally
        {
            foreach (var (path, _) in staged) File.Delete(path);
        }
        return false;
    }

    private static string PhysicalPath(DirectoryInfo directory)
    {
        if (directory.ResolveLinkTarget(true) is DirectoryInfo target) return PhysicalPath(target);
        return directory.Parent == null ? directory.FullName : Path.Combine(PhysicalPath(directory.Parent), directory.Name);
    }

    private void CheckBodies(Module source, Module copy, EmitAssembly output)
    {
        if (copy.Image != source.Image || copy.Md.MethodDefinitions.Count != source.Md.MethodDefinitions.Count)
            throw new InvalidDataException("副本的模块名或 MethodDef 数改变");
        foreach (var h in source.Md.MethodDefinitions)
        {
            int token = MetadataTokens.GetToken(h);
            int original = source.Md.GetMethodDefinition(h).RelativeVirtualAddress;
            int rva = copy.Md.GetMethodDefinition(h).RelativeVirtualAddress;
            if (output.Replacements.TryGetValue(token, out var written))
            {
                var block = copy.Pe.GetMethodBody(rva);
                var bytes = copy.Pe.GetSectionData(rva).GetContent(0, block.Size);
                byte[] signature = block.LocalSignature.IsNil ? [] : copy.Md.GetBlobBytes(copy.Md.GetStandaloneSignature(block.LocalSignature).Signature);
                if (!bytes.AsSpan().SequenceEqual(written.Bytes.AsSpan()) || !signature.AsSpan().SequenceEqual(written.LocalSignature.AsSpan()))
                    throw new InvalidDataException($"MethodDef 0x{token:x8} 的方法体或局部签名与写入字节不一致");
                if ((bytes[0] & 3) == 3 && !block.LocalVariablesInitialized)
                    throw new InvalidDataException($"MethodDef 0x{token:x8} 大头缺少 InitLocals");
                continue;
            }
            if (rva != original) throw new InvalidDataException($"未替换的 MethodDef 0x{token:x8} 的 RVA 改变");
            if (original == 0) { absent++; continue; }
            var a = source.Pe.GetSectionData(original).GetContent(0, source.Pe.GetMethodBody(original).Size);
            var b = copy.Pe.GetSectionData(rva).GetContent(0, copy.Pe.GetMethodBody(rva).Size);
            if (!a.AsSpan().SequenceEqual(b.AsSpan())) throw new InvalidDataException($"未替换的 MethodDef 0x{token:x8} 方法体改变");
            unchanged++;
        }
    }

    private void CheckCase(Case item, Module copy)
    {
        var body = metadata.Body(copy, item.Token);
        var tokens = metadata.Tokens(copy, body.Method.Entity);
        var decoded = IlDecoder.Decode(body.Code.AsSpan());
        EmitChecks.Instructions(item.Input, decoded, tokens);
        int rva = copy.Md.GetMethodDefinition((MethodDefinitionHandle)MetadataTokens.EntityHandle(item.Token)).RelativeVirtualAddress;
        int peak = EmitChecks.Stack(decoded, tokens, metadata.Facts, body.Method, copy.Pe.GetMethodBody(rva).MaxStack);
        peaks[peak] = peaks.GetValueOrDefault(peak) + 1;
        instructions += decoded.Length;
        foreach (var expected in Cases)
        {
            if (expected.Signature != item.Signature || (expected != item && expected.Name == item.Name)) continue;
            var left = IlExpander.Expand(expected.Real, metadata.Facts, metadata.Tokens(expected.Module, expected.Real.Method.Entity),
                expected.Terms, nextGraph++, expected.PointerBits);
            var right = IlExpander.Expand(body, metadata.Facts, tokens, expected.Terms, nextGraph++, expected.PointerBits);
            var result = CoExecution.Equivalent(left.Graph, right.Graph, expected.Real, facts, metadata.Callees(expected.Terms, expected.PointerBits));
            if (expected == item)
            {
                if (result.Verdict != Verdict.Proved) throw new InvalidDataException($"{item.Name} 回读未证等价：{result.Detail}");
                methods++;
            }
            else
            {
                if (result.Verdict == Verdict.Proved) throw new InvalidDataException($"{expected.Name} 与 {item.Name} 的交叉对照被证明等价");
                if (result.Verdict is Verdict.Budget or Verdict.MissingFact or Verdict.MissingIndependence)
                    throw new InvalidDataException($"{expected.Name} 与 {item.Name} 的交叉对照缺少判定依据：{result.Detail}");
                pairs++;
            }
        }
    }
}
