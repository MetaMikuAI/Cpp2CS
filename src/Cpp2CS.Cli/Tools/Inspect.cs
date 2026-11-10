using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Convert = System.Convert;
using Cpp2CS.Recovery;

namespace Cpp2CS.Cli;

/// <summary>逐层打印方法的恢复产物（调试用）。目标为十六进制入口或方法清单文件。</summary>
internal static class Inspect
{
    internal static int Run(string binary, string metadata, string[] options)
    {
        string? cache = null;
        var targets = new List<string>();
        for (var i = 0; i < options.Length; i++)
        {
            if (options[i] == "--fact-cache-file" && i + 1 < options.Length) cache = Path.GetFullPath(options[++i]);
            else if (options[i] is "--brief" or "--calls" or "--inline") continue;
            else targets.Add(options[i]);
        }
        var facts = FactsBuilder.Build(binary, metadata, options: new Cpp2CS.Options.RecoveryOptions { FactCacheFile = cache });
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var decompiler = new MethodDecompiler(facts, types);
        foreach (var target in Targets(facts, types, targets))
        {
            Console.Write($"== 0x{target.Entry:x} {target.Instance}");
            var method = target.Shared ? decompiler.BindShared(target.Instance, target.Entry) : target.Instance;
            if (!decompiler.Analyze(method, target.Entry).TryGet(out var analysis, out var failure))
            {
                Console.WriteLine($"\n  ! 0x{failure.Address:x} {failure.Reason}");
                continue;
            }
            Console.WriteLine(analysis.Splits > 0 ? $" 拆分 {analysis.Splits}" : "");
            if (!options.Contains("--brief")) Print(analysis);
            if (options.Contains("--calls"))
                foreach (var call in analysis.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => c is { Op: null, Target: Const }))
                    if (decompiler.Shapes.Of(call).Signature is null && facts.Unregistered.Decisions.FirstOrDefault(d => d.Address == ((Const)call.Target).Value) is { } decision)
                        Console.WriteLine($"  未注册 0x{call.Address:x} → 0x{decision.Address:x}：{decision.Reason}");
                    else if (decompiler.Shapes.Of(call).Signature is null)
                        foreach (var (candidate, signature, problem) in decompiler.Shapes.Candidates(((Const)call.Target).Value))
                            Console.WriteLine($"  无签名调用 0x{call.Address:x} 候选 {candidate}：{(signature is null ? problem : string.Join(", ", signature.Arguments.Select(a => $"{a.Index}:{a.Transfer}/{a.Size}")))}");
            if (options.Contains("--inline"))
            {
                Cpp2CS.Recovery.Inlining.InlineTrace.Sink = Console.WriteLine;
                Cpp2CS.Recovery.Inlining.InlineTrace.Method = method.Method;
                Cpp2CS.Recovery.Inlining.InlineTrace.Print = body => { foreach (var line in ManagedPrinter.Lines(body)) Console.WriteLine(line); };
                Cpp2CS.Recovery.Inlining.InlineTrace.Lines = ManagedPrinter.Lines;
                Cpp2CS.Recovery.Inlining.InlineTrace.Before = body =>
                {
                    Console.WriteLine("  -- 内联证明之前");
                    foreach (var line in ManagedPrinter.Lines(body)) Console.WriteLine(line);
                    Console.WriteLine("  -- 证明");
                };
            }
            var result = decompiler.Lower(analysis);
            Cpp2CS.Recovery.Inlining.InlineTrace.Sink = null;
            Cpp2CS.Recovery.Inlining.InlineTrace.Print = null;
            Cpp2CS.Recovery.Inlining.InlineTrace.Lines = null;
            Cpp2CS.Recovery.Inlining.InlineTrace.Before = null;
            foreach (var rejection in analysis.Idioms.Rejections) Console.WriteLine($"  拒绝 {rejection.Rule} 0x{rejection.Address:x} {rejection.Reason}");
            foreach (var hole in result.Holes) Console.WriteLine($"  洞 0x{hole.Address:x} {hole.Reason}");
            if ((result.Body ?? result.Partial) is { } body)
                foreach (var line in ManagedPrinter.Lines(body)) Console.WriteLine(line);
        }
        return 0;
    }

    private static IEnumerable<RecoveryTarget> Targets(ProgramFacts facts, ManagedTypes types, List<string> targets)
    {
        foreach (var target in targets)
        {
            if (File.Exists(target))
            {
                foreach (var line in File.ReadLines(target).Where(l => l.Length > 0))
                {
                    var fields = line.Split('\t');
                    yield return RecoveryTarget.Find(facts, Convert.ToUInt64(fields[0], 16), fields[1]);
                }
                continue;
            }
            if (target.StartsWith("name:", StringComparison.Ordinal))
            {
                // 共享泛型定义没有自己的地址，按写出时选用的见证入口查找；名字可写开放形式（Owner<T>.Method<U>）。
                foreach (var definition in new MethodEntries(facts, types).Definitions.Where(e => e.Instance.Method is var m
                    && ($"{m.Owner.FullName}.{m.Name}" == target[5..] || MethodRef.Open(m).ToString() == target[5..])))
                    yield return new RecoveryTarget(definition.Instance.Method.Address != 0 ? MethodRef.Open(definition.Instance.Method) : definition.Instance, definition.Address);
                continue;
            }
            var entry = Convert.ToUInt64(target.StartsWith("0x", StringComparison.Ordinal) ? target[2..] : target, 16);
            var method = facts.EntriesAt(entry).FirstOrDefault(e => e.Method is not null && e.Kind is EntryKind.Method or EntryKind.GenericMethod)?.Method
                ?? throw new InvalidDataException($"0x{entry:x} 处没有托管方法");
            yield return new RecoveryTarget(method, entry);
        }
    }

    private static void Print(MethodAnalysis analysis)
    {
        var values = analysis.Values;
        Console.WriteLine($"  签名: {string.Join(", ", analysis.Signature.Arguments.Select(a => $"{a.Index}:{a.Type} {a.Transfer} [{string.Join(" ", a.Pieces.Select(p => $"{p.Register}+{p.Offset}"))}]"))}"
            + (analysis.Signature.Return is { } r ? $" → {r.Type} {r.Transfer}" : ""));
        foreach (var cell in analysis.Memory.Cells) Console.WriteLine($"  {cell}");
        Console.WriteLine($"  符号值求值 {values.Passes} 轮");
        foreach (var block in analysis.Function.Blocks)
        {
            Console.WriteLine($"  B{block.Index}@0x{block.Start:x} <- [{string.Join(", ", block.Predecessors.Select(p => "B" + p.Index))}]"
                + (block.IsLandingPad ? " 落地块" : "") + (block.Handler is { } handler ? $" 异常→B{handler.Index}" : ""));
            foreach (var statement in block.Statements)
            {
                Console.WriteLine($"    {statement.Address:x}: {statement}");
                switch (statement)
                {
                    case Define define:
                        Console.WriteLine($"        ⇒ {values.Of(define.Target)}");
                        break;
                    case Phi phi:
                        Console.WriteLine($"        ⇒ {values.Of(phi.Target)}");
                        break;
                    case Call call:
                        Console.WriteLine($"        ⇒ ({string.Join(", ", values.Operands(call).Skip(1).Take(call.Arguments.Length))})"
                            + string.Concat(call.Defines.Where(d => d is not null).Select(d => $" {d} = {values.Of(d!)}")));
                        break;
                    default:
                        if (values.Operands(statement) is { Count: > 0 } operands)
                            Console.WriteLine($"        ⇒ {string.Join(", ", operands)}");
                        break;
                }
            }
        }
        foreach (var phi in values.Syms.Phis.Where(p => p.Forward is null))
            Console.WriteLine($"  {phi} @B{phi.Block.Index} = φ({string.Join(", ", phi.Sources.Select(s => s?.ToString() ?? "?"))})");
    }
}
