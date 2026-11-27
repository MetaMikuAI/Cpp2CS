using System.Collections.Immutable;
using System.Text.Json;
using Cpp2CS.Kernel.Engine;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Kernel.Sources;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>
/// 正向核对。
///   terms [--seed N] [--rounds N]                       项的规范化的语义核对
///   snapshot                                            按前端约定抄写一个语料用例的原生代码，构造快照
///   il --cases 用例清单.json --assemblies 程序集目录     读语料的真实 IL，按操作目录展开，并在展开的图上核对合流的三个操作
///   counterexamples --assemblies 程序集目录              逐项核对有出处的反例（核心库取自程序集目录）
///   native --cases … --assemblies … --binary … --metadata … --symbols …   原生一侧的正向核对：真实 IL 的展开与原生快照共同执行
///   returns --binary … --metadata … [--symbols …]         全映像核对“排在函数范围末尾的调用不返回”
/// </summary>
internal static class Program
{
    private static int Main(string[] arguments)
    {
        if (arguments.Length == 0) return Usage();
        var options = new Dictionary<string, string>();
        for (int i = 1; i + 1 < arguments.Length; i += 2) options[arguments[i]] = arguments[i + 1];
        switch (arguments[0])
        {
            case "sample":
                return Sample.Run(arguments);
            case "returns" when options.ContainsKey("--binary") && options.ContainsKey("--metadata"):
                return ReturnAudit.Run(options["--binary"], options["--metadata"], options.GetValueOrDefault("--symbols"));
            case "keys" or "layouts" when options.TryGetValue("--assemblies", out var assemblies):
                using (var metadata = ModelInput.Load(assemblies, options))
                    return arguments[0] == "keys" ? MetadataAudit.Keys(metadata, options.GetValueOrDefault("--order") == "reverse", options.GetValueOrDefault("--keys-file"))
                        : MetadataAudit.Layouts(metadata);
            case "terms":
                return new TermCheck(int.Parse(options.GetValueOrDefault("--seed", "12345")))
                    .Run(int.Parse(options.GetValueOrDefault("--rounds", "60000")), depth: 4, samples: 16);
            case "snapshot":
                return SnapshotExample.Run();
            case "counterexamples" when options.ContainsKey("--assemblies"):
                return Counterexamples.Run(options["--assemblies"], options);
            case "native" when options.ContainsKey("--cases") && options.ContainsKey("--assemblies") && options.ContainsKey("--binary")
                && options.ContainsKey("--metadata") && options.ContainsKey("--symbols"):
                return NativeCheck.Run(options["--cases"], options["--assemblies"], options["--binary"], options["--metadata"], options["--symbols"],
                    options.GetValueOrDefault("--target", "arm64-v8a"), options.GetValueOrDefault("--show", ""));
            case "recover" when options.ContainsKey("--cases") && options.ContainsKey("--assemblies") && options.ContainsKey("--binary")
                && options.ContainsKey("--metadata") && options.ContainsKey("--symbols"):
                if (arguments.Length % 2 == 0) return Usage();
                return Recover.Run(options["--cases"], options["--assemblies"], options["--binary"], options["--metadata"], options["--symbols"],
                    options.GetValueOrDefault("--target", "arm64-v8a"), options.GetValueOrDefault("--show", ""), options.GetValueOrDefault("--emit"));
            case "il" when options.ContainsKey("--cases") && options.ContainsKey("--assemblies"):
                return CheckIl(options, options["--cases"], options["--assemblies"], int.Parse(options.GetValueOrDefault("--pointer-bits", "64")),
                    options.GetValueOrDefault("--show", ""));
            default:
                return Usage();
        }
    }

    private static int Usage()
    {
        Console.Error.WriteLine("用法：ForwardCheck terms [--seed N] [--rounds N]");
        Console.Error.WriteLine("      ForwardCheck snapshot");
        Console.Error.WriteLine("      ForwardCheck il --cases 用例清单.json --assemblies 程序集目录 [--binary 原生库 --metadata 元数据文件] [--pointer-bits 64] [--show 方法名]");
        Console.Error.WriteLine("      ForwardCheck counterexamples --assemblies 程序集目录 [--binary 原生库 --metadata 元数据文件]");
        Console.Error.WriteLine("      ForwardCheck recover --cases 用例清单.json --assemblies 程序集目录 --binary 原生库 --metadata 元数据文件 --symbols 带符号的原生库 [--show 方法名|all] [--emit 目录]");
        Console.Error.WriteLine("      ForwardCheck native --cases 用例清单.json --assemblies 程序集目录 --binary 原生库 --metadata 元数据文件 --symbols 带符号的原生库 [--show 方法名]");
        Console.Error.WriteLine("      ForwardCheck returns --binary 原生库 --metadata 元数据文件 [--symbols 带符号的原生库]");
        Console.Error.WriteLine("      ForwardCheck keys|layouts --assemblies 程序集目录 [--binary 原生库 --metadata 元数据文件] [--order reverse] [--keys-file 输出文件]");
        return 2;
    }

    private sealed record CaseResult(string Category, string Name, bool Expanded, string Reason, string Detail);

    private static int CheckIl(Dictionary<string, string> options, string casesPath, string assemblies, int pointerBits, string show)
    {
        using var document = JsonDocument.Parse(File.ReadAllBytes(casesPath));
        if (pointerBits != 64) throw new ArgumentException("元数据模型需要 LP64 目标");
        using var metadata = ModelInput.Load(assemblies, options);
        var shared = new TermPool();
        var results = new List<CaseResult>();
        var entryUse = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var entryCases = new Dictionary<string, HashSet<string>>();
        var instructionsSeen = new SortedSet<string>(StringComparer.Ordinal);
        int blocks = 0, effects = 0, instructions = 0, digestsStable = 0, cyclic = 0, mutations = 0, rejected = 0;
        long paths = 0, segments = 0, compared = 0;
        var problems = new List<string>();
        var rows = new RowStats();
        int graphNumber = 1;

        foreach (var item in document.RootElement.EnumerateArray())
        {
            var description = item.GetProperty("case");
            var method = item.GetProperty("method");
            string category = description.GetProperty("category").GetString()!;
            string name = $"{description.GetProperty("type").GetString()}::{description.GetProperty("method").GetString()}";
            try
            {
                var module = metadata.Load(Path.GetFileNameWithoutExtension(method.GetProperty("assembly").GetString()!))
                    ?? throw new ExpansionException("程序集不在目录里", method.GetProperty("assembly").GetString()!);
                int token = Convert.ToInt32(method.GetProperty("token").GetString()!, 16);
                var body = metadata.Body(module, token);
                if (!Convert.ToHexString(body.Code.AsSpan()).Equals(method.GetProperty("il_hex").GetString(), StringComparison.OrdinalIgnoreCase))
                    throw new ExpansionException("IL 与语料记录不一致", "");
                foreach (var instruction in IlDecoder.Decode(body.Code.AsSpan())) instructionsSeen.Add(instruction.Opcode.Name);

                var tokens = metadata.Tokens(module, body.Method.Entity);
                var pool = new TermPool();
                var expansion = IlExpander.Expand(body, metadata.Facts, tokens, pool, 1, pointerBits);
                results.Add(new(category, name, true, "", ""));
                var graph = expansion.Graph;
                blocks += graph.BlockCount;
                effects += graph.Blocks.Sum(b => b.Occurrences.Length);
                instructions += expansion.Entries.Length;
                foreach (var (_, entry) in expansion.Entries)
                {
                    entryUse[entry] = entryUse.GetValueOrDefault(entry) + 1;
                    if (!entryCases.TryGetValue(entry, out var set)) entryCases[entry] = set = [];
                    set.Add(name);
                }

                // 摘要：在另一个已有内容的池里、用另一个图号再展开一次，摘要必须相同。
                var again = IlExpander.Expand(body, metadata.Facts, tokens, shared, ++graphNumber, pointerBits);
                if (again.Graph.DigestText == graph.DigestText) digestsStable++;
                else problems.Add($"{name}：两次展开的摘要不同");

                Exercise(name, graph, pool, problems, rows, ref paths, ref segments, ref compared, ref cyclic);
                Probe(name, graph, pool, problems, ref mutations, ref rejected);
                if (show.Length > 0 && name.EndsWith("::" + show, StringComparison.Ordinal)) Dump(expansion);
            }
            catch (ExpansionException failure)
            {
                results.Add(new(category, name, false, failure.Reason, failure.Message));
            }
            catch (FlowException failure)
            {
                results.Add(new(category, name, false, "展开出的图不满足契约", failure.Message));
            }
        }

        int expanded = results.Count(r => r.Expanded);
        Console.WriteLine($"IL 展开：用例 {results.Count} 个，能展开 {expanded} 个，不能展开 {results.Count - expanded} 个");
        foreach (var group in results.Where(r => !r.Expanded).GroupBy(r => r.Reason).OrderByDescending(g => g.Count()))
        {
            Console.WriteLine($"  {group.Key}：{group.Count()} 个");
            foreach (var failed in group) Console.WriteLine($"    {failed.Name}  {failed.Detail}");
        }
        Console.WriteLine($"  指令 {instructions} 条（不同的助记符 {instructionsSeen.Count} 个），用到目录项 {entryUse.Count} 个（目录共 {OperationCatalog.Entries.Length} 个），" +
            $"块 {blocks} 个，效果 {effects} 个");
        Console.WriteLine($"  摘要与项池、图号无关：{digestsStable}/{expanded}");
        Console.WriteLine($"  构造时的校验：把展开出的图各改坏一处再构造，共 {mutations} 次，被拒绝 {rejected} 次");
        Console.WriteLine($"合流的三个操作（在展开出的图上）：含环的方法 {cyclic} 个；走查的路径 {paths} 条，其中切点之间的段 {segments} 条；" +
            $"走查与分情况逐路径对照 {compared} 条");
        Console.WriteLine($"  路径条件格：不可行的走查路径 {rows.InfeasiblePaths} 条；剔除不可行的行：正向 {rows.ForwardDropped} 行，反向 {rows.BackwardDropped} 行；" +
            $"逐情况提升按可行的各行判为一致 {rows.Consistent} 处，其中计入不可行行的 Lift 判为不一致 {rows.LiftStricter} 处");
        foreach (var entry in OperationCatalog.Entries)
            if (!entryUse.ContainsKey(entry.Id)) Console.WriteLine($"  目录项 {entry.Id} 没有被任何用例用到");
        if (show == "entries")
            foreach (var (entry, count) in entryUse)
                Console.WriteLine($"  {entry,-20} {count,4} 次  {string.Join("、", entryCases[entry].Select(n => n[(n.IndexOf("::", StringComparison.Ordinal) + 2)..]).Take(4))}");
        Console.WriteLine($"问题 {problems.Count} 个");
        foreach (string problem in problems.Take(40)) Console.WriteLine($"  {problem}");
        return expanded == results.Count && problems.Count == 0 ? 0 : 1;
    }

    /// <summary>路径条件格在对照里剔除与判定的计数。</summary>
    private sealed class RowStats
    {
        public long InfeasiblePaths, ForwardDropped, BackwardDropped, Consistent, LiftStricter;
    }

    /// <summary>在一张展开出的图上核对按边代入、分情况、走查与逐情况提升。</summary>
    private static void Exercise(string name, FlowGraph<TemplateEffect> graph, TermPool pool, List<string> problems, RowStats rows,
        ref long paths, ref long segments, ref long compared, ref int cyclic)
    {
        var sources = new ValueSources(graph, pool);
        var shape = sources.Shape;
        var heads = new List<ProgramPoint>();
        for (int b = 0; b < graph.BlockCount; b++)
            if (shape.IsLoopHead(new(b))) heads.Add(new(new(b), 0));
        var entry = new ProgramPoint(graph.Entry, 0);

        var whole = sources.Walk(new Window([entry], []));
        if (heads.Count > 0)
        {
            cyclic++;
            if (whole.Status != WalkStatus.Cyclic) problems.Add($"{name}：有回边，但整体走查没有报告环");
            // 含环：在循环头处切开，逐段走查，每段都必须无环。
            var cut = sources.Walk(new Window([entry, .. heads], [.. heads]));
            if (cut.Status != WalkStatus.Complete) problems.Add($"{name}：在循环头处切开之后仍然走不完（{cut.Status}）");
            paths += cut.Paths.Length;
            segments += cut.Paths.Length;
            return;
        }
        if (whole.Status != WalkStatus.Complete) { problems.Add($"{name}：无回边，但走查没有走完（{whole.Status}）"); return; }
        paths += whole.Paths.Length;

        // 路径数与图上的动态规划一致。
        var counts = new Dictionary<int, long>();
        long Count(int block)
        {
            if (counts.TryGetValue(block, out long known)) return known;
            long total = 0;
            foreach (var exit in graph.Blocks[block].Terminator.Exits) total += exit.Kind == ExitKind.Target ? Count(exit.Target.Index) : 1;
            return counts[block] = total;
        }
        if (Count(graph.Entry.Index) != whole.Paths.Length)
            problems.Add($"{name}：走查得到 {whole.Paths.Length} 条路径，按图计数是 {Count(graph.Entry.Index)} 条");

        // 走查（向前、逐边代入）与分情况（向后展开）对照：同一条路径上，返回值必须是同一组项。
        // 两边的行都先在这条路径的条件之下用路径条件格筛掉不可行的行，各项在该行的条件下求值，再按求值之后的项比较（设计 7.7）。
        var empty = PathConditions.Empty(pool);
        foreach (var path in whole.Paths)
        {
            if (path.End != PathEnd.Return) continue;
            var block = path.ExitPoint.Block;
            var returned = graph.Terminator(block).Exits.Single(e => e.Kind == ExitKind.Return).Arguments;
            if (returned.Length == 0) continue;
            var table = sources.SplitCases(path.ExitPoint, returned);
            if (!table.Complete) { problems.Add($"{name}：分情况的预算耗尽"); continue; }
            if (CaseRows.Assume(empty, path.Conditions, pool) is not { } along) { rows.InfeasiblePaths++; continue; }
            var backward = new HashSet<string>();
            foreach (var item in table.Cases)
            {
                bool onPath = item.Edges.Length <= path.Edges.Length;
                for (int i = 0; onPath && i < item.Edges.Length; i++) onPath = item.Edges[i] == path.Edges[^(i + 1)];
                if (!onPath) continue;
                if (CaseRows.Evaluate(item, along, pool) is { } values) backward.Add(CaseRows.Key(values));
                else rows.BackwardDropped++;
            }
            var forward = new HashSet<string>();
            foreach (var item in sources.SplitCases(path.Entry, path.Outcome).Cases)
            {
                if (CaseRows.Evaluate(item, along, pool) is { } values) forward.Add(CaseRows.Key(values));
                else rows.ForwardDropped++;
            }
            compared++;
            if (!forward.SetEquals(backward))
                problems.Add($"{name}：路径 [{string.Join(" ", path.Edges)}] 上走查与分情况的返回值不同：{string.Join(" | ", forward)} ≠ {string.Join(" | ", backward)}");

            // 逐情况提升：规则是“取这个项”。一致性是“可行的各行相同”：提升的各行与情况表的各行分别筛掉不可行的行、
            // 在该行的条件下求值，两边的判断必须相同。Lift 自己的 Unanimous 计入不可行的行，只会更严，单独计数。
            var lifted = sources.Lift(path.ExitPoint, returned[0], term => term);
            bool liftedSame = lifted.Complete && Agree(lifted.Cases.Select(r => (r.Case, r.Result!)));
            bool same = table.Complete && Agree(sources.SplitCases(path.ExitPoint, [returned[0]]).Cases.Select(c => (c, c.Terms[0])));
            if (liftedSame != same) problems.Add($"{name}：逐情况提升的一致性与情况表不符");
            if (liftedSame) rows.Consistent++;
            if (liftedSame && !lifted.Unanimous) rows.LiftStricter++;
        }

        bool Agree(IEnumerable<(Case Row, Term Value)> items)
        {
            var seen = new HashSet<Term>(ReferenceEqualityComparer.Instance);
            foreach (var (row, value) in items)
                if (CaseRows.Assume(empty, row.Conditions, pool) is { } assumed) seen.Add(assumed.Evaluate(value));
            return seen.Count == 1;
        }
    }

    /// <summary>
    /// 构造时校验的核对：把一张真实的图原样重放，摘要必须不变；再各改坏一处（少一个实参、实参换成别的块的值、
    /// 实参位宽不符、指向入口块、漏掉终结），每一种都必须被拒绝。
    /// </summary>
    private static void Probe(string name, FlowGraph<TemplateEffect> graph, TermPool pool, List<string> problems, ref int mutations, ref int rejected)
    {
        FlowGraph<TemplateEffect> Replay(Func<BlockId, Exit, Exit>? change, int unterminated)
        {
            var builder = new FlowBuilder<TemplateEffect>(pool, graph.Graph);
            foreach (var parameter in graph.EntryParameters) builder.EntryParameter(parameter.Slot, parameter.Width);
            builder.SetReturnWidths(graph.ReturnWidths.AsSpan());
            for (int b = 1; b < graph.BlockCount; b++) builder.Block([.. graph.Blocks[b].Parameters.Select(p => p.Width)]);
            foreach (var block in graph.Blocks)
            {
                foreach (var occurrence in block.Occurrences) builder.Append(block.Id, occurrence);
                if (block.Id.Index == unterminated) continue;
                var terminator = block.Terminator;
                ImmutableArray<Exit> exits = [.. terminator.Exits.Select(e => change is null ? e : change(block.Id, e))];
                builder.Terminate(block.Id, terminator.Kind switch
                {
                    TerminatorKind.Single => Terminator.Single(exits[0]),
                    TerminatorKind.Branch => Terminator.Branch(terminator.Condition!, exits[0], exits[1]),
                    TerminatorKind.Switch => Terminator.Switch(terminator.Condition!, exits),
                    _ => Terminator.Invoke(exits[0], exits[1]),
                });
            }
            return builder.Build();
        }

        if (Replay(null, -1).DigestText != graph.DigestText) problems.Add($"{name}：原样重放之后摘要变了");

        // 取第一条带实参、且目标不是源块自己的边作为改动的对象。
        (BlockId Source, Exit Exit)? victim = null;
        foreach (var block in graph.Blocks)
            foreach (var exit in block.Terminator.Exits)
                if (victim is null && exit.Kind == ExitKind.Target && exit.Arguments.Length > 0 && exit.Target != block.Id) victim = (block.Id, exit);
        var changes = new List<(string What, Func<BlockId, Exit, Exit>? Change, int Unterminated)>
        {
            ("漏掉最后一个块的终结", null, graph.BlockCount - 1),
        };
        if (victim is { } v)
        {
            bool Hit(BlockId source, Exit exit) => source == v.Source && ReferenceEquals(exit, v.Exit);
            var foreign = graph.Parameters(v.Exit.Target)[0];
            var first = v.Exit.Arguments[0];
            var resized = first.Width > 1 ? pool.Truncate(first, first.Width - 1) : pool.ZeroExtend(first, 2);
            changes.Add(("少一个实参", (s, e) => Hit(s, e) ? Exit.To(e.Target, e.Arguments.AsSpan()[..^1]) : e, -1));
            changes.Add(("实参换成目标块自己的参数", (s, e) => Hit(s, e) ? Exit.To(e.Target, [foreign, .. e.Arguments.AsSpan()[1..]]) : e, -1));
            changes.Add(("实参位宽不符", (s, e) => Hit(s, e) ? Exit.To(e.Target, [resized, .. e.Arguments.AsSpan()[1..]]) : e, -1));
            changes.Add(("指向入口块", (s, e) => Hit(s, e) ? Exit.To(graph.Entry) : e, -1));
        }
        foreach (var (what, change, unterminated) in changes)
        {
            mutations++;
            try
            {
                Replay(change, unterminated);
                problems.Add($"{name}：改坏之后（{what}）仍然通过了校验");
            }
            catch (FlowException)
            {
                rejected++;
            }
        }
    }

    private static void Dump(Expansion expansion)
    {
        var graph = expansion.Graph;
        foreach (var block in graph.Blocks)
        {
            Console.WriteLine($"{block.Id}（IL_{expansion.BlockOffsets[block.Id.Index]:x4}）参数 {block.Parameters.Length} 个");
            for (int i = 0; i < block.Occurrences.Length; i++)
            {
                var effect = block.Occurrences[i];
                Console.WriteLine($"    {i}: {effect.Kind} {effect.Location} {effect.Exception} {effect.Function} {effect.Entity} [{effect.Entry}]");
                foreach (var operand in effect.Operands) Console.WriteLine($"         {operand}");
            }
            var terminator = block.Terminator;
            if (terminator.Condition is not null) Console.WriteLine($"    {terminator.Kind} {terminator.Condition}");
            foreach (var exit in terminator.Exits)
                Console.WriteLine($"    → {exit.Kind} {(exit.Kind == ExitKind.Target ? exit.Target.ToString() : "")} {string.Join("; ", exit.Arguments)}");
        }
    }
}
