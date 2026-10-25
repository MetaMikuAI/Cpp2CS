using Cpp2CS.Facts;
using Cpp2CS.Idioms;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Lifting;

namespace Cpp2CS.Tests;

/// <summary>诊断：打印一个函数提升并经 L2 归一之后的 IR（逐块，含前驱与 φ）。CPP2CS_FRAME_SLOTS=off 可对比帧槽提升之前的形态。</summary>
internal static class IrDump
{
    [Command("ir-dump", "打印函数在提升与 L2 之后的 IR", Arguments = "<binary> <metadata> <入口地址…>")]
    public static int Run(string binary, string metadata, string[] entries)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var lifter = new FunctionLifter(facts);
        var rewriter = new IdiomRewriter(facts) { RecordFilter = _ => false };
        foreach (var text in entries)
        {
            var entry = System.Convert.ToUInt64(text, 16);
            var lifted = lifter.Lift(entry);
            Console.WriteLine($"== 0x{entry:x}{(lifted.Succeeded ? "" : "（提升失败：" + string.Join("；", lifted.Errors) + "）")}");
            if (!lifted.Succeeded) continue;
            var idioms = rewriter.Run(lifted.Function);
            foreach (var error in idioms.Errors) Console.WriteLine($"  L2 错误 {error}");
            foreach (var block in lifted.Function.Blocks)
            {
                Console.WriteLine($"B{block.Index}@0x{block.Start:x}{(block.IsLandingPad ? " 落地块" : "")} ← {string.Join(",", block.Predecessors.Select(p => $"B{p.Index}"))}");
                foreach (var statement in block.Statements) Console.WriteLine($"  0x{statement.Address:x}  {statement}");
            }
        }
        return 0;
    }
}

/// <summary>诊断：只跑 L3，打印方法的全部洞（含连带洞）；无洞时打印托管方法体的语句。</summary>
internal static class RecoverDump
{
    [Command("recover-dump", "只跑 L3，打印方法的洞或托管方法体", Arguments = "<binary> <metadata> <入口地址…>")]
    public static int Run(string binary, string metadata, string[] entries)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new Cpp2CS.Recovery.ManagedTypes(facts.Model, facts.Layouts);
        var recovery = new Cpp2CS.Recovery.MethodRecovery(facts, types);
        foreach (var text in entries)
        {
            var sourceView = text.StartsWith("source:", StringComparison.Ordinal);
            var selection = sourceView ? text[7..] : text;
            var shared = selection.StartsWith("shared:", StringComparison.Ordinal);
            if (shared) selection = selection[7..];
            // 十六进制入口，或方法全名的一部分（只取有代码、非泛型的前 20 个）。
            var isAddress = ulong.TryParse(selection, System.Globalization.NumberStyles.HexNumber, null, out var parsed);
            var methods = isAddress ? facts.Model.Methods.Where(m => m.Address == parsed)
                : facts.Model.Methods.Where(m => m.Address != 0 && m.GenericParameters.Count == 0 && m.Owner.GenericParameters.Count == 0 && m.ToString().Contains(selection, StringComparison.Ordinal)).Take(20);
            // 没有方法定义的地址：按该处登记的泛型实例恢复（封闭实例）。
            var instances = isAddress && !methods.Any() ? facts.EntriesAt(parsed).Where(e => e.Kind == EntryKind.GenericMethod && e.Method is not null)
                .Select(e => shared ? recovery.RecoverShared(e.Method!, parsed) : recovery.RecoverInstance(e.Method!, parsed)).Take(1).ToArray() : [];
            foreach (var result in instances.Concat(methods.Select(m => recovery.Recover(new Cpp2CS.Model.MethodRef(m, [], []), m.Address))))
            {
                var entry = result.Entry;
                var method = result.Method;
                Console.WriteLine($"== 0x{entry:x} {method}：{(result.Body is null ? $"{result.Holes.Count} 个洞" : "无洞")}");
                foreach (var hole in result.Holes) Console.WriteLine($"  0x{hole.Address:x} {(hole.Derived ? "连带" : "独立")} {hole.Reason}");
                if ((result.Body ?? result.Partial) is { } body)
                {
                    if (sourceView) body = Cpp2CS.Recovery.SourceRewriter.Rewrite(body, types);
                    foreach (var region in body.Regions) Console.WriteLine($"  {Show(region)}");
                    foreach (var block in body.Blocks)
                    {
                        Console.WriteLine($"  B@0x{block.Address:x}");
                        foreach (var statement in block.Statements) Console.WriteLine($"    0x{statement.Address:x} {Show(statement)}");
                    }
                }
            }
        }
        return 0;
    }

    /// <summary>紧凑打印：托管值按 种类(子项…) 展开，列表逐项展开。</summary>
    private static string Show(object? value) => value switch
    {
        null => "null",
        string text => text,
        Cpp2CS.Recovery.LocalValue local => $"{local.Variable}:{local.Type}",
        Cpp2CS.Recovery.ArgumentValue argument => $"arg{argument.Index}",
        Cpp2CS.Recovery.ConstantValue constant => $"0x{constant.Bits:x}:{constant.Type}",
        Cpp2CS.Recovery.FieldValue field => $"{Show(field.Receiver)}.{field.Field.Field.Name}",
        Cpp2CS.Recovery.AddressValue address => $"&{Show(address.Target)}",
        Cpp2CS.Recovery.IndirectValue indirect => $"*{Show(indirect.Address)}",
        System.Collections.IEnumerable list => "[" + string.Join(", ", list.Cast<object?>().Select(Show)) + "]",
        _ when value.GetType().Namespace == "Cpp2CS.Recovery" && value.GetType().IsClass => value.GetType().Name.Replace("Managed", "").Replace("Value", "") + "("
            + string.Join(", ", value.GetType().GetProperties().Where(p => p.Name is not ("Address" or "EqualityContract" or "Width") || value is Cpp2CS.Recovery.IndirectValue)
                .Select(p => $"{p.Name}={Show(p.GetValue(value))}")) + ")",
        _ => value.ToString() ?? "",
    };
}

/// <summary>诊断：对清单中的方法跑 L3 与 F9/内联认回闭包（假定候选全部已验证），打印候选、认回前后的写出问题与仍越权的语句。</summary>
internal static class ClosureDump
{
    [Command("closure-dump", "打印内联认回的候选与认回前后的写出问题", Arguments = "<binary> <metadata> <清单>")]
    public static int Run(string binary, string metadata, string list)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new Cpp2CS.Recovery.ManagedTypes(facts.Model, facts.Layouts);
        var recovery = new Cpp2CS.Recovery.MethodRecovery(facts, types);
        var entries = File.ReadLines(list).Where(l => l.Length > 0 && !l.StartsWith('#')).Select(l => System.Convert.ToUInt64(l.Split('\t')[0], 16)).ToHashSet();
        var results = facts.Model.Methods.Where(m => entries.Contains(m.Address)).Select(m => recovery.Recover(new Cpp2CS.Model.MethodRef(m, [], []), m.Address)).ToArray();
        var skeleton = new Cpp2CS.Output.Skeleton(facts.Model);
        var emitter = new Cpp2CS.Output.BodyEmitter(skeleton, types);
        var closure = new Cpp2CS.Output.AccessorRecovery(facts, types, recovery, emitter, results);
        var before = results.ToDictionary(r => r.Method.Method, r => r.Body is { } b ? closure.Problems.GetValueOrDefault(b) : "有洞");
        Console.WriteLine($"内联候选 {closure.InlineCandidates.Count}：{string.Join("，", closure.InlineCandidates.Keys.Select(m => m.ToString()))}");
        Console.WriteLine($"泛型访问器 {closure.GenericAccessors.Count}：{string.Join("，", closure.GenericAccessors.Select(a => a.Method.ToString()))}");
        foreach (var access in closure.Accesses) Console.WriteLine($"  越权 {access.Value.GetType().Name} {Cpp2CS.Recovery.FieldAccessor.FieldOf(access.Value)} 写 {access.Write}：候选 {access.Candidates.Length}");
        closure.Rewrite(types, emitter, _ => true, _ => true);
        foreach (var result in closure.Targets)
        {
            var owner = result.Method.Method.Owner;
            Console.WriteLine($"== {result.Method}：认回前 {before[result.Method.Method]}；认回后 {(result.Body is { } b ? closure.Problems.GetValueOrDefault(b) ?? "可写出" : "有洞")}；内联调用 {result.Body?.Blocks.SelectMany(x => x.Statements).OfType<Cpp2CS.Recovery.ManagedCall>().Count(c => c.Inlined)}");
            if (result.Body is null) continue;
            foreach (var block in result.Body.Blocks)
                foreach (var statement in block.Statements)
                    if (Cpp2CS.Recovery.ManagedValues.Of(statement).SelectMany(Cpp2CS.Recovery.ManagedValues.Walk).Any(v => v is Cpp2CS.Recovery.FieldValue f && !Cpp2CS.Recovery.ManagedAccess.Field(types, owner, f.Field, f.Receiver.Type)))
                        Console.WriteLine($"  B@0x{block.Address:x} 越权：{statement}");
        }
        return 0;
    }
}

/// <summary>诊断：列出入口地址上登记的全部条目（方法、泛型实例、调用器等）。</summary>
internal static class EntriesDump
{
    [Command("entries", "列出地址上登记的条目", Arguments = "<binary> <metadata> <入口地址…>")]
    public static int Run(string binary, string metadata, string[] entries)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        foreach (var text in entries)
        {
            var entry = System.Convert.ToUInt64(text, 16);
            Console.WriteLine($"== 0x{entry:x}");
            foreach (var e in facts.EntriesAt(entry)) Console.WriteLine($"  {e.Kind} {e.Method}");
        }
        return 0;
    }
}

/// <summary>诊断：按名称片段列出注册表条目（含泛型实例）及其地址。</summary>
internal static class EntrySearch
{
    [Command("find-entries", "按名称片段列出注册表条目", Arguments = "<binary> <metadata> <名称片段> [上限]")]
    public static int Run(string binary, string metadata, string[] arguments)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var limit = arguments.Length > 1 ? int.Parse(arguments[1]) : 30;
        var shown = 0;
        foreach (var function in facts.Code.Functions)
            foreach (var entry in facts.EntriesAt(function.Start))
                if (entry.Method?.ToString().Contains(arguments[0], StringComparison.Ordinal) == true && shown++ < limit)
                    Console.WriteLine($"0x{function.Start:x}\t{function.Size}\t{entry.Kind}\t{entry.Method}");
        Console.WriteLine($"共 {shown}");
        return 0;
    }
}
