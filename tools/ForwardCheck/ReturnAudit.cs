using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Kernel.Engine;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Runtime;
using Cpp2CS.Target;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>
/// “排在函数范围末尾的调用不返回”（设计 7.5、16.2）的全映像核对：对每个托管入口的快照里以“不返回”的出口结束的块，
/// 看块内最后一次调用的目标——登记为不返回的运行时函数，或快照里没有返回出口的托管方法，就是另一种依据印证了它；
/// 其余的逐类列出。没有符号时运行时函数没有名字，只能核对目标是托管方法的那些。
/// </summary>
internal static class ReturnAudit
{
    public static int Run(string binary, string metadataPath, string? symbols)
    {
        var input = Il2CppInput.Load(binary, metadataPath);
        var file = File.ReadAllBytes(binary);
        var metadata = ModelInput.Facts(input, file);
        var facts = new BridgeFacts(input, metadata, symbols, file);
        var target = new Arm64Target(input.Elf, file,
            input.Code.Methods.Concat(input.Code.MethodInstances).Where(m => m.Entry.HasValue).Select(m => m.Entry!.Value));
        var lifts = new Dictionary<ulong, MethodSnapshot?>();
        MethodSnapshot? Snapshot(ulong entry)
        {
            if (lifts.TryGetValue(entry, out var known)) return known;
            try
            {
                return lifts[entry] = target.Lift(entry).Snapshot;
            }
            catch (FlowException)
            {
                return lifts[entry] = null;
            }
        }
        static bool Returns(MethodSnapshot snapshot) => snapshot.Blocks.Any(b => b.Terminator.Exits.Any(e => e.Kind == ExitKind.Return));

        int methods = 0, ends = 0, registered = 0, managed = 0, traps = 0;
        var other = new SortedDictionary<string, (int Count, string First)>(StringComparer.Ordinal);
        void Other(string kind, ulong entry, ulong at)
        {
            var known = other.GetValueOrDefault(kind);
            other[kind] = (known.Count + 1, known.First ?? $"入口 0x{entry:x}，调用在 0x{at:x}");
        }
        foreach (ulong entry in target.Entries)
        {
            if (Snapshot(entry) is not { } snapshot) continue;
            methods++;
            foreach (var block in snapshot.Blocks)
            {
                if (block.Terminator is { Kind: TerminatorKind.Single } single && single.Exits[0].Kind == ExitKind.Trap) traps++;
                if (block.Terminator is not { Kind: TerminatorKind.Single } terminator || terminator.Exits[0].Kind != ExitKind.NoReturn) continue;
                ends++;
                var id = new OccurrenceId(block.Id, block.Occurrences.Length - 1);
                var call = (CallOccurrence)snapshot[id];
                var operand = snapshot.Operands(id)[0];
                if (call.Target is null || !operand.IsConstant) { Other("目标不是常量地址", entry, call.Address); continue; }
                ulong address = (ulong)operand.Value;
                var callee = facts.Callee(address);
                switch (callee.Kind)
                {
                    case CalleeKind.Runtime when callee.Operation!.Effect is RuntimeEffect.Throw or RuntimeEffect.ThrowArgument:
                        registered++;
                        break;
                    case CalleeKind.Runtime:
                        Other($"登记为会返回的运行时操作 {callee.Operation!.Id}", entry, call.Address);
                        break;
                    case CalleeKind.Managed when Snapshot(address) is { } body:
                        if (Returns(body)) Other("托管方法，快照里有返回出口", entry, call.Address);
                        else managed++;
                        break;
                    case CalleeKind.Managed:
                        Other("托管方法，没有快照", entry, call.Address);
                        break;
                    default:
                        Other(symbols is null ? "没有命名" : $"没有登记：{callee.Name}", entry, call.Address);
                        break;
                }
            }
        }
        Console.WriteLine($"有快照的托管入口 {methods} 个；以“不返回”的出口结束的块 {ends} 个；以陷阱结束的块 {traps} 个");
        Console.WriteLine($"  目标登记为不返回的运行时函数 {registered}");
        Console.WriteLine($"  目标是快照里没有返回出口的托管方法 {managed}");
        foreach (var (kind, (count, first)) in other) Console.WriteLine($"  {kind} {count}　首例 {first}");
        return other.Keys.Any(k => k.StartsWith("托管方法，快照里有返回出口", StringComparison.Ordinal) || k.StartsWith("登记为会返回", StringComparison.Ordinal)) ? 1 : 0;
    }
}
