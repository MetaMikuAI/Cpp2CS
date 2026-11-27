using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Kernel.Facts;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;
using Cpp2CS.Spec.Runtime;
using Cpp2CS.Target;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>设计 16.2。签名与逃逸按入口去重，调用处的缺事实按原生位置去重。</summary>
internal static class PassingAudit
{
    private static readonly string[] Reasons = ["形参副本逃逸", "结果位置逃逸", "经内存传递的实参指向堆",
        "间接结果地址不在帧或结果位置", "调用的传递区间超出私有区域的大小",
        "两段经内存传递的区域有重叠", "经内存传递的实参有成员没有写全", "读取已交给被调方的副本"];

    public static int Run(string binary, string metadataPath, string? symbols, string? fingerprint)
    {
        var input = Il2CppInput.Load(binary, metadataPath);
        var file = File.ReadAllBytes(binary);
        var metadata = ModelInput.Facts(input, file);
        var native = new ModelNativeFacts(metadata, input.Code);
        var target = new Arm64Target(input.Elf, file, input.Code.Methods.Concat(input.Code.MethodInstances)
            .Where(m => m.Entry.HasValue).Select(m => m.Entry!.Value));
        var facts = new BridgeFacts(input, metadata, symbols, file, target, fingerprint);
        var indirect = new HashSet<ulong>();
        var signatures = new Dictionary<ulong, (bool Argument, bool Result, bool Unknown)>();
        foreach (ulong entry in target.Entries)
        {
            var shapes = native.Signatures(entry - input.Elf.ImageBase, out _);
            bool argument = false, result = false, incomplete = shapes.IsEmpty;
            foreach (var shape in shapes)
            {
                foreach (var type in shape.Parameters)
                {
                    var placement = Aggregate(type);
                    argument |= placement == AggregatePlacement.Reference;
                    incomplete |= placement == AggregatePlacement.Unknown;
                }
                var returned = Aggregate(shape.Return);
                result |= returned == AggregatePlacement.Reference;
                incomplete |= returned == AggregatePlacement.Unknown;
            }
            if (argument || result) indirect.Add(entry);
            if (argument || result || incomplete) signatures.Add(entry, (argument, result, incomplete));
        }

        // 除直接调用和尾跳外，寄存器目标经读取和沿边代入也可能取得名字。
        var frames = new HashSet<ulong>();
        foreach (var section in input.Elf.Sections.Where(s => (s.Flags & 4) != 0 && s.Type == 1))
            for (ulong pc = section.Address; pc + 4 <= section.Address + section.Size; pc += 4)
            {
                var op = target.InstructionAt(pc);
                bool dynamic = op.Form == Form.BranchRegister || op.IsCall && op.Form != Form.Call;
                if (!dynamic && (!(op.Form is Form.Call or Form.Branch || op.Conditional) || !indirect.Contains(op.Destination(pc)))) continue;
                if (target.Unwind.Find(pc) is { } frame) frames.Add(frame.Start);
            }

        int arguments = 0, returns = 0, unknown = 0, noSnapshot = 0, missingCaller = 0, graphs = 0, noGraph = 0;
        var failures = new Dictionary<string, int>();
        var sites = Reasons.ToDictionary(s => s, _ => new HashSet<ulong>());
        var hosts = Reasons.ToDictionary(s => s, _ => new HashSet<ulong>());
        var examples = new HashSet<string>();
        int processed = 0;
        foreach (ulong entry in signatures.Keys.Concat(target.Entries.Where(entry => !signatures.ContainsKey(entry))))
        {
            if (processed == signatures.Count)
                Console.WriteLine($"签名候选已核对：有快照且已证经内存传递的形参 {arguments}，经内存返回 {returns}，签名或放法不全 {unknown}");
            if (++processed % 50000 == 0) Console.Error.WriteLine($"已检查入口 {processed}/{target.Entries.Count}，可用实例效果图 {graphs}");
            bool candidate = signatures.TryGetValue(entry, out var signature);
            if (!candidate && !frames.Contains(target.Unwind.Find(entry)?.Start ?? entry)) continue;
            if (Lift(entry, out string failure) is not { } snapshot)
            {
                if (candidate)
                {
                    failures[failure] = failures.GetValueOrDefault(failure) + 1;
                    noSnapshot++;
                }
                else missingCaller++;
                continue;
            }
            if (signature.Argument) arguments++;
            if (signature.Result) returns++;
            if (signature.Unknown) unknown++;
            if (!indirect.Contains(entry) && !snapshot.Blocks.Any(b => b.Occurrences.OfType<CallOccurrence>()
                    .Any(c => c.Target is { } t && (!t.IsConstant || indirect.Contains((ulong)t.Value))))) continue;
            var callees = new Dictionary<ulong, MethodSnapshot?>();
            MethodSnapshot? Callee(ulong at) => callees.TryGetValue(at, out var body) ? body : callees[at] = Lift(at, out _);
            var shapes = native.Signatures(entry - input.Elf.ImageBase, out _);
            if (shapes.IsEmpty) noGraph++;
            foreach (var shape in shapes)
            {
                var graph = new EffectGraph(snapshot, shape, facts, Callee);
                if (graph.Failure != null) { noGraph++; continue; }
                graphs++;
                foreach (var effect in graph.Effects.Where(e => e.Kind == NativeEffectKind.Unnamed))
                {
                    foreach (string reason in Reasons)
                    {
                        if (!effect.Detail.Contains(reason, StringComparison.Ordinal)) continue;
                        hosts[reason].Add(entry);
                        sites[reason].Add(snapshot[effect.Occurrence].Address);
                    }
                    if ((effect.Detail.Contains("形参副本上的地址不是常量偏移") || effect.Detail.Contains("结果位置上的地址不是常量偏移") ||
                        effect.Detail.Contains("分别接收两次调用的返回值")) &&
                        examples.Add(effect.Detail.Split('：')[0]))
                    {
                        var method = metadata.Keys.DescribeMethod(shape.Entity)!;
                        var definition = metadata.Model.Methods[method.Definition];
                        Console.WriteLine($"未覆盖形态 {metadata.Model.Types[definition.Owner].Name}::{definition.Name} 入口 0x{entry:x} {effect.Occurrence} {effect.Detail}");
                        var block = snapshot.Blocks[effect.Occurrence.Block.Index];
                        for (int i = 0; i < block.Occurrences.Length; i++)
                        {
                            var id = new OccurrenceId(block.Id, i);
                            Console.WriteLine($"  {id} 0x{snapshot[id].Address:x} {snapshot[id].Kind} {string.Join(" ", snapshot.Operands(id).Select(graph.Resolve))}");
                        }
                    }
                }
            }
        }
        Console.WriteLine($"去重登记入口 {target.Entries.Count}，有快照且已证经内存传递的形参 {arguments}，经内存返回 {returns}");
        Console.WriteLine($"有快照但签名或放法不全 {unknown}，上述候选中无快照 {noSnapshot}");
        foreach (var (reason, count) in failures.OrderByDescending(p => p.Value)) Console.WriteLine($"  {reason} {count}");
        Console.WriteLine($"其余调用者无快照 {missingCaller}，可用实例效果图 {graphs}，签名或效果图不可用 {noGraph}");
        foreach (string reason in Reasons) Console.WriteLine($"{reason}：入口 {hosts[reason].Count}，位置 {sites[reason].Count}");
        int escaped = hosts["形参副本逃逸"].Union(hosts["结果位置逃逸"]).Count();
        int escapeSites = sites["形参副本逃逸"].Union(sites["结果位置逃逸"]).Count();
        Console.WriteLine($"R6 逃逸入口 {escaped}，位置 {escapeSites}");
        int outside = sites["经内存传递的实参指向堆"].Union(sites["间接结果地址不在帧或结果位置"]).Union(sites["调用的传递区间超出私有区域的大小"]).Count();
        Console.WriteLine($"C3 未落入规定私有区间的位置 {outside}");
        return 0;

        MethodSnapshot? Lift(ulong address, out string failure)
        {
            try
            {
                var lifted = target.Lift(address);
                failure = lifted.Reason ?? "未生成快照";
                return lifted.Snapshot;
            }
            catch (FlowException e) { failure = e.Message; return null; }
        }
    }

    private static AggregatePlacement? Aggregate(TypeShape? type) => type?.Kind == StackKind.Value
        ? AggregateConvention.Aapcs64.Classify(type.StorageBits, type.Members) : null;
}
