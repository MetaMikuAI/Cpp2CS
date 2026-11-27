using Cpp2CS.Discovery;
using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Engine;
using Cpp2CS.Kernel.Facts;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Model;
using Cpp2CS.Snapshot;
using Cpp2CS.Target;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>设计 16.2、18.3。先枚举映像的直接调用位置，再逐调用者实例核对实参；未能取定的单列。</summary>
internal static class RgctxAudit
{
    public static int Run(string binary, string metadataPath, string? symbols, string? detailsPath)
    {
        var input = Il2CppInput.Load(binary, metadataPath);
        var file = File.ReadAllBytes(binary);
        var metadata = ModelInput.Facts(input, file);
        var target = new Arm64Target(input.Elf, file, input.Code.Methods.Concat(input.Code.MethodInstances)
            .Where(c => c.Entry.HasValue).Select(c => c.Entry!.Value));
        var facts = new BridgeFacts(input, metadata, symbols, file, target, null);
        var entities = new EntityFacts(metadata);
        var hosts = new Dictionary<ulong, HashSet<EntityRef>>();
        var generic = new HashSet<ulong>();
        void Register(ulong rva, EntityRef method)
        {
            ulong entry = checked(input.Elf.ImageBase + rva);
            if (!hosts.TryGetValue(entry, out var group)) hosts[entry] = group = [];
            group.Add(method);
        }
        for (int i = 0; i < input.Code.Methods.Count; i++)
            if (input.Code.Methods[i].Entry is ulong rva) Register(rva, new(EntityKind.Method, i));
        for (int i = 0; i < input.Model.MethodInstances.Count; i++)
        {
            var entity = new EntityRef(EntityKind.Method, metadata.Keys.MethodKey(input.Model.MethodInstances[i])!.Value);
            if (input.Code.MethodInstances[i].Entry is ulong rva) Register(rva, entity);
            if (facts.GenericEntry(entity) is not { } registration) continue;
            Register(registration.Address, entity);
            generic.Add(checked(input.Elf.ImageBase + registration.Address));
        }

        var definitions = input.Model.GenericContexts.Values.SelectMany(rows => rows).ToLookup(r => r.Kind);
        Console.WriteLine($"上下文定义所属者 {input.Model.GenericContexts.Count}，表项 {definitions.Sum(g => g.Count())}");
        foreach (var kind in Enum.GetValues<RgctxDataType>())
            Console.WriteLine($"登记 {kind} {definitions[kind].Count()}");
        var sites = DirectCalls(input.Elf, target, generic);
        var callerFrames = sites.Keys.Select(at => target.Unwind.Find(at)?.Start).OfType<ulong>().ToHashSet();
        Console.WriteLine($"泛型入口 {generic.Count}，指向它们的直接调用位置 {sites.Count}，其中无 FDE {sites.Keys.Count(at => target.Unwind.Find(at) == null)}");
        using var details = detailsPath == null ? null : new StreamWriter(detailsPath);
        MethodSnapshot? Snapshot(ulong address)
        {
            try { return target.Lift(address).Snapshot; }
            catch (FlowException) { return null; }
        }
        var readers = new Dictionary<ulong, Slot>();
        var nonReaders = new Dictionary<ulong, Slot>();
        int noSnapshot = 0, noSlot = 0;
        foreach (ulong address in generic.Order())
        {
            var callee = facts.Callee(address);
            var slot = NativeEntryQueries.SharedMethodSlot(callee.SharedSignatures ??
                (callee.Signature is { } only ? [only] : []), out string reason);
            if (slot is null) noSlot++;
            else if (Snapshot(address) is not { } snapshot) noSnapshot++;
            else if (ParameterSummary.ReadsHidden(snapshot, slot.Value)) readers.Add(address, slot.Value);
            else nonReaders.Add(address, slot.Value);
            details?.WriteLine($"入口\t0x{address:x}\t{slot}\t{(readers.ContainsKey(address) ? "读" : nonReaders.ContainsKey(address) ? "不读" : "不可判定")}\t{callee.Name}\t{reason}");
        }
        int unreadSites = sites.Values.Count(nonReaders.ContainsKey);
        int readSites = sites.Values.Count(readers.ContainsKey);
        Console.WriteLine($"泛型入口：满足读前提 {readers.Count}，未满足 {generic.Count - readers.Count}（判定不读 {nonReaders.Count}，无快照 {noSnapshot}，无共同槽位 {noSlot}）");
        Console.WriteLine($"直接调用位置：目标读 {readSites}，不读 {unreadSites}，无快照或共同槽位 {sites.Count - readSites - unreadSites}");
        var reached = new HashSet<ulong>();
        var named = new HashSet<ulong>();
        var unnamed = new HashSet<ulong>();
        var indirectReads = new HashSet<ulong>();
        var readCounts = new Dictionary<(RgctxDataType? Kind, bool Named), int>();
        var guards = new GuardCounts();
        int checkedCalls = 0, unknown = 0, snapshots = 0, missingSnapshot = 0, missingShape = 0, graphs = 0;
        foreach (var (address, methods) in hosts.OrderBy(p => p.Key))
        {
            if (!callerFrames.Contains(target.Unwind.Find(address)?.Start ?? address) && !generic.Contains(address)) continue;
            if (Snapshot(address) is not { } snapshot) { missingSnapshot++; continue; }
            snapshots++;
            var callees = new Dictionary<ulong, MethodSnapshot?>();
            MethodSnapshot? CalleeSnapshot(ulong entry) => callees.TryGetValue(entry, out var result) ? result : callees[entry] = Snapshot(entry);
            foreach (var entity in methods.OrderBy(m => m.Key))
            {
                MethodShape host;
                try { host = metadata.Method(entity); }
                catch (ExpansionException) { missingShape++; continue; }
                var graph = new EffectGraph(snapshot, host, facts, CalleeSnapshot);
                if (graph.Failure != null) { missingShape++; continue; }
                bool genericHost = facts.GenericEntry(entity) != null;
                graphs++;
                foreach (int b in graph.Order)
                {
                    var block = new BlockId(b);
                    for (int i = 0; i < snapshot.OccurrenceCount(block); i++)
                    {
                        var id = new OccurrenceId(block, i);
                        if (genericHost && snapshot[id] is ReadOccurrence read)
                        {
                            CountRead(graph, id, read, metadata, facts, address, readCounts, details);
                            if (details != null && !indirectReads.Contains(address) && nonReaders.TryGetValue(address, out var hiddenSlot))
                            {
                                var resolved = graph.Resolve(read.Location);
                                var baseTerm = resolved is { Kind: TermKind.Operation, Op: Op.Add } && resolved.Operands[1].IsConstant
                                    ? resolved.Operands[0] : resolved;
                                if (baseTerm.Kind == TermKind.EntryParameter && baseTerm.Slot == hiddenSlot)
                                {
                                    details.WriteLine($"间接读\t0x{address:x}\t0x{read.Address:x}\t{facts.Symbol(address)}\t{read.Location}\t{resolved}");
                                    indirectReads.Add(address);
                                }
                            }
                        }
                        if (snapshot[id] is CallOccurrence call && call.Target is { IsConstant: true } &&
                            sites.TryGetValue(call.Address, out ulong to))
                        {
                            reached.Add(call.Address);
                            if (readers.TryGetValue(to, out var slot))
                            {
                                int arg = call.ArgumentSlots.IndexOf(slot);
                                if (arg < 0 || graph.Resolve(call.Arguments[arg]) is not { Kind: TermKind.Entity } value)
                                {
                                    unknown++;
                                    unnamed.Add(call.Address);
                                }
                                else
                                {
                                    checkedCalls++;
                                    details?.WriteLine($"调用\t0x{address:x}\t{entity.Key}\t0x{call.Address:x}\t0x{to:x}\t{slot}\t{value.Entity}");
                                    if (!hosts[to].Contains(value.Entity))
                                    {
                                        Console.WriteLine($"反例：调用者 {entity} 0x{address:x}，调用 0x{call.Address:x}，目标 0x{to:x}，{slot} 为 {value.Entity}，入口登记 [{string.Join("、", hosts[to].OrderBy(m => m.Key))}]");
                                        named.Remove(call.Address);
                                        unnamed.ExceptWith(named);
                                        unnamed.Remove(call.Address);
                                        Console.WriteLine($"停止时：被调入口未满足读前提 {sites.Count - readSites}（其中判定不读 {unreadSites}），读且相符 {named.Count}，读且未命名 {unnamed.Count}，读且不符 1，其余读入口位置尚未核对 {readSites - named.Count - unnamed.Count - 1}");
                                        return 1;
                                    }
                                    named.Add(call.Address);
                                }
                            }
                        }
                        if (graph.Effect(id) is { Ends: true }) break;
                    }
                }
                if (genericHost) guards.Check(graph, entities, facts, details);
            }
        }
        Console.WriteLine($"可用快照 {snapshots}，无快照入口 {missingSnapshot}，可用实例效果图 {graphs}，无签名或调用约定 {missingShape}");
        Console.WriteLine($"直接调用位置 {sites.Count}，进入效果图 {reached.Count}，未进入 {sites.Count - reached.Count}，隐含实参已命名的位置 {named.Count}");
        Console.WriteLine($"按调用者实例核对：已命名 {checkedCalls}，不符 0，未命名或无槽位 {unknown}");
        Console.WriteLine($"被调入口未满足读前提 {sites.Count - readSites}（其中判定不读 {unreadSites}），读且相符 {named.Count}，读且未命名 {readSites - named.Count}，读且不符 0");
        Console.WriteLine($"读入口位置中：兼有已命名与未命名实例 {unnamed.Count(named.Contains)}，未进入效果图 {sites.Count(p => readers.ContainsKey(p.Value) && !reached.Contains(p.Key))}");
        foreach (var (key, count) in readCounts.OrderBy(p => p.Key.Kind).ThenBy(p => p.Key.Named))
            Console.WriteLine($"表项读取 {key.Kind?.ToString() ?? "越界或无表"} {(key.Named ? "已命名" : "未命名")} {count}");
        guards.Report();
        return 0;
    }

    private static Dictionary<ulong, ulong> DirectCalls(Elf64 elf, Arm64Target target, HashSet<ulong> generic)
    {
        var sites = new Dictionary<ulong, ulong>();
        foreach (var text in elf.Sections.Where(s => (s.Flags & 4) != 0 && s.Type == 1))
            for (ulong pc = text.Address; pc + 4 <= text.Address + text.Size; pc += 4)
            {
                var op = target.InstructionAt(pc);
                if (op.Form is not (Form.Call or Form.Branch) && !op.Conditional) continue;
                ulong to = op.Destination(pc);
                if (!generic.Contains(to)) continue;
                if (op.Form != Form.Call && target.Unwind.Find(pc) is { } frame && to >= frame.Start && to < frame.End) continue;
                sites.Add(pc, to);
            }
        return sites;
    }

    private static void CountRead(EffectGraph graph, OccurrenceId id, ReadOccurrence read, ModelMetadata metadata,
        BridgeFacts facts, ulong entry, Dictionary<(RgctxDataType?, bool), int> counts, StreamWriter? details)
    {
        if (read.Width != facts.Layout.PointerBits) return;
        var root = graph.Resolve(read.Location);
        UInt128 offset = 0;
        if (root is { Kind: TermKind.Operation, Op: Op.Add } && root.Operands[1].IsConstant)
        {
            offset = root.Operands[1].Value;
            root = root.Operands[0];
        }
        uint stride = (uint)(read.Width / 8);
        if (root is not { Kind: TermKind.Attribute, Attribute.Value: KernelAttributes.RgctxTable } ||
            offset % stride != 0 || offset / stride > int.MaxValue) return;
        int index = (int)(offset / stride);
        var entity = root.Operands[0].Entity;
        RgctxOwner? owner = metadata.Keys.DescribeMethod(entity) is { } method ? new(true, method.Definition) :
            metadata.Keys.DescribeType(entity) is NamedType type ? new(false, type.Definition) : null;
        RgctxDataType? kind = owner.HasValue && metadata.Model.GenericContexts.TryGetValue(owner.Value, out var rows) &&
            (uint)index < rows.Length ? rows[index].Kind : null;
        var result = graph.Resolve(graph.Snapshot.Results(id)[0]);
        bool named = result.Kind == TermKind.Entity;
        counts[(kind, named)] = counts.GetValueOrDefault((kind, named)) + 1;
        if (details != null)
        {
            string? name = null;
            if (named && metadata.Keys.DescribeMethod(result.Entity) is { } spec)
            {
                var definition = metadata.Model.Methods[spec.Definition];
                name = $"{metadata.Model.Types[definition.Owner].Name}::{definition.Name}";
            }
            else if (named && metadata.Keys.DescribeType(result.Entity) is NamedType namedType)
                name = metadata.Model.Types[namedType.Definition].Name;
            string? image = null;
            uint? token = null;
            if (owner is { } key)
            {
                int typeIndex = key.IsMethod ? metadata.Model.Methods[key.Definition].Owner : key.Definition;
                image = metadata.Model.Images.Single(m => typeIndex >= m.FirstType && typeIndex < m.FirstType + m.TypeCount).Name;
                token = key.IsMethod ? metadata.Model.Methods[key.Definition].Token : metadata.Model.Types[typeIndex].Token;
            }
            details.WriteLine($"读取\t0x{entry:x}\t{graph.Host.Entity.Key}\t0x{read.Address:x}\t{entity}\t{index}\t{kind}\t{(named ? result.Entity.ToString() : "未命名")}\t{name}\t{image}\t{token:x8}");
        }
    }

    private sealed class GuardCounts
    {
        private readonly int[] branches = new int[2], proposed = new int[2], tried = new int[2], proved = new int[2];

        internal void Check(EffectGraph graph, EntityFacts entities, BridgeFacts facts, StreamWriter? details)
        {
            var snapshot = graph.Snapshot;
            foreach (int b in graph.Order)
            {
                var block = new BlockId(b);
                if (graph.Condition(block) is not { } condition || snapshot.Terminator(block).Kind != TerminatorKind.Branch) continue;
                bool Has(Term t, Func<Term, bool> test) => test(t) || t.Operands.Any(v => Has(v, test));
                int kind = Has(condition, t => t is { Kind: TermKind.Attribute, Attribute.Value: KernelAttributes.RgctxTable } &&
                    t.Operands[0].Entity.Kind == EntityKind.Method) ? 1 :
                    Has(condition, t => graph.RuntimeStateAddress(t) is { Op: Op.Add } a &&
                        a.Operands[0] is { Kind: TermKind.Entity, Entity.Kind: EntityKind.Type } && a.Operands[1].IsConstant &&
                        a.Operands[1].Value == (uint)facts.Layout.ClassInitializedFlagsOffset) ? 0 : -1;
                if (kind < 0) continue;
                string operation = kind == 0 ? "class.initialize-metadata" : "method.initialize-rgctx";
                if (!snapshot.Terminator(block).Exits.Any(e => e.Kind == ExitKind.Target &&
                    snapshot.Blocks[e.Target.Index].Occurrences.OfType<CallOccurrence>().Any(c => c.Target is { IsConstant: true } to &&
                        facts.Callee((ulong)to.Value).Operation?.Id == operation))) continue;
                branches[kind]++;
                var view = new FactView(graph, entities, facts.Layout);
                var claim = new GuardDiscoverer().Propose(view).FirstOrDefault(c => c.Operation == "nop" &&
                    c.Occupied.Contains(EffectRef.Of(new EdgeId(block, 0))));
                if (claim == null) continue;
                proposed[kind]++;
                if (proved[kind] != 0 || tried[kind] >= 32) continue;
                tried[kind]++;
                var result = Proof.Prove(new(snapshot, graph.Host, graph.Host.IsTypeInitializer ? graph.Host.DeclaringType : null,
                    facts, entities, _ => null), claim);
                if (result.Certificate != null) proved[kind]++;
                details?.WriteLine($"守卫\t{operation}\t{graph.Host.Entity.Key}\t{block}\t{(result.Certificate != null ? "取得凭据" : result.Refutation!.Detail)}");
            }
        }

        internal void Report()
        {
            for (int i = 0; i < 2; i++)
                Console.WriteLine($"{(i == 0 ? "类" : "方法")}守卫 {branches[i]}，提出空操作 {proposed[i]}，核对声明 {tried[i]}，取得凭据 {proved[i]}");
        }
    }
}
