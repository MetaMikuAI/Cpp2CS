using System.Buffers.Binary;
using System.Collections.Immutable;
using Cpp2CS.Input;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Target;

/// <summary>核对工具请求的指令位置；不参与快照构造与摘要。</summary>
public sealed class LiftLocations(bool collectBlocks = true)
{
    internal bool CollectBlocks => collectBlocks;
    public ulong? UnresolvedBranch { get; internal set; }
    public string? BranchReason { get; internal set; }
    internal Dictionary<ulong, JumpTableInfo> Tables { get; } = [];
    public IReadOnlyDictionary<ulong, JumpTableInfo> Switches => Tables;
    internal Dictionary<ulong, ulong[]> TracedTargets { get; } = [];
    public IReadOnlyDictionary<ulong, ulong[]> SwitchTargets => TracedTargets;
    public Dictionary<BlockId, (ulong Start, int Instructions)> Blocks { get; } = [];
}

public sealed record LiftResult(MethodSnapshot? Snapshot, string? Reason);

/// <summary>按 FDE 划界，从登记的入口追踪可达指令，按调用点表接展开边。</summary>
public sealed class Arm64Target
{
    readonly Elf64 elf;
    readonly byte[] file;
    readonly HashSet<ulong> relocated;
    public UnwindIndex Unwind { get; }
    public IReadOnlyList<ulong> Entries { get; }

    public Arm64Target(Elf64 elf, byte[] file, IEnumerable<ulong> entryRvas)
    {
        this.elf = elf;
        if (elf.Machine != 183) throw new InvalidDataException("需要 AArch64 ELF");
        this.file = file;
        Unwind = new(elf, file);
        Entries = entryRvas.Select(rva => checked(elf.ImageBase + rva)).Distinct().Order().ToArray();
        relocated = elf.Relocations.Select(r => r.Address).ToHashSet();
    }

    [ThreadStatic] static (uint Word, Instruction Value, bool Valid)[]? decodeCache;

    internal Instruction Cached(uint word)
    {
        decodeCache ??= new (uint, Instruction, bool)[65536];
        ref var cell = ref decodeCache[(word * 2654435761u) >> 16];
        if (!cell.Valid || cell.Word != word) cell = (word, Decoder.Decode(word), true);
        return cell.Value;
    }

    /// <summary>逐指令核对使用同一提升语义。输入与输出依 Abi 的寄存器顺序排列，读写出现追加到给定块。</summary>
    public Term[] EvaluateInstruction(ulong pc, SnapshotBuilder builder, BlockId block, Term[] inputs)
    {
        if (inputs.Length != Abi.Count) throw new ArgumentException("寄存器行长度不符", nameof(inputs));
        var machine = new Machine(builder, block, (Term[])inputs.Clone());
        machine.Apply(Cached(Word(pc)), pc);
        return machine.Row;
    }

    public Instruction InstructionAt(ulong pc) => Cached(Word(pc));

    public uint Word(ulong pc) => BinaryPrimitives.ReadUInt32LittleEndian(file.AsSpan(elf.FileOffset(pc, 4) ??
        throw new InvalidDataException("指令地址没有文件内容")));
    public LiftResult Lift(ulong entry, LiftLocations? locations = null)
    {
        if (Unwind.Find(entry) is not Frame f) return new(null, "缺少 FDE");
        if ((entry & 3) != 0 || ((f.End - f.Start) & 3) != 0 || elf.FileOffset(f.Start, f.End - f.Start) == null)
            return new(null, "FDE 代码范围无效");
        return Lift(entry, f, locations, []);
    }

    LiftResult Lift(ulong entry, Frame f, LiftLocations? locations, Dictionary<ulong, string> unconfirmed)
    {
        if (locations != null) { locations.UnresolvedBranch = null; locations.BranchReason = null; }
        var sites = Unwind.Sites(f);
        var targets = new HashSet<ulong>();
        var tails = new Dictionary<ulong, ulong>();
        var instructions = new Dictionary<ulong, Instruction>();
        var tables = new Dictionary<ulong, JumpTableInfo>();
        var pads = new Dictionary<ulong, ulong>();
        var pending = new Stack<ulong>();
        pending.Push(entry);
        bool Inside(ulong pc) => pc >= f.Start && pc < f.End && (pc & 3) == 0;
        void Edge(ulong pc) { targets.Add(pc); pending.Push(pc); }
        while (pending.TryPop(out ulong pc))
        {
            while (Inside(pc) && !instructions.ContainsKey(pc))
            {
                var i = Cached(Word(pc));
                if (i.Form == Form.Unknown) return new(null, "不支持指令");
                instructions.Add(pc, i);
                if (i.Form == Form.BranchRegister)
                {
                    // 相对表分派的目标最后由 64 位 ADD 生成。普通间接尾跳无需建前驱图。
                    string reason = unconfirmed.GetValueOrDefault(pc, "目标无相对表项加法");
                    JumpTableInfo? table = null;
                    for (ulong back = pc; back >= f.Start + 4 && instructions.TryGetValue(back - 4, out var writer); back -= 4)
                    {
                        if (writer.IsCall || writer.Conditional || writer.Form is Form.Branch or Form.BranchRegister or Form.Return or Form.Trap) break;
                        if ((writer.WrittenGeneralRegisters & (1u << i.N)) == 0) continue;
                        if (!unconfirmed.ContainsKey(pc) && writer is { Name: "add", Width: 64, Shift: 2 })
                            table = new JumpTables(entry, instructions, pads, tables).Resolve(pc, f, elf, file, relocated, out reason);
                        break;
                    }
                    if (table == null)
                    {
                        if (locations != null && locations.UnresolvedBranch == null) { locations.UnresolvedBranch = pc; locations.BranchReason = reason; }
                        break;
                    }
                    tables.Add(pc, table);
                    foreach (var arm in table.Arms.Distinct()) Edge(arm);
                    break;
                }
                if (i.Form is Form.Return or Form.Trap) break;
                if (i.Form == Form.Branch || i.Conditional)
                {
                    ulong dest = i.Destination(pc);
                    if (Inside(dest)) Edge(dest);
                    else tails[pc] = dest;
                    if (!i.Conditional) break;
                    if (!Inside(pc + 4)) return new(null, "落空边越出 FDE");
                    Edge(pc + 4); break;
                }
                if (i.IsCall)
                {
                    var site = Array.Find(sites, s => s.Start <= pc && pc < s.End);
                    if (site.Landing != 0)
                    {
                        if (!Inside(site.Landing) || !Inside(pc + 4)) return new(null, "展开边越出 FDE");
                        pads.Add(pc, site.Landing); Edge(site.Landing); Edge(pc + 4); break;
                    }
                    if (pc + 4 == f.End) break;
                }
                if (pc + 4 == f.End) return new(null, "落空边越出 FDE");
                pc += 4;
            }
        }
        // 所有表项和异常入边已闭合。在完整图上重做证明，避免后来发现的入边绕过检查或改写基址。
        if (tables.Count != 0)
        {
            var complete = new JumpTables(entry, instructions, pads, tables);
            bool retry = false;
            foreach (var (pc, t) in tables)
            {
                var proof = complete.Resolve(pc, f, elf, file, relocated, out string reason);
                if (proof == null || proof.Load != t.Load || proof.Address != t.Address || proof.Basis != t.Basis ||
                    !proof.Arms.AsSpan().SequenceEqual(t.Arms))
                {
                    retry |= unconfirmed.TryAdd(pc, proof == null ? reason : "补全入边后表定义不唯一");
                }
            }
            // 失去证明的表按间接调用终结，重新追踪以剔除仅由其表项可达的块。
            if (retry) return Lift(entry, f, locations, unconfirmed);
            if (locations != null)
                foreach (var (pc, t) in tables)
                {
                    locations.Tables.Add(pc, t);
                    locations.TracedTargets.Add(pc, t.Arms);
                }
        }

        var heads = targets.Append(entry).ToHashSet();
        // 选择子取自读表前的索引。之后即使机器指令复用了该寄存器，块内的项仍然有效。
        var loads = tables.Values.ToDictionary(t => t.Load);
        heads.UnionWith(loads.Keys);
        var dispatch = new HashSet<ulong>();
        foreach (var (jump, t) in tables)
            for (ulong p = t.Load + 4; p <= jump; p += 4) dispatch.Add(p);
        // 用实参行分段传递长直线上的值，限制规范化一次切片所需展开的表达式深度。
        if (instructions.Count > 16)
        {
            int count = 0;
            foreach (var pc in instructions.Keys.Order())
            {
                if (heads.Contains(pc)) count = 0;
                if (count >= 16 && !dispatch.Contains(pc)) { heads.Add(pc); count = 0; }
                count++;
            }
        }
        var live = LiveRows.Compute(heads, instructions, pads, tables, f.End);
        var builder = new SnapshotBuilder(64, target: "arm64");
        builder.SetReturnSlots(Abi.Slots(Abi.Return));
        int[] widths = Enumerable.Range(0, Abi.Count).Select(Abi.Width).ToArray();
        var ids = new Dictionary<ulong, BlockId>();
        var work = new Queue<ulong>();
        BlockId Block(ulong pc)
        {
            if (ids.TryGetValue(pc, out var existing)) return existing;
            var id = pc == entry && !targets.Contains(entry) ? builder.Entry : builder.Block(live[pc].Select(Abi.Width).ToArray());
            ids.Add(pc, id);
            work.Enqueue(pc);
            return id;
        }
        var initial = new Term[Abi.Count];
        for (int r = 0; r < initial.Length; r++)
        {
            if (Abi.Entry(r) is not Slot slot) initial[r] = builder.Terms.Undefined(widths[r]);
            else if (r is >= 40 and < 48) initial[r] = builder.Terms.Concat(builder.EntryParameter(slot, 64), builder.Terms.Undefined(64));
            else initial[r] = builder.EntryParameter(slot, widths[r]);
        }
        Term[] Out(ulong dest, Term[] row) => live[dest].Select(r => row[r]).ToArray();
        var empty = widths.Select(builder.Terms.Undefined).ToArray();
        var first = Block(entry);
        if (first != builder.Entry) builder.Jump(builder.Entry, first, Out(entry, initial));

        while (work.TryDequeue(out ulong start))
        {
            var b = ids[start];
            var row = b == builder.Entry ? initial : (Term[])empty.Clone();
            if (b != builder.Entry)
            {
                var layout = live[start];
                for (int j = 0; j < layout.Length; j++) row[layout[j]] = builder.Parameter(b, j);
            }
            var state = new Machine(builder, b, row);
            Exit To(ulong dest) => Exit.To(Block(dest), Out(dest, state.Row));
            Term? selector = null;
            int instructionCount = 0;
            for (ulong pc = start; ; pc += 4)
            {
                instructionCount++;
                var i = instructions[pc];
                if (loads.TryGetValue(pc, out var loaded)) selector = state.G(loaded.Index, 32);
                if (i.Form == Form.Return) { builder.Return(b, state.ReturnValues(state.G(i.N))); break; }
                if (i.Form == Form.Trap) { builder.Terminate(b, Terminator.Single(Exit.Trap, pc)); break; }
                if (i.Form == Form.BranchRegister)
                {
                    if (!tables.TryGetValue(pc, out var t))
                    {
                        state.TailCall(state.G(i.N), pc);
                        break;
                    }
                    // 末项兼作默认出口；支配此处的有界比较排除了所有越界值。
                    var arms = t.Arms.Select(To).ToImmutableArray();
                    builder.Terminate(b, Terminator.Switch(selector ?? throw new InvalidOperationException("读表与跳转不在同一块"), arms, pc)); break;
                }
                if (i.Conditional)
                {
                    Exit taken;
                    if (tails.TryGetValue(pc, out ulong target))
                    {
                        var regs = Abi.TailInputs;
                        var tail = builder.Block(regs.Select(Abi.Width).ToArray());
                        var input = (Term[])empty.Clone();
                        for (int j = 0; j < regs.Length; j++) input[regs[j]] = builder.Parameter(tail, j);
                        new Machine(builder, tail, input).TailCall(builder.Terms.Bits(target, 64), pc);
                        if (locations?.CollectBlocks == true) locations.Blocks.Add(tail, (pc, 0));
                        taken = Exit.To(tail, regs.Select(r => state.Row[r]).ToArray());
                    }
                    else taken = To(i.Destination(pc));
                    builder.Terminate(b, Terminator.Branch(state.Predicate(i), taken, To(pc + 4), pc)); break;
                }
                if (i.Form == Form.Branch)
                {
                    if (tails.TryGetValue(pc, out ulong target)) state.TailCall(builder.Terms.Bits(target, 64), pc);
                    else builder.Terminate(b, Terminator.Single(To(i.Destination(pc)), pc));
                    break;
                }
                if (i.IsCall)
                {
                    var target = i.Form == Form.Call ? builder.Terms.Bits(i.Destination(pc), 64) : state.G(i.N);
                    bool invoke = pads.TryGetValue(pc, out ulong pad);
                    var unwind = state.Call(target, pc, invoke);
                    if (invoke) { builder.Terminate(b, Terminator.Invoke(To(pc + 4), Exit.To(Block(pad), Out(pad, unwind)), pc)); break; }
                    if (pc + 4 == f.End) { builder.Terminate(b, Terminator.Single(Exit.NoReturn, pc)); break; }
                }
                else state.Apply(i, pc);
                if (heads.Contains(pc + 4)) { builder.Terminate(b, Terminator.Single(To(pc + 4), pc)); break; }
            }
            if (locations?.CollectBlocks == true) locations.Blocks.Add(b, (start, instructionCount));
            if (state.PlatformRegister) return new(null, "读取平台寄存器 x18");
        }
        return new(builder.Build(), null);
    }
}
