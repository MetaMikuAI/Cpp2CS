using System.Buffers.Binary;
using System.Collections.Immutable;
using Cpp2CS.Input;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Target;

public sealed record LiftResult(MethodSnapshot? Snapshot, string? Reason);

/// <summary>按 FDE 划界，从登记的入口追踪可达指令，按调用点表接展开边。</summary>
public sealed class Arm64Target
{
    readonly Elf64 elf;
    readonly byte[] file;
    readonly HashSet<ulong> entries;
    readonly HashSet<ulong> relocated;
    readonly HashSet<ulong> linkageEntries = [];
    public UnwindIndex Unwind { get; }
    public IReadOnlyList<ulong> Entries { get; }

    public Arm64Target(Elf64 elf, byte[] file, IEnumerable<ulong> entryRvas)
    {
        this.elf = elf;
        if (elf.Machine != 183) throw new InvalidDataException("需要 AArch64 ELF");
        this.file = file;
        Unwind = new(elf, file);
        entries = entryRvas.Select(rva => checked(elf.ImageBase + rva)).ToHashSet();
        Entries = entries.Order().ToArray();
        relocated = elf.Relocations.Select(r => r.Address).ToHashSet();
        var jumpSlots = elf.Relocations.Where(r => r.Type == 1026).Select(r => r.Address).ToHashSet();
        foreach (var plt in elf.Sections.Where(s => s.Name == ".plt" && (s.Flags & 4) != 0))
        {
            // AAELF64 的短 PLT 项以 x16 建立 GOT 槽地址，取槽中 x17 并跳转。
            for (ulong offset = 0; offset + 16 <= plt.Size; offset += 16)
            {
                ulong pc = plt.Address + offset;
                var page = Cached(Word(pc));
                var load = Cached(Word(pc + 4));
                var add = Cached(Word(pc + 8));
                var branch = Cached(Word(pc + 12));
                if (page is not { Form: Form.Address, Name: "adrp", D: 16 } ||
                    load is not { Form: Form.Memory, Name: "ldr", Vector: false, Width: 64, D: 17, N: 16, Mode: 0 } ||
                    add is not { Form: Form.Immediate, Name: "add", Width: 64, D: 16, N: 16 } ||
                    branch is not { Form: Form.BranchRegister, N: 17 } || load.Imm != (add.Imm << add.Shift)) continue;
                if (jumpSlots.Contains(page.Destination(pc & ~4095ul) + (ulong)load.Imm)) linkageEntries.Add(pc);
            }
        }
    }

    [ThreadStatic] static (uint Word, Instruction Value, bool Valid)[]? decodeCache;

    internal Instruction Cached(uint word)
    {
        decodeCache ??= new (uint, Instruction, bool)[65536];
        ref var cell = ref decodeCache[(word * 2654435761u) >> 16];
        if (!cell.Valid || cell.Word != word) cell = (word, Decoder.Decode(word), true);
        return cell.Value;
    }

    public uint Word(ulong pc) => BinaryPrimitives.ReadUInt32LittleEndian(file.AsSpan(elf.FileOffset(pc, 4) ??
        throw new InvalidDataException("指令地址没有文件内容")));
    bool Tail(ulong pc) => entries.Contains(pc) || Unwind.Find(pc)?.Start == pc || linkageEntries.Contains(pc);

    sealed record Table(int Index, ulong[] Arms, ulong Guard, ulong First);
    // CMP Wn,#last; B.HI default; ADRP+ADD; ADR; LDRB/H; ADD Xd,Xbase,Woff,SXTW #2; BR Xd。
    // 表项无符号；guard 的落空边必须是分派序列唯一的外部入口。
    Table? JumpTable(ulong pc, Frame frame)
    {
        if (pc < frame.Start + 28) return null;
        Instruction I(int back) => Decoder.Decode(Word(pc - (uint)(back * 4)));
        var guard = I(6); var cmp = I(7); var page = I(5); var add = I(4); var anchor = I(3);
        var load = I(2); var sum = I(1); var br = I(0);
        if (cmp.Form != Form.Immediate || cmp.Name != "subs" || cmp.D != 31 || cmp.Width != 32 || cmp.Shift != 0 ||
            guard.Form != Form.Condition || guard.Mode != 8 || guard.Destination(pc - 24) is var dest && dest >= pc - 20 && dest <= pc ||
            page.Form != Form.Address || page.Name != "adrp" || add.Form != Form.Immediate || add.Name != "add" ||
            add.Width != 64 || page.D != add.N || anchor.Form != Form.Address || anchor.Name != "adr" ||
            load.Form != Form.Memory || load.Name is not ("ldrb" or "ldrh") || load.Mode is not (6 or 7) || load.Shift != (load.Size == 8 ? 0 : 1) ||
            load.N != add.D || load.M != cmp.N || sum.Form is not (Form.Extended or Form.Shifted) || sum.Name != "add" || sum.Width != 64 ||
            sum.N != anchor.D || sum.M != load.D || sum.Mode != (sum.Form == Form.Extended ? 6 : 0) || sum.Shift != 2 || br.N != sum.D) return null;
        if (new[] { cmp.N, page.D, add.D, anchor.D, load.D, sum.D }.Any(r => r == 31) ||
            cmp.N == page.D || cmp.N == add.D || cmp.N == anchor.D || cmp.N == load.D || cmp.N == sum.D || anchor.D == add.D || anchor.D == load.D) return null;
        ulong proofStart = pc - 28;
        if (load.Mode == 7)
        {
            // 比较 Wn 只约束低半。使用 Xn 索引时，还要证明上一条指令整写了 Wn。
            if (proofStart < frame.Start + 4) return null;
            var producer = I(8);
            if (producer.Form is not (Form.Immediate or Form.Shifted or Form.Logical or Form.Wide or Form.Bitfield)
                || producer.Width != 32 || producer.D != cmp.N) return null;
            proofStart -= 4;
        }
        ulong table = page.Destination((pc - 20) & ~4095ul) + (ulong)(add.Imm << add.Shift);
        ulong basis = anchor.Destination(pc - 12);
        int count = checked((int)cmp.Imm + 1), bytes = load.Size / 8;
        ulong length = (uint)(count * bytes);
        if (elf.FileOffset(table, length) is not int start || !elf.Segments.Any(s => s.Type == 1 && (s.Flags & 2) == 0 &&
            table >= s.Address && table - s.Address < s.FileSize && length <= s.FileSize - (table - s.Address))) return null;
        var arms = new ulong[count];
        for (int j = 0; j < count; j++)
        {
            int index = start + j * bytes;
            ulong target = basis + 4ul * (bytes == 1 ? file[index] : BinaryPrimitives.ReadUInt16LittleEndian(file.AsSpan(index)));
            if (target < frame.Start || target >= frame.End || (target & 3) != 0 || (target >= pc - 24 && target <= pc)) return null;
            arms[j] = target;
        }
        for (ulong j = table > 7 ? table - 7 : 0; j < table + length; j++) if (relocated.Contains(j)) return null;
        return new(cmp.N, arms, proofStart, pc - 20);
    }

    static readonly ulong arguments = Abi.Arguments.Aggregate(0ul, (mask, r) => mask | (1ul << r));
    static readonly ulong results = Abi.Results.Append(31).Aggregate(0ul, (mask, r) => mask | (1ul << r));
    public LiftResult Lift(ulong entry)
    {
        if (Unwind.Find(entry) is not Frame f) return new(null, "缺少 FDE");
        if ((entry & 3) != 0 || ((f.End - f.Start) & 3) != 0 || elf.FileOffset(f.Start, f.End - f.Start) == null)
            return new(null, "FDE 代码范围无效");
        var sites = Unwind.Sites(f);
        var targets = new HashSet<ulong>();
        var tails = new HashSet<ulong>();
        var instructions = new Dictionary<ulong, Instruction>();
        var tables = new Dictionary<ulong, Table>();
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
                if (i is { Form: Form.Extended, Name: "sub", D: 31, N: 31 })
                    return new(null, "动态栈分配缺少当前栈基址");
                instructions.Add(pc, i);
                if (i.Form == Form.BranchRegister)
                {
                    if (JumpTable(pc, f) is not { } table) return new(null, "间接跳转目标未证实");
                    tables.Add(pc, table);
                    foreach (var arm in table.Arms.Distinct()) Edge(arm);
                    break;
                }
                if (i.Form is Form.Return or Form.Trap) break;
                if (i.Form == Form.Branch || i.Conditional)
                {
                    ulong dest = i.Destination(pc);
                    if (Inside(dest)) Edge(dest);
                    else if (Tail(dest)) tails.Add(dest);
                    else return new(null, "外部分支目标未证实");
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
        foreach (var (jump, t) in tables)
            if (targets.Append(entry).Any(p => p > t.Guard && p <= jump && p != t.First) ||
                instructions.Any(pair => pair.Value.Form is Form.Branch || pair.Value.Conditional ?
                    pair.Value.Destination(pair.Key) == t.First : false) || entry == t.First || pads.ContainsValue(t.First) ||
                tables.Values.Any(other => other.Arms.Contains(t.First))) return new(null, "跳转表边界未证实");

        var heads = targets.Append(entry).Concat(tails).ToHashSet();
        // 用实参行分段传递长直线上的值，限制规范化一次切片所需展开的表达式深度。
        if (instructions.Count > 16)
        {
            int count = 0;
            foreach (var pc in instructions.Keys.Order())
            {
                if (heads.Contains(pc)) count = 0;
                if (count == 16) { heads.Add(pc); count = 0; }
                count++;
            }
        }
        var live = LiveRows.Compute(heads, instructions, pads, tables.ToDictionary(p => p.Key, p => (p.Value.Index, p.Value.Arms)), f.End);
        var builder = new SnapshotBuilder(64);
        builder.SetReturnSlots(Abi.Slots(Abi.Return));
        int[] widths = Enumerable.Range(0, Abi.Count).Select(Abi.Width).ToArray();
        var ids = new Dictionary<(ulong Pc, ulong Defined), BlockId>();
        var work = new Queue<(ulong Pc, ulong Defined)>();
        BlockId Block(ulong pc, ulong defined)
        {
            var key = (pc, defined & live[pc].CallMask);
            if (ids.TryGetValue(key, out var existing)) return existing;
            var id = pc == entry && !targets.Contains(entry) ? builder.Entry : builder.Block(live[pc].Registers.Select(Abi.Width).ToArray());
            ids.Add(key, id); work.Enqueue(key); return id;
        }
        var initial = new Term[Abi.Count];
        for (int r = 0; r < initial.Length; r++)
        {
            if (Abi.Entry(r) is not Slot slot) initial[r] = builder.Terms.Undefined(widths[r]);
            else if (r is >= 40 and < 48) initial[r] = builder.Terms.Concat(builder.EntryParameter(slot, 64), builder.Terms.Undefined(64));
            else initial[r] = builder.EntryParameter(slot, widths[r]);
        }
        Term[] Out(ulong dest, Term[] row) => live[dest].Registers.Select(r => row[r]).ToArray();
        var empty = widths.Select(builder.Terms.Undefined).ToArray();
        var first = Block(entry, arguments);
        if (first != builder.Entry) builder.Jump(builder.Entry, first, Out(entry, initial));

        // 有定义的调用槽随边传播；同一地址只在槽位集合不同时另建块。
        while (work.TryDequeue(out var key))
        {
            var (start, defined) = key;
            var b = ids[key];
            var row = b == builder.Entry ? initial : (Term[])empty.Clone();
            if (b != builder.Entry)
            {
                var layout = live[start].Registers;
                for (int j = 0; j < layout.Length; j++) row[layout[j]] = builder.Parameter(b, j);
            }
            var state = new Machine(builder, b, row);
            Exit To(ulong dest) => Exit.To(Block(dest, defined), Out(dest, state.Row));
            for (ulong pc = start; ; pc += 4)
            {
                if (tails.Contains(pc))
                {
                    var link = state.G(30);
                    state.Call(builder.Terms.Bits(pc, 64), pc, defined, false);
                    builder.Return(b, state.ReturnValues(link)); break;
                }
                var i = instructions[pc];
                if (i.Form == Form.Return) { builder.Return(b, state.ReturnValues(state.G(i.N))); break; }
                if (i.Form == Form.Trap) { builder.Terminate(b, Terminator.Single(Exit.Trap, pc)); break; }
                if (i.Form == Form.BranchRegister)
                {
                    var t = tables[pc];
                    // 末项兼作默认出口；支配此处的有界比较排除了所有越界值。
                    var arms = t.Arms.Select(To).Append(To(t.Arms[^1])).ToImmutableArray();
                    builder.Terminate(b, Terminator.Switch(state.G(t.Index, 32), arms, pc)); break;
                }
                if (i.Conditional)
                {
                    builder.Terminate(b, Terminator.Branch(state.Predicate(i), To(i.Destination(pc)), To(pc + 4), pc)); break;
                }
                if (i.Form == Form.Branch) { builder.Terminate(b, Terminator.Single(To(i.Destination(pc)), pc)); break; }
                if (i.IsCall)
                {
                    var target = i.Form == Form.Call ? builder.Terms.Bits(i.Destination(pc), 64) : state.G(i.N);
                    bool invoke = pads.TryGetValue(pc, out ulong pad);
                    var unwind = state.Call(target, pc, defined, invoke);
                    defined = results;
                    if (invoke) { builder.Terminate(b, Terminator.Invoke(To(pc + 4), Exit.To(Block(pad, defined), Out(pad, unwind)), pc)); break; }
                    if (pc + 4 == f.End) { builder.Terminate(b, Terminator.Single(Exit.NoReturn, pc)); break; }
                }
                else { state.Apply(i, pc); ulong bits = (ulong)LiveRows.Description(i).Write & arguments; defined |= bits; }
                if (heads.Contains(pc + 4)) { builder.Terminate(b, Terminator.Single(To(pc + 4), pc)); break; }
            }
            if (state.PlatformRegister) return new(null, "读取平台寄存器 x18");
        }
        return new(builder.Build(), null);
    }
}
