using System.Buffers.Binary;
using Cpp2CS.Input;

namespace Cpp2CS.Target;

/// <summary>DDI 0487：无符号条件分支限定索引，LDRB/LDRH 取无符号项，ADD 将项乘四并加到代码基址。</summary>
public sealed record JumpTableInfo(ulong Load, int Index, ulong Address, int Bytes, ulong Basis, ulong[] Arms);

internal sealed class JumpTables
{
    readonly Dictionary<ulong, Instruction> code;
    readonly Dictionary<ulong, List<ulong>> parents = [];
    readonly ulong entry;
    readonly Dictionary<(ulong, int), HashSet<ulong>> definitions = [];
    const ulong EntryValue = ulong.MaxValue;

    public JumpTables(ulong entry, Dictionary<ulong, Instruction> code, Dictionary<ulong, ulong> pads,
        Dictionary<ulong, JumpTableInfo> tables)
    {
        this.entry = entry;
        this.code = code;
        void Edge(ulong from, ulong to)
        {
            if (!code.ContainsKey(to)) return;
            if (!parents.TryGetValue(to, out var list)) parents[to] = list = [];
            list.Add(from);
        }
        foreach (var (pc, i) in code)
        {
            if (i.Form == Form.BranchRegister)
            {
                if (tables.TryGetValue(pc, out var t))
                    foreach (ulong arm in t.Arms.Distinct()) Edge(pc, arm);
                continue;
            }
            if (i.Form == Form.Branch || i.Conditional) Edge(pc, i.Destination(pc));
            if (i.Form is Form.Return or Form.Trap or Form.Branch) continue;
            Edge(pc, pc + 4);
            if (pads.TryGetValue(pc, out ulong pad)) Edge(pc, pad);
        }
    }

    // 所有可达入边逆向走到第一次整写。没有改写的环只走一圈，函数入口单列为一个来源。
    HashSet<ulong> Definitions(ulong pc, int reg)
    {
        if (definitions.TryGetValue((pc, reg), out var known)) return known;
        var result = new HashSet<ulong>();
        var visited = new HashSet<ulong>();
        var work = new Stack<ulong>();
        work.Push(pc);
        while (work.TryPop(out ulong at))
        {
            if (!visited.Add(at)) continue;
            if (at == entry) result.Add(EntryValue);
            if (!parents.TryGetValue(at, out var incoming)) continue;
            foreach (ulong p in incoming)
                if ((LiveRows.Description(code[p]).Write & (UInt128.One << reg)) != 0) result.Add(p);
                else work.Push(p);
        }
        return definitions[(pc, reg)] = result;
    }

    readonly record struct Address(bool Stack, ulong Offset);
    Address? AddressOf(ulong pc, int reg, int depth = 0)
    {
        if (depth == 32) return null;
        Address? agreed = null;
        foreach (ulong p in Definitions(pc, reg))
        {
            Address? value = null;
            if (p == EntryValue)
            {
                if (reg == 31) value = new(true, 0);
            }
            else
            {
                var i = code[p];
                if (i.Form == Form.Address)
                    value = new(false, i.Destination(i.Name == "adrp" ? p & ~4095ul : p));
                else if (i is { Form: Form.Immediate, Width: 64, Name: "add" or "sub" } ||
                    i.Form is Form.Memory or Form.Pair && i.Mode is 1 or 3 && i.N == reg)
                {
                    var basis = AddressOf(p, i.N, depth + 1);
                    long offset = (i.Name == "sub" ? -i.Imm : i.Imm) << i.Shift;
                    if (basis is { } b) value = b with { Offset = b.Offset + (ulong)offset };
                }
            }
            if (value == null || agreed != null && agreed != value) return null;
            agreed = value;
        }
        return agreed;
    }

    bool Previous(ulong pc, out ulong p)
    {
        p = 0;
        if (pc == entry || !parents.TryGetValue(pc, out var edges) || edges.Count != 1) return false;
        p = edges[0];
        return true;
    }

    static bool WordResult(Instruction i, int reg) => i.Width == 32 && !i.IsCall &&
        (i.D == reg || i.Form == Form.Pair && i.A == reg) && i.Form switch
        {
            Form.Memory or Form.Pair or Form.Literal => !i.Vector && i.Name[0] == 'l',
            Form.Wide or Form.Immediate or Form.Shifted or Form.Extended or Form.Logical or Form.Mask or
                Form.Bitfield or Form.Select or Form.Multiply or Form.Unary or Form.Binary or Form.Extract or Form.Reverse => true,
            _ => false
        };

    // 位掩码与来源共同标识一个索引。W 寄存器复制清零高位，AND 只保留掩码内的位。
    readonly record struct IndexValue(ulong Definition, int Register, ulong Mask);
    bool Bounded(ulong loadPc, Instruction load, out int count)
    {
        count = 0;
        var path = new List<ulong>();
        ulong at = loadPc, guard = EntryValue, compare = EntryValue;
        bool inclusive = false;
        var visited = new HashSet<ulong> { at };
        while (Previous(at, out ulong p) && visited.Add(p))
        {
            var i = code[p];
            if (i.IsCall || i.Form == Form.BranchRegister) break;
            if (guard == EntryValue && i.Form == Form.Condition && i.Destination(p) != p + 4)
            {
                bool taken = at == i.Destination(p);
                if (taken ? i.Mode is 3 or 9 : i.Mode is 2 or 8)
                {
                    guard = p;
                    inclusive = i.Mode is 8 or 9;
                }
            }
            path.Add(p);
            if (guard != EntryValue && compare == EntryValue && (LiveRows.Description(i).Write >> Abi.Negative) != 0)
            {
                if (i is not { Form: Form.Immediate, Name: "subs", D: 31 } || i.N == 31) return false;
                compare = p;
            }
            at = p;
        }
        if (compare == EntryValue) return false;
        var cmp = code[compare];
        long length = (cmp.Imm << cmp.Shift) + (inclusive ? 1 : 0);
        if (length <= 0 || length > int.MaxValue) return false;
        var row = new IndexValue[32];
        for (int r = 0; r < row.Length; r++) row[r] = new(EntryValue, r, ulong.MaxValue);
        IndexValue bound = default;
        for (int j = path.Count - 1; j >= 0; j--)
        {
            ulong p = path[j];
            var i = code[p];
            var src = row[i.N]; var right = row[i.M];
            if (p == compare) bound = src with { Mask = src.Mask & (cmp.Width == 32 ? uint.MaxValue : ulong.MaxValue) };
            uint written = i.WrittenGeneralRegisters;
            while (written != 0)
            {
                int r = System.Numerics.BitOperations.TrailingZeroCount(written);
                written &= written - 1;
                ulong mask = WordResult(i, r) ? uint.MaxValue : ulong.MaxValue;
                row[r] = i switch
                {
                    { Form: Form.Logical, Name: "orr", N: 31, Mode: 0, Shift: 0, M: < 31 } => right with { Mask = right.Mask & mask },
                    { Form: Form.Mask, Name: "and", N: < 31 } => src with { Mask = src.Mask & (ulong)i.Imm & mask },
                    _ => new(p, r, mask)
                };
            }
        }
        var index = row[load.M];
        if (load.Mode is 6 or 10) index = index with { Mask = index.Mask & uint.MaxValue };
        if (bound != index)
        {
            if (index.Definition != EntryValue || bound.Definition != EntryValue || index.Register != bound.Register ||
                (index.Mask & uint.MaxValue) != (bound.Mask & uint.MaxValue)) return false;
            var defs = Definitions(at, index.Register);
            if (defs.Count == 0 || defs.Any(p => p == EntryValue || !WordResult(code[p], index.Register))) return false;
        }
        count = (int)length;
        return true;
    }

    public JumpTableInfo? Resolve(ulong branch, Frame frame, Elf64 elf, byte[] file, HashSet<ulong> relocated, out string reason)
    {
        // 从 BR 反找定义目标的 ADD 和读取表项的指令，读表与跳转必须在同一直线路径。
        reason = "目标无相对表项加法";
        ulong at = branch, sumPc = 0, loadPc = 0;
        int reg = code[branch].N;
        while (Previous(at, out ulong p) && p + 4 == at)
        {
            var i = code[p];
            if (i.Conditional || i.IsCall || i.Form is Form.Branch or Form.BranchRegister) return null;
            at = p;
            if ((i.WrittenGeneralRegisters & (1u << reg)) == 0) continue;
            if (sumPc == 0)
            {
                if (i is not { Name: "add", Width: 64, Shift: 2, M: < 31, N: < 31 } ||
                    !(i.Form == Form.Shifted && i.Mode == 0 || i.Form == Form.Extended && i.Mode is 2 or 6)) return null;
                sumPc = p; reg = i.M;
                reason = "表项宽度或寻址未证实";
            }
            else
            {
                if (i is not { Form: Form.Memory, Name: "ldrb" or "ldrh", Vector: false, M: < 31, Mode: 6 or 7 or 10 } ||
                    i.Shift != (i.Size == 8 ? 0 : 1)) return null;
                loadPc = p; break;
            }
        }
        if (loadPc == 0) return null;
        var load = code[loadPc];
        var stack = AddressOf(branch, 31);
        reason = stack is { Stack: true, Offset: 0 } ? "SP 已归位" : "SP 偏移未证实";
        if (stack is not { Stack: true, Offset: not 0 }) return null;
        reason = "上界或索引同一性未证实";
        if (!Bounded(loadPc, load, out int count)) return null;
        reason = "表地址或目标基址未证实";
        if (AddressOf(loadPc, load.N) is not { Stack: false } table || AddressOf(sumPc, code[sumPc].N) is not { Stack: false } basis) return null;
        int bytes = load.Size / 8;
        ulong address = table.Offset, length = (ulong)count * (uint)bytes;
        reason = "表不在无重定位的只读段";
        if (length > ulong.MaxValue - address || elf.FileOffset(address, length) is not int start) return null;
        var owners = elf.Segments.Where(s => s.Type == 1 && s.MemorySize != 0 &&
            address < s.Address + s.MemorySize && s.Address < address + length).ToArray();
        if (owners is not [var owner] || (owner.Flags & 6) != 4) return null;
        for (ulong a = address > 7 ? address - 7 : 0; a < address + length; a++) if (relocated.Contains(a)) return null;
        var arms = new ulong[count];
        reason = "表项目标不在本 FDE 的指令边界";
        for (int j = 0; j < count; j++)
        {
            int offset = start + j * bytes;
            ulong target = basis.Offset + 4ul * (bytes == 1 ? file[offset] : BinaryPrimitives.ReadUInt16LittleEndian(file.AsSpan(offset)));
            if (target < frame.Start || target >= frame.End || (target & 3) != 0) return null;
            arms[j] = target;
        }
        return new(loadPc, load.M, address, bytes, basis.Offset, arms);
    }
}
