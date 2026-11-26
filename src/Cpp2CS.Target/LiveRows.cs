namespace Cpp2CS.Target;

/// <summary>反向传播出口所需的寄存器。块内在首次使用前已整写的寄存器无需列入入边实参。</summary>
internal static class LiveRows
{
    static UInt128 Bit(int r) => UInt128.One << r;
    static UInt128 Mask(IEnumerable<int> regs) => regs.Aggregate(UInt128.Zero, (m, r) => m | Bit(r));
    static UInt128 G(int r) => r == 31 ? 0 : Bit(r);
    static UInt128 V(int r) => Bit(32 + r);
    static readonly UInt128 flags = Mask(Enumerable.Range(Abi.Negative, 4));
    static readonly UInt128 arguments = Mask(Abi.Arguments), returns = Mask(Abi.Return);
    static readonly UInt128 volatileRegs = Mask(Enumerable.Range(0, 19).Append(30).Concat(Enumerable.Range(32, 8))
        .Concat(Enumerable.Range(48, 16))) | flags;

    public static (UInt128 Read, UInt128 Write) Description(Instruction i)
    {
        UInt128 d = G(i.D), n = G(i.N), m = G(i.M), a = G(i.A);
        switch (i.Form)
        {
            case Form.Return: return ((returns & ~Bit(30)) | n, 0);
            case Form.Call: case Form.CallRegister: return (arguments | n, volatileRegs);
            case Form.Condition: return (flags, 0);
            case Form.CompareBranch: case Form.TestBranch: return (d, 0);
            case Form.Thread: return (Bit(Abi.Thread), d);
            case Form.Wide: return (i.Name == "movk" ? d : 0, d);
            case Form.Address: return (0, d);
            case Form.Immediate:
            case Form.Shifted:
            case Form.Extended:
                bool sp = i.Form != Form.Shifted, set = i.Name.EndsWith('s');
                return ((sp ? Bit(i.N) : n) | (i.Form == Form.Immediate ? 0 : m), (sp && !set ? Bit(i.D) : d) | (set ? flags : 0));
            case Form.Mask:
            case Form.Logical:
                set = i.Name is "ands" or "bics";
                return (n | (i.Form == Form.Logical ? m : 0), (i.Form == Form.Mask && !set ? Bit(i.D) : d) | (set ? flags : 0));
            case Form.Bitfield: return (n | (i.Name == "bfm" ? d : 0), d);
            case Form.Select: return (n | m | flags, d);
            case Form.Multiply: case Form.LongMultiply: return (n | m | a, d);
            case Form.Binary: case Form.Extract: return (n | m, d);
            case Form.Unary: return (n, d);
            case Form.Memory:
            case Form.Literal:
            case Form.Pair:
                UInt128 loc = i.Form == Form.Literal ? 0 : Bit(i.N);
                if (i.Mode >= 4) loc |= m;
                UInt128 data = i.Vector ? V(i.D) : d;
                if (i.Form == Form.Pair) data |= i.Vector ? V(i.A) : a;
                UInt128 wb = i.Mode is 1 or 3 ? Bit(i.N) : 0;
                return i.Name[0] == 's' ? (data | loc, wb) : (loc, data | wb);
            case Form.FloatCompare: return (V(i.N) | (i.Mode == 0 ? V(i.M) : 0), flags);
            case Form.FloatMove: return i.Mode == 0 ? (V(i.N), d) : (n, V(i.D));
            case Form.FloatImmediate: case Form.VectorImmediate: return (0, V(i.D));
            case Form.Convert: return i.Name switch { "fcvt" => (V(i.N), V(i.D)), "fcvtzs" or "fcvtzu" => (V(i.N), d), _ => (n, V(i.D)) };
            case Form.FloatUnary: return (V(i.N), V(i.D));
            case Form.FloatSelect: return (V(i.N) | V(i.M) | flags, V(i.D));
            case Form.Fused: return (V(i.N) | V(i.M) | V(i.A), V(i.D));
            case Form.FloatBinary: case Form.VectorOr: return (V(i.N) | V(i.M), V(i.D));
            case Form.Branch: case Form.BranchRegister: case Form.Nop: case Form.Trap: return (0, 0);
            default: throw new InvalidOperationException("指令缺少寄存器使用说明");
        }
    }

    public static Dictionary<ulong, (int[] Registers, ulong CallMask)> Compute(HashSet<ulong> heads, Dictionary<ulong, Instruction> code,
        Dictionary<ulong, ulong> pads, Dictionary<ulong, (int Index, ulong[] Arms)> tables, ulong end)
    {
        var blocks = new Dictionary<ulong, (UInt128 Use, UInt128 Def, ulong Calls, List<ulong> Next)>();
        var live = new Dictionary<ulong, UInt128>();
        var calls = new Dictionary<ulong, ulong>();
        foreach (ulong start in heads)
        {
            UInt128 use = 0, def = 0; var next = new List<ulong>();
            ulong callUse = 0;
            if (!code.ContainsKey(start)) { use = arguments | (returns & ~volatileRegs) | Bit(30); callUse = (ulong)arguments; }
            else for (ulong pc = start; ; pc += 4)
                {
                    var i = code[pc]; var (read, write) = Description(i);
                    if (i.IsCall) callUse |= (ulong)(arguments & ~def);
                    use |= read & ~def; def |= write;
                    if (i.Form is Form.Trap or Form.Return) break;
                    if (i.Form == Form.BranchRegister)
                    { var t = tables[pc]; use |= G(t.Index) & ~def; next.AddRange(t.Arms); break; }
                    if (i.Form == Form.Branch || i.Conditional) next.Add(i.Destination(pc));
                    if (i.Form == Form.Branch || pc + 4 == end) break;
                    if (pads.TryGetValue(pc, out var pad)) next.Add(pad);
                    if (heads.Contains(pc + 4)) { next.Add(pc + 4); break; }
                }
            blocks.Add(start, (use, def, callUse, next)); live.Add(start, use); calls.Add(start, callUse);
        }
        ulong[] order = heads.OrderDescending().ToArray();
        bool changed;
        do
        {
            changed = false;
            foreach (ulong pc in order)
            {
                var b = blocks[pc]; UInt128 need = b.Use;
                ulong callNeed = b.Calls;
                foreach (ulong next in b.Next) { need |= live[next] & ~b.Def; callNeed |= calls[next] & ~(ulong)b.Def; }
                if (calls[pc] != callNeed) { calls[pc] = callNeed; changed = true; }
                if (live[pc] != need) { live[pc] = need; changed = true; }
            }
        } while (changed);
        return live.ToDictionary(pair => pair.Key, pair => (Enumerable.Range(0, Abi.Count).Where(r => (pair.Value & Bit(r)) != 0).ToArray(), calls[pair.Key]));
    }
}
