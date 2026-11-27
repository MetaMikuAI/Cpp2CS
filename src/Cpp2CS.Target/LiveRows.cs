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

    static readonly UInt128 tailInputs = Mask(Abi.TailInputs);

    public static (UInt128 Read, UInt128 Write) Description(Instruction i)
    {
        UInt128 d = G(i.D), n = G(i.N), m = G(i.M), a = G(i.A);
        switch (i.Form)
        {
            case Form.PointerAuth: return (Bit(30) | Bit(31), Bit(30));
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
            case Form.ConditionalCompare: return (flags | n | (i.Vector ? 0 : m), flags);
            case Form.FloatConditionalCompare: return (flags | V(i.N) | V(i.M), flags);
            case Form.Reverse: return (n, d);
            case Form.RoundConvert: return (V(i.N), d);
            case Form.SimdCopy:
                return i.Mode switch
                {
                    0 => (n, V(i.D)), 1 or 2 => (V(i.N), V(i.D)), 3 => (V(i.D) | n, V(i.D)),
                    4 => (V(i.D) | V(i.N), V(i.D)), _ => (V(i.N), d)
                };
            case Form.SimdImmediate: return (i.Name is "bic" or "orr" ? V(i.D) : 0, V(i.D));
            case Form.SimdFloatImmediate: return (0, V(i.D));
            case Form.SimdBits: return (V(i.N) | V(i.M) | (i.Name is "bsl" or "bit" or "bif" ? V(i.D) : 0), V(i.D));
            case Form.SimdBinary: case Form.SimdIndexed: case Form.SimdPermute: return (V(i.N) | V(i.M), V(i.D));
            case Form.SimdNarrow: return (V(i.N) | (i.Mode == 1 ? V(i.D) : 0), V(i.D));
            case Form.SimdUnary: case Form.SimdWiden: case Form.SimdReduce: case Form.SimdShift: return (V(i.N), V(i.D));
            case Form.SimdTransfer:
                var baseReg = Bit(i.N);
                var inputs = baseReg | (i.Mode != 0 ? m : 0);
                if (i.Name == "st2") inputs |= V((i.D + 1) % 32);
                if (i.Name != "ld1r") inputs |= V(i.D);
                return (inputs, (i.Mode != 0 ? baseReg : 0) | (i.Name[0] == 'l' ? V(i.D) : 0));
            default: throw new InvalidOperationException("指令缺少寄存器使用说明");
        }
    }

    public static Dictionary<ulong, int[]> Compute(HashSet<ulong> heads, Dictionary<ulong, Instruction> code,
        Dictionary<ulong, CallSite> pads, Dictionary<ulong, JumpTableInfo> tables, ulong end)
    {
        var blocks = new Dictionary<ulong, (UInt128 Use, UInt128 Def, List<ulong> Next)>();
        var live = new Dictionary<ulong, UInt128>();

        foreach (ulong start in heads)
        {
            UInt128 use = 0, def = 0; var next = new List<ulong>();
            for (ulong pc = start; ; pc += 4)
            {
                var i = code[pc]; var (read, write) = Description(i);
                if (i.Form == Form.BranchRegister && !tables.ContainsKey(pc))
                    read |= G(i.N) | tailInputs;
                if ((i.Form == Form.Branch || i.Conditional) && !code.ContainsKey(i.Destination(pc)))
                    read |= tailInputs;
                if ((write & Bit(31)) != 0) read |= Bit(31);
                use |= read & ~def; def |= write;
                if (i.Form is Form.Trap or Form.Return) break;
                if (i.Form == Form.BranchRegister)
                {
                    if (tables.TryGetValue(pc, out var t)) next.AddRange(t.Arms);
                    break;
                }
                if ((i.Form == Form.Branch || i.Conditional) && code.ContainsKey(i.Destination(pc))) next.Add(i.Destination(pc));
                if (i.Form == Form.Branch || pc + 4 == end) break;
                if (pads.TryGetValue(pc, out var site)) next.Add(site.Landing);
                if (heads.Contains(pc + 4)) { next.Add(pc + 4); break; }
            }
            blocks.Add(start, (use, def, next)); live.Add(start, use);
        }
        ulong[] order = heads.OrderDescending().ToArray();
        bool changed;
        do
        {
            changed = false;
            foreach (ulong pc in order)
            {
                var b = blocks[pc]; UInt128 need = b.Use;
                foreach (ulong next in b.Next) need |= live[next] & ~b.Def;
                if (live[pc] != need) { live[pc] = need; changed = true; }
            }
        } while (changed);
        return live.ToDictionary(pair => pair.Key, pair => Enumerable.Range(0, Abi.Count).Where(r => (pair.Value & Bit(r)) != 0).ToArray());
    }
}
