using System.Globalization;
using Cpp2CS.Target;

namespace Cpp2CS.Tools.LiftCheck;

/// <summary>只描述到达未确认 BR 的指令形态。合流时保留相同来源，栈槽按入口 SP 的字节偏移追踪。</summary>
internal static class BranchSurvey
{
    enum Origin { Unknown, Argument, Stack, Link, Reload, Image, IndexedImage, ImageLoad, Pointer, FirstLoad, Chain, Relative, ChangedLink }
    readonly record struct Value(Origin Origin, long Offset = 0, bool Indexed = false);
    sealed class State
    {
        public Value[] Registers = new Value[32];
        public Dictionary<(long Offset, int Bytes), Value> Stack = [];
        public State Copy() => new() { Registers = (Value[])Registers.Clone(), Stack = new(Stack) };
        public bool Merge(State incoming)
        {
            bool changed = false;
            for (int i = 0; i < Registers.Length; i++)
                if (Registers[i] != default && Registers[i] != incoming.Registers[i]) { Registers[i] = default; changed = true; }
            foreach (var (k, v) in Stack.ToArray())
                if (incoming.Stack.GetValueOrDefault(k) != v) { Stack.Remove(k); changed = true; }
            return changed;
        }
    }

    public static void Write(Scan scan, string prefix)
    {
        using var rows = new StreamWriter(prefix + ".branches.local.tsv");
        foreach (string line in File.ReadLines(prefix + ".rejected.local.tsv"))
        {
            ulong entry = ulong.Parse(line.AsSpan(0, line.IndexOf('\t')), NumberStyles.HexNumber);
            var locations = new LiftLocations(false);
            scan.Target.Lift(entry, locations);
            ulong branch = locations.UnresolvedBranch ?? throw new InvalidDataException("清单与跳转诊断不一致");
            var state = AtBranch(scan, entry, branch, locations);
            var sp = state.Registers[31]; var link = state.Registers[30];
            var target = state.Registers[Decoder.Decode(scan.Target.Word(branch)).N];
            string stack = sp.Origin != Origin.Stack ? "不明" : sp.Offset == 0 ? "是" : "否";
            string lr = link.Origin switch { Origin.Reload => "栈恢复", Origin.Link => "入口值保留", Origin.Unknown => "不明", _ => "未恢复" };
            string source = target.Origin switch
            {
                Origin.Argument when target.Offset == 0 => "参数直传",
                Origin.Chain when target.Offset == 0 => "类指针链形态",
                Origin.ImageLoad or Origin.Relative when target.Offset == 0 => "映像表读取",
                _ => "其他"
            };
            rows.WriteLine($"{entry:x}\t{branch:x}\t{stack}\t{lr}\t{source}\t{(target.Indexed ? "疑表" : "未见表形态")}");
        }
    }

    static State AtBranch(Scan scan, ulong entry, ulong branch, LiftLocations locations)
    {
        var frame = scan.Target.Unwind.Find(entry)!.Value;
        var sites = scan.Target.Unwind.Sites(frame);
        var states = new Dictionary<ulong, State>();
        var pending = new Queue<ulong>();
        var queued = new HashSet<ulong>();
        void Send(ulong pc, State state)
        {
            if (pc < frame.Start || pc >= frame.End) return;
            if (states.TryGetValue(pc, out var previous))
            {
                if (!previous.Merge(state)) return;
            }
            else states.Add(pc, state.Copy());
            if (queued.Add(pc)) pending.Enqueue(pc);
        }
        var initial = new State();
        for (int i = 0; i < 8; i++) initial.Registers[i] = new(Origin.Argument);
        initial.Registers[30] = new(Origin.Link); initial.Registers[31] = new(Origin.Stack);
        Send(entry, initial);
        while (pending.TryDequeue(out ulong pc))
        {
            queued.Remove(pc);
            if (pc == branch) continue;
            var state = states[pc].Copy();
            var i = Decoder.Decode(scan.Target.Word(pc));
            if (i.Form is Form.Return or Form.Trap or Form.Unknown) continue;
            if (i.Form == Form.BranchRegister)
            {
                if (locations.SwitchTargets.TryGetValue(pc, out var targets))
                    foreach (ulong dest in targets.Distinct()) Send(dest, state);
                continue;
            }
            if (i.Conditional || i.Form == Form.Branch) Send(i.Destination(pc), state);
            if (i.Form == Form.Branch) continue;
            Transfer(scan, state, i, pc);
            if (i.IsCall)
                foreach (var site in sites)
                    if (site.Start <= pc && pc < site.End && site.Landing != 0) Send(site.Landing, state);
            Send(pc + 4, state);
        }
        return states[branch];
    }

    static Value Add(Value value, long delta) => delta == 0 ? value : value.Origin switch
    {
        Origin.Stack or Origin.Image or Origin.Argument or Origin.FirstLoad or Origin.Pointer =>
            value with { Offset = unchecked(value.Offset + delta) },
        _ => default
    };

    static void Transfer(Scan scan, State state, Instruction i, ulong pc)
    {
        var r = state.Registers;
        if (i.IsCall)
        {
            Array.Clear(r, 0, 19);
            r[0] = new(Origin.Pointer); r[30] = new(Origin.ChangedLink);
            return;
        }
        bool InImage(long address) => scan.Elf.Segments.Any(s => s.Type == 1 && (ulong)address - s.Address < s.MemorySize);
        Value Read(Value address, int bytes)
        {
            if (address.Origin == Origin.Stack)
            {
                var stored = state.Stack.GetValueOrDefault((address.Offset, bytes));
                return stored.Origin == Origin.Link ? new(Origin.Reload) : stored;
            }
            if (address.Origin is Origin.Image or Origin.IndexedImage && InImage(address.Offset))
                return new(Origin.ImageLoad, Indexed: address.Indexed);
            if (bytes != 8) return new(Origin.Pointer, Indexed: address.Indexed);
            if (address.Origin == Origin.FirstLoad && address.Offset > 0) return new(Origin.Chain);
            if (address.Origin is Origin.Argument or Origin.Pointer && address.Offset == 0) return new(Origin.FirstLoad);
            return new(Origin.Pointer, Indexed: address.Indexed);
        }
        void Store(Value address, int bytes, Value value)
        {
            if (address.Origin != Origin.Stack) return;
            foreach (var k in state.Stack.Keys.ToArray())
                if (k.Offset < address.Offset + bytes && address.Offset < k.Offset + k.Bytes) state.Stack.Remove(k);
            if (value != default) state.Stack[(address.Offset, bytes)] = value;
        }
        if (i.Form is Form.Memory or Form.Pair or Form.Literal)
        {
            var basis = i.Form == Form.Literal ? new Value(Origin.Image, (long)pc) : r[i.N];
            var at = Add(basis, i.Mode == 1 ? 0 : i.Imm);
            if (i.Mode >= 4) at = basis.Origin == Origin.Image ? new(Origin.IndexedImage, basis.Offset, true) : new(Origin.Pointer, Indexed: true);
            int bytes = i.Size / 8;
            void Access(int reg, Value address)
            {
                if (i.Name[0] == 's') Store(address, bytes, i.Vector || reg == 31 ? default : r[reg]);
                else if (!i.Vector && reg != 31) r[reg] = Read(address, bytes);
            }
            Access(i.D, at);
            if (i.Form == Form.Pair) Access(i.A, Add(at, bytes));
            if (i.Mode is 1 or 3) r[i.N] = Add(basis, i.Imm);
            return;
        }
        if (i.Form == Form.Address && i.D != 31)
        {
            r[i.D] = new(Origin.Image, (long)i.Destination(i.Name == "adrp" ? pc & ~4095ul : pc)); return;
        }
        if (i is { Form: Form.Immediate, Width: 64, Name: "add" or "sub" })
        {
            r[i.D] = Add(r[i.N], (i.Name == "sub" ? -i.Imm : i.Imm) << i.Shift); return;
        }
        if (i is { Form: Form.Logical, Width: 64, Name: "orr", N: 31, Mode: 0, Shift: 0 } && i.D != 31)
        {
            r[i.D] = i.M == 31 ? default : r[i.M]; return;
        }
        if (i is { Form: Form.Shifted or Form.Extended, Width: 64, Name: "add" } && i.D != 31)
        {
            var left = r[i.N]; var right = r[i.M];
            if (left.Origin == Origin.Image && right.Origin == Origin.ImageLoad || right.Origin == Origin.Image && left.Origin == Origin.ImageLoad)
                r[i.D] = new(Origin.Relative, Indexed: left.Indexed || right.Indexed);
            else if (left.Origin == Origin.Image) r[i.D] = new(Origin.IndexedImage, left.Offset, true);
            else r[i.D] = new(Origin.Unknown, Indexed: left.Indexed || right.Indexed);
            return;
        }
        uint written = i.WrittenGeneralRegisters;
        while (written != 0)
        {
            int reg = System.Numerics.BitOperations.TrailingZeroCount(written);
            r[reg] = default; written &= written - 1;
        }
    }
}
