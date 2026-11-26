using Cpp2CS.Target;

namespace Cpp2CS.Tools.LiftCheck;

/// <summary>沿 Unicorn 的实际路径和 Capstone 的寄存器读写集回溯严格观察的来源。只作诊断。</summary>
internal sealed class UndefinedSource(Trace trace)
{
    readonly record struct Step(ulong Pc, Instruction Code, NativeInstruction Native, int Events);
    readonly List<Step> path = [];
    int observed = -1;
    public void Record(ulong pc, uint word, NativeInstruction native, int events)
    {
        if (observed >= 0 && events > trace.Events.Count) return;
        path.Add(new(pc, Decoder.Decode(word), native, events));
        if (pc == trace.Pc && events <= trace.Events.Count) observed = path.Count - 1;
    }

    public string Describe()
    {
        if (observed < 0) return "原生路径未到达";
        var site = path[observed]; var i = site.Code;
        var roots = new HashSet<string>();
        var pending = new Stack<(int Before, int Register, int Width)>();
        var seen = new HashSet<(int, int, int)>();
        void Operand(int reg, int width = 64) => pending.Push((observed, reg, width));
        string role = trace.Diagnostic!.Split('@')[0];
        if (role is "写地址" or "读地址")
        {
            if (i.Form != Form.Literal) Operand(i.N);
            if (i.Mode >= 4) Operand(i.M, (i.Mode - 4 & 3) == 3 ? 64 : 32);
        }
        else if (role == "写值")
        {
            int reg = i.Form == Form.Pair && trace.Events.Count != site.Events ? i.A : i.D;
            if (i.Vector || i.Form == Form.SimdTransfer) Operand(32 + reg, i.Size);
            else if (reg != 31) Operand(reg, i.Size);
        }
        else if (role == "调用目标") Operand(i.N);
        else if (i.Form == Form.Condition) Operand(65, 4);
        else if (i.Form is Form.TestBranch or Form.CompareBranch) Operand(i.D, i.Width);
        else Operand(i.N);
        while (pending.TryPop(out var item))
        {
            if (!seen.Add(item)) continue;
            var (before, reg, width) = item;
            bool defined = false;
            for (int j = before - 1; j >= 0; j--)
            {
                var step = path[j]; var code = step.Code;
                if (code.IsCall)
                {
                    if (reg is >= 19 and <= 29 or 31 || reg is >= 40 and < 48 && width <= 64) continue;
                    if (reg is not (0 or 1 or >= 32 and <= 35)) roots.Add($"调用破坏 {Register(reg)}@{step.Pc:x}");
                    defined = true; break;
                }
                if ((step.Native.Written & UInt128.One << reg) == 0) continue;
                defined = true;
                if (code.Form is Form.Memory or Form.Pair or Form.Literal or Form.SimdTransfer && code.Name.StartsWith("ld") &&
                    !(reg == code.N && code.Mode is 1 or 3)) break;
                UInt128 reads = step.Native.Read;
                while (reads != 0)
                {
                    int r = (int)UInt128.TrailingZeroCount(reads);
                    pending.Push((j, r, r >= 32 && r < 64 ? Math.Min(128, code.Width) : 64));
                    reads &= reads - 1;
                }
                break;
            }
            if (!defined && (Abi.Entry(reg) == null || reg is >= 40 and < 48 && width > 64))
                roots.Add($"入口未定义 {Register(reg)}");
        }
        string sources = roots.Count == 0 ? "需核对寄存器来源" : string.Join("、", roots.Order());
        return $"{site.Native.Name} {site.Native.Operands}\t{sources}";
    }

    static string Register(int r) => r switch { 31 => "sp", 65 => "NZCV", >= 32 => "v" + (r - 32), _ => "x" + r };
}
