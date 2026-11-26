using System.Numerics;

namespace Cpp2CS.Target;

/// <summary>A64 解码结果的汇编表示。寄存器 31 按对应操作数解释为 SP 或 ZR。</summary>
public static class AssemblyText
{
    static readonly string[] conditions = ["eq", "ne", "hs", "lo", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le", "al", "nv"];
    static readonly string[] shifts = ["lsl", "lsr", "asr", "ror"];
    static readonly string[] extends = ["uxtb", "uxth", "uxtw", "uxtx", "sxtb", "sxth", "sxtw", "sxtx"];
    static string Reg(int r, int w, bool sp = false) => r == 31 ? (sp ? (w == 64 ? "sp" : "wsp") : (w == 64 ? "xzr" : "wzr")) : (w == 64 ? "x" : "w") + r;
    static string Vec(int r, int w) => (w switch { 8 => "b", 16 => "h", 32 => "s", 64 => "d", 128 => "q", _ => throw new ArgumentException() }) + r;

    public static string Format(Instruction i, ulong pc)
    {
        var (form, name, w, d, n, m, a, imm, mode, shift, size, vec) = i;
        string D = Reg(d, w), N = Reg(n, w), M = Reg(m, w), A = Reg(a, w);
        string I(long v) => "#" + v;
        string U(ulong v) => "#0x" + v.ToString("x");
        string target = U(i.Destination(pc));
        string Join(params string[] args) => name + " " + string.Join(", ", args);
        string shifted = shift == 0 && mode == 0 ? "" : ", " + shifts[mode % 4] + " " + I(shift);
        string cond = conditions[mode % 16];
        string operand;
        switch (form)
        {
            case Form.Unknown: return "?";
            case Form.Nop: return name;
            case Form.Trap: return Join(I(imm));
            case Form.Branch: case Form.Call: return Join(target);
            case Form.Return: return n == 30 ? name : Join(N);
            case Form.BranchRegister: case Form.CallRegister: return Join(N);
            case Form.Condition: return "b." + cond + " " + target;
            case Form.CompareBranch: return Join(D, target);
            case Form.TestBranch: return Join(D, I(shift), target);
            case Form.Address: return Join(D, U(i.Destination(name == "adrp" ? pc & ~4095ul : pc)));
            case Form.Wide:
                if (name != "movk" && (imm != 0 || shift == 0))
                {
                    ulong bits = (ulong)imm << shift;
                    if (name == "movn") bits = ~bits;
                    name = "mov"; return Join(D, U(w == 32 ? (uint)bits : bits));
                }
                return Join(D, I(imm) + (shift == 0 ? "" : ", lsl " + I(shift)));
            case Form.Immediate:
            case Form.Shifted:
            case Form.Extended:
                bool flags = name.EndsWith('s'), sp = form != Form.Shifted;
                operand = form switch
                {
                    Form.Immediate => I(imm) + (shift == 0 ? "" : ", lsl " + I(shift)),
                    Form.Extended => Reg(m, (mode & 3) == 3 && w == 64 ? 64 : 32) + ", " + extends[mode] + (shift == 0 ? "" : " " + I(shift)),
                    _ => M + shifted
                };
                if (d == 31 && flags) { name = name == "subs" ? "cmp" : "cmn"; return Join(Reg(n, w, sp), operand); }
                if (form == Form.Shifted && n == 31 && name.StartsWith("sub")) { name = flags ? "negs" : "neg"; return Join(D, operand); }
                if (form == Form.Immediate && name == "add" && imm == 0 && shift == 0 && (d == 31 || n == 31))
                { name = "mov"; return Join(Reg(d, w, true), Reg(n, w, true)); }
                return Join(Reg(d, w, sp && !flags), Reg(n, w, sp), operand);
            case Form.Mask:
            case Form.Logical:
                operand = form == Form.Mask ? U((ulong)imm) : M + shifted;
                if (name == "ands" && d == 31) { name = "tst"; return Join(N, operand); }
                if (n == 31 && (name == "orn" || name == "orr" && (form == Form.Mask || (mode == 0 && shift == 0))))
                { name = name == "orn" ? "mvn" : "mov"; return Join(D, operand); }
                return Join(Reg(d, w, form == Form.Mask && name != "ands"), N, operand);
            case Form.Bitfield:
                if (name != "bfm" && imm == 0 && (shift == 7 || shift == 15 || shift == 31 && w == 64 && name == "sbfm"))
                {
                    if (name == "sbfm" || w == 32) { name = (name == "sbfm" ? "sxt" : "uxt") + (shift == 7 ? "b" : shift == 15 ? "h" : "w"); return Join(D, Reg(n, 32)); }
                }
                if (name != "bfm" && shift == w - 1) { name = name == "sbfm" ? "asr" : "lsr"; return Join(D, N, I(imm)); }
                if (name == "ubfm" && shift + 1 == imm) { name = "lsl"; return Join(D, N, I(w - imm)); }
                if (shift < imm)
                { name = name == "bfm" ? "bfi" : name == "sbfm" ? "sbfiz" : "ubfiz"; return Join(D, N, I(w - imm), I(shift + 1)); }
                name = name == "bfm" ? "bfxil" : name == "sbfm" ? "sbfx" : "ubfx"; return Join(D, N, I(imm), I(shift - imm + 1));
            case Form.Select:
                if (n == m && mode < 14 && name != "csel")
                {
                    cond = conditions[mode ^ 1];
                    if (n == 31 && name != "csneg") { name = name == "csinc" ? "cset" : "csetm"; return Join(D, cond); }
                    name = name == "csinc" ? "cinc" : name == "csneg" ? "cneg" : "cinv"; return Join(D, N, cond);
                }
                return Join(D, N, M, cond);
            case Form.LongMultiply:
                if (a == 31)
                {
                    name = name switch { "smaddl" => "smull", "umaddl" => "umull", "smsubl" => "smnegl", _ => "umnegl" };
                    return Join(D, Reg(n, 32), Reg(m, 32));
                }
                return Join(D, Reg(n, 32), Reg(m, 32), A);
            case Form.Extract:
                if (n == m) { name = "ror"; return Join(D, N, I(shift)); }
                return Join(D, N, M, I(shift));
            case Form.VectorOr:
                string Bytes(int r) => "v" + r + "." + w / 8 + "b";
                if (n == m) { name = "mov"; return Join(Bytes(d), Bytes(n)); }
                return Join(Bytes(d), Bytes(n), Bytes(m));
            case Form.VectorImmediate:
                string vd = size == 64 && w == 64 ? Vec(d, w) : "v" + d + "." + w / size + (size switch { 8 => "b", 16 => "h", 32 => "s", _ => "d" });
                return Join(vd, U((ulong)imm) + (shift == 0 ? "" : ", lsl " + I(shift)));
            case Form.FloatImmediate:
                double number = w == 32 ? BitConverter.Int32BitsToSingle((int)imm) : BitConverter.Int64BitsToDouble(imm);
                return Join(Vec(d, w), "#" + number.ToString("F8", System.Globalization.CultureInfo.InvariantCulture));
            case Form.Convert:
                if (name is "fcvtzu" or "fcvtzs") return Join(D, Vec(n, size));
                return Join(Vec(d, w), name == "fcvt" ? Vec(n, size) : Reg(n, size));
            case Form.Multiply:
                if (a == 31) { name = name == "madd" ? "mul" : "mneg"; return Join(D, N, M); }
                return Join(D, N, M, A);
            case Form.Binary:
                if (name is "lslv" or "lsrv" or "asrv" or "rorv") name = name[..^1];
                return Join(D, N, M);
            case Form.Unary: return Join(D, N);
            case Form.Thread: return Join(D, "tpidr_el0");
            case Form.Memory:
            case Form.Pair:
            case Form.Literal:
                D = vec ? Vec(d, w) : D;
                if (form == Form.Literal) return Join(D, target);
                string address = "[" + Reg(n, 64, true);
                if (mode >= 4)
                {
                    int opt = mode - 4;
                    address += ", " + Reg(m, (opt & 3) == 3 ? 64 : 32);
                    if (opt != 3 || shift != 0) address += ", " + (opt == 3 ? "lsl" : extends[opt]) + (shift == 0 ? "" : " " + I(shift));
                }
                else if (mode != 1 && (imm != 0 || mode == 3)) address += ", " + I(imm);
                address += "]";
                if (mode == 1) address += ", " + I(imm);
                if (mode == 3) address += "!";
                return form == Form.Pair ? Join(D, vec ? Vec(a, w) : A, address) : Join(D, address);
            case Form.FloatBinary: return Join(Vec(d, w), Vec(n, w), Vec(m, w));
            case Form.FloatUnary: return Join(Vec(d, w), Vec(n, w));
            case Form.FloatCompare: return Join(Vec(n, w), mode == 0 ? Vec(m, w) : "#0.0");
            case Form.FloatMove: return mode == 0 ? Join(D, Vec(n, w)) : Join(Vec(d, w), N);
            case Form.FloatSelect: return Join(Vec(d, w), Vec(n, w), Vec(m, w), cond);
            case Form.Fused: return Join(Vec(d, w), Vec(n, w), Vec(m, w), Vec(a, w));
            default: throw new ArgumentOutOfRangeException(nameof(i));
        }
    }
}
