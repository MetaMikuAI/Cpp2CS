using System.Globalization;

namespace Cpp2CS.Target;

public static partial class AssemblyText
{
    static string FormatExtension(Instruction i)
    {
        var (form, name, w, d, n, m, a, imm, mode, shift, size, immediate) = i;
        string S(int bits) => bits switch { 8 => "b", 16 => "h", 32 => "s", 64 => "d", _ => throw new ArgumentOutOfRangeException(nameof(bits)) };
        string V(int reg, int width, int element) => $"v{reg}.{width / element}{S(element)}";
        string Operand(int reg) => w == size ? Vec(reg, size) : V(reg, w, size);
        string Lane(int reg, int index) => $"v{reg}.{S(size)}[{index}]";
        string operands = form switch
        {
            Form.ConditionalCompare => $"{Reg(n, w)}, {(immediate ? "#" + m : Reg(m, w))}, #{imm}, {conditions[mode]}",
            Form.FloatConditionalCompare => $"{Vec(n, w)}, {Vec(m, w)}, #{imm}, {conditions[mode]}",
            Form.Reverse => $"{Reg(d, w)}, {Reg(n, w)}",
            Form.RoundConvert => $"{Reg(d, w)}, {Vec(n, size)}" + (shift == 0 ? "" : $", #{shift}"),
            Form.SimdBits or Form.SimdBinary => $"{Operand(d)}, {Operand(n)}, {Operand(m)}",
            Form.SimdIndexed => $"{Operand(d)}, {Operand(n)}, {Lane(m, shift)}",
            Form.SimdUnary => $"{Operand(d)}, {Operand(n)}" + (name.StartsWith("fcm") ? ", #0.0" : ""),
            Form.SimdCopy => mode switch
            {
                0 => $"{Operand(d)}, {Reg(n, Math.Max(32, size))}", 1 => $"{Operand(d)}, {Lane(n, shift)}",
                2 => $"{Vec(d, size)}, {Lane(n, shift)}", 3 => $"{Lane(d, shift)}, {Reg(n, Math.Max(32, size))}",
                4 => $"{Lane(d, shift)}, {Lane(n, a)}", _ => $"{Reg(d, w)}, {Lane(n, shift)}"
            },
            Form.SimdPermute => $"{Operand(d)}, {Operand(n)}, {Operand(m)}" + (name == "ext" ? $", #{shift}" : ""),
            Form.SimdNarrow => $"{V(d, w, size)}, {V(n, 128, 2 * size)}",
            Form.SimdWiden => $"{V(d, 128, 2 * size)}, {V(n, 64 << mode, size)}" + (name.StartsWith("fcvt") ? "" : $", #{shift}"),
            Form.SimdReduce => $"{Vec(d, name == "uaddlv" ? 2 * size : size)}, {V(n, w, size)}",
            Form.SimdShift => $"{Operand(d)}, {Operand(n)}, #{shift}",
            Form.SimdImmediate => $"{Operand(d)}, #{imm}" + (shift == 0 ? "" : $", {(mode == 1 ? "msl" : "lsl")} #{shift}"),
            Form.SimdFloatImmediate => $"{Operand(d)}, #" + (size == 32 ? BitConverter.Int32BitsToSingle((int)imm) : BitConverter.Int64BitsToDouble(imm)).ToString("F8", CultureInfo.InvariantCulture),
            Form.SimdTransfer => (name switch
            {
                "ld1r" => "{" + V(d, w, size) + "}",
                "st2" => "{" + V(d, w, size) + ", " + V((d + 1) % 32, w, size) + "}",
                _ => $"{{v{d}.{S(size)}}}[{shift}]"
            }) + $", [{Reg(n, 64, true)}]" + (mode == 0 ? "" : ", " + (m == 31 ? "#" + size / 8 : Reg(m, 64))),
            _ => throw new ArgumentOutOfRangeException(nameof(i))
        };
        return name + " " + operands;
    }
}
