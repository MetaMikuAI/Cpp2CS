using System.Buffers.Binary;
using System.Collections.Immutable;
using Cpp2CS.Spec.IL;

namespace Cpp2CS.Kernel.Forward;

/// <summary>
/// 一条解码后的指令。Operand：立即数、变量序号、元数据记号，或转移目标的绝对偏移；短形式里隐含的操作数已经填入。
/// Targets：跳转表各项的绝对偏移。
/// </summary>
public sealed record Instruction(int Offset, int Size, OpcodeInfo Opcode, long Operand, ImmutableArray<int> Targets)
{
    public int Next => Offset + Size;
    public override string ToString() => $"IL_{Offset:x4} {Opcode.Name}";
}

/// <summary>IL 字节流的解码，按 ECMA-335 III.1.2 的指令编码。</summary>
public static class IlDecoder
{
    public static ImmutableArray<Instruction> Decode(ReadOnlySpan<byte> code)
    {
        var result = ImmutableArray.CreateBuilder<Instruction>();
        int at = 0;
        while (at < code.Length)
        {
            int start = at;
            ushort value = code[at++];
            if (value == 0xFE)
            {
                if (at >= code.Length) throw new ExpansionException("IL 无法解码", $"偏移 {start:x4} 处的双字节指令不完整", start);
                value = (ushort)(0xFE00 | code[at++]);
            }
            var opcode = Opcodes.Find(value) ?? throw new ExpansionException("IL 无法解码", $"偏移 {start:x4} 处的编码 {value:x} 不是指令", start);
            long length = opcode.Operand switch
            {
                OperandKind.None => 0,
                OperandKind.Int8 or OperandKind.Variable8 or OperandKind.Branch8 => 1,
                OperandKind.Variable16 => 2,
                OperandKind.Int64 or OperandKind.Float64 => 8,
                // 表长是无符号 32 位的项数 N，其后 N 个 4 字节目标（ECMA-335 III.3.66）；按 64 位计算，超出剩余字节就是不完整。
                OperandKind.Switch => at + 4 <= code.Length ? (long)4 + 4L * BinaryPrimitives.ReadUInt32LittleEndian(code[at..]) : 4,
                _ => 4,
            };
            if (length > code.Length - at)
                throw new ExpansionException("IL 无法解码", $"偏移 {start:x4} 处的 {opcode.Name} 操作数不完整", start);
            var bytes = code.Slice(at, (int)length);
            at += (int)length;
            long operand = opcode.Implied ?? 0;
            ImmutableArray<int> targets = [];
            switch (opcode.Operand)
            {
                case OperandKind.Int8: operand = (sbyte)bytes[0]; break;
                case OperandKind.Variable8: operand = bytes[0]; break;
                case OperandKind.Variable16: operand = BinaryPrimitives.ReadUInt16LittleEndian(bytes); break;
                case OperandKind.Branch8: operand = at + (sbyte)bytes[0]; break;
                case OperandKind.Branch32: operand = at + BinaryPrimitives.ReadInt32LittleEndian(bytes); break;
                case OperandKind.Int64 or OperandKind.Float64: operand = BinaryPrimitives.ReadInt64LittleEndian(bytes); break;
                case OperandKind.Switch:
                {
                    var table = ImmutableArray.CreateBuilder<int>(bytes.Length / 4 - 1);
                    for (int i = 4; i < bytes.Length; i += 4) table.Add(at + BinaryPrimitives.ReadInt32LittleEndian(bytes[i..]));
                    targets = table.MoveToImmutable();
                    break;
                }
                case OperandKind.None: break;
                default: operand = BinaryPrimitives.ReadInt32LittleEndian(bytes); break;
            }
            result.Add(new Instruction(start, at - start, opcode, operand, targets));
        }
        return result.ToImmutable();
    }
}
