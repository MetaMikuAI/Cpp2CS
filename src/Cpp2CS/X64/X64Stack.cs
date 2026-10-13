using Cpp2CS.Ir;
using Iced.Intel;

namespace Cpp2CS.X64;

public static partial class X64Lifter
{
    private sealed partial class Lifting
    {
        private void CheckStackAddress(Value address, int bytes)
        {
            Value last = b.Add(address, b.Const(64, (ulong)(bytes - 1)));
            Value firstCanonical = b.Eq(address, b.Sext(b.Trunc(address, 48), 64));
            Value lastCanonical = b.Eq(last, b.Sext(b.Trunc(last, 48), 64));
            b.Guard(b.And(b.And(firstCanonical, lastCanonical), b.BoolNot(b.Ult(last, address))),
                "noncanonical or wrapping ENTER stack address; fault priority, rollback and delivery are unmodeled");
        }

        private LiftResult Enter()
        {
            if (instruction.Code is not (Code.Enterw_imm16_imm8 or Code.Enterq_imm16_imm8) ||
                instruction.OpCount != 2 || instruction.Op0Kind != OpKind.Immediate16 || instruction.Op1Kind != OpKind.Immediate8_2nd)
                return Unsupported("ENTER 仅支持 64 位模式下的 16/64 位帧指针");
            int width = instruction.Code == Code.Enterw_imm16_imm8 ? 16 : 64;
            int bytes = width / 8, nesting = (int)instruction.GetImmediate(1) & 31;
            Value size = b.Const(64, (ulong)bytes);
            Value oldBase = b.Read("rbp", 64), stack = b.Sub(b.Read("rsp", 64), size);
            CheckStackAddress(stack, bytes);
            b.Store(stack, b.Trunc(oldBase, width));
            Value frame = stack, source = oldBase;
            for (int i = 1; i < nesting; i++)
            {
                source = b.Sub(source, size);
                CheckStackAddress(source, bytes);
                Value value = b.Load(source, width);
                stack = b.Sub(stack, size);
                CheckStackAddress(stack, bytes);
                b.Store(stack, value);
            }
            if (nesting != 0)
            {
                stack = b.Sub(stack, size);
                CheckStackAddress(stack, bytes);
                b.Store(stack, b.Trunc(frame, width));
            }
            Value allocated = b.Sub(stack, b.Const(64, instruction.GetImmediate(0)));
            CheckStackAddress(allocated, 1);
            b.WriteProbe(allocated, 1);
            b.Write("rbp", width == 64 ? frame : b.Concat(b.Extract(oldBase, 16, 48), b.Trunc(frame, 16)));
            b.Write("rsp", allocated);
            b.MarkNormalPathOnly("ENTER preserves ordered overlapping frame accesses and final write probe; fault rollback and partial register state are unmodeled");
            return Next();
        }
    }
}
