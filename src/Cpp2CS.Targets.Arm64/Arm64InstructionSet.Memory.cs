using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using static Cpp2CS.Native.Terms.CoreOperation;
using static Cpp2CS.Targets.Arm64.Arm64Registers;

namespace Cpp2CS.Targets.Arm64;

public sealed partial class Arm64InstructionSet
{
    private sealed partial class Semantics
    {
        private bool BranchSystem()
        {
            if (Is(0x7c000000, 0x14000000))
            {
                if (Bit(31)) Link(new ImageFunction(Relative(0, 26)));
                else e.Jump(Relative(0, 26));
                return true;
            }
            if (Is(0xff000010, 0x54000000))
            {
                if (B(0, 4) >= 14) e.Jump(Relative(5, 19));
                else e.Branch(Condition(B(0, 4)), Relative(5, 19), pc + 4);
                return true;
            }
            if (Is(0x7e000000, 0x34000000))
            { e.Branch(Compare(Bit(24) ? NotEqual : Equal, ReadX(D, Width), K(0, Width)), Relative(5, 19), pc + 4); return true; }
            if (Is(0x7e000000, 0x36000000))
            {
                var bit = T.Slice(ReadX(D, 64), (B(31) << 5) | B(19, 5), 1);
                e.Branch(Bit(24) ? bit : Unary(Not, bit), Relative(5, 14), pc + 4); return true;
            }
            if (Is(0xfffffc1f, 0xd61f0000)) { e.IndirectJump(ReadX(A, 64)); return true; }
            if (Is(0xfffffc1f, 0xd63f0000)) { Link(new ComputedTarget(ReadX(A, 64))); return true; }
            if (Is(0xfffffc1f, 0xd65f0000))
            {
                if (A == 30) e.Return();
                else e.IndirectJump(ReadX(A, 64));
                return true;
            }
            if (Is(0xffe0001f, 0xd4200000) || Is(0xffe0001f, 0xd4400000)) { e.Trap(); return true; }
            if (Is(0xfffff01f, 0xd503201f)) return true;
            if (Is(0xffffffe0, 0xd53bd040)) { WriteX(D, e.ThreadPointer); return true; }
            if (Is(0xfffff0ff, 0xd503305f)) { Hole("exclusive"); return true; }
            if (Is(0xfffff09f, 0xd503309f)) { Hole("barrier"); return true; }
            if (Is(0xffc00000, 0xd5000000)) { Hole("system-register"); return true; }
            if (Is(0xfe000000, 0xd6000000)) { Hole("branch-extension"); return true; }
            if (Is(0xff000000, 0xd4000000)) { Hole("system-trap"); return true; }
            return false;
        }
        private void Link(CallTarget target)
        {
            // Call 消去物理调用；返回地址不能在 Call 之后写，以兼容不返回调用。
            WriteX(30, e.ImageAddress(pc + 4));
            e.Call(target);
        }
        private Term Address(Term basis, long offset) => offset == 0 ? basis : Op(Add, basis, K(offset));
        private bool Memory()
        {
            if (Is(0x3f000000, 0x08000000)) { Hole("exclusive"); return true; }
            if (Is(0x3b200c00, 0x38200000)) { Hole("atomic"); return true; }
            if (Is(0x3b000000, 0x18000000))
            {
                int opc = B(30, 2); bool vector = Bit(26);
                if (opc == 3) { if (vector) Hole(); return true; }
                Access(vector, true, vector ? 32 << opc : opc == 1 ? 64 : 32, !vector && opc == 2, 64, D, e.ImageAddress(Relative(5, 19)));
                return true;
            }
            if (Is(0x3a000000, 0x28000000)) { Pair(); return true; }
            bool unsigned = Is(0x3b000000, 0x39000000), immediate = Is(0x3b200000, 0x38000000), register = Is(0x3b200c00, 0x38200800);
            if (!unsigned && !immediate && !register) return false;
            int size = B(30, 2), opcSingle = B(22, 2), mode = B(10, 2);
            bool vec = Bit(26), prefetch = !vec && size == 3 && opcSingle == 2;
            if ((vec && opcSingle >= 2 && size != 0) || (!vec && opcSingle == 3 && size >= 2)) { Hole(); return true; }
            if (prefetch && immediate && mode is 1 or 3) { Hole(); return true; }
            int bits = vec && opcSingle >= 2 ? 128 : 8 << size;
            var basis = ReadX(A, 64, true); Term address; Term? writeback = null;
            if (unsigned) address = Address(basis, (long)B(10, 12) * bits / 8);
            else if (immediate)
            {
                var updated = Address(basis, Signed(B(12, 9), 9));
                address = mode == 1 ? basis : updated;
                if (mode is 1 or 3) writeback = updated;
                if (vec && mode == 2) { Hole(); return true; }
            }
            else
            {
                int option = B(13, 3);
                if (option is not (2 or 3 or 6 or 7)) { Hole(); return true; }
                var index = Extend(ReadX(M, (option & 1) == 0 ? 32 : 64), 64, option >= 6);
                address = Op(Add, basis, Shift(index, 0, Bit(12) ? System.Numerics.BitOperations.Log2((uint)(bits / 8)) : 0));
            }
            if (prefetch) return true;
            if (writeback is not null && !vec && A != 31 && A == D) { Hole("constrained-unpredictable"); return true; }
            Access(vec, vec ? (opcSingle & 1) != 0 : opcSingle != 0, bits, !vec && opcSingle >= 2, opcSingle == 3 ? 32 : 64, D, address);
            if (writeback is not null) WriteX(A, writeback, true);
            return true;
        }
        private void Access(bool vector, bool load, int bits, bool signed, int signedWidth, int rt, Term address)
        {
            if (load)
            {
                var value = e.Load(address, bits);
                if (vector) WriteV(rt, value);
                else WriteX(rt, Extend(value, signed ? signedWidth : Math.Max(32, bits), signed));
            }
            else e.Store(address, vector ? T.Slice(e.Read(V[rt]), 0, bits) : ReadX(rt, bits));
        }
        private void Pair()
        {
            int opc = B(30, 2), mode = B(23, 2), rt2 = B(10, 5);
            bool vector = Bit(26), load = Bit(22), signed = !vector && opc == 1;
            if (opc == 3 || (!vector && opc == 1 && (!load || mode == 0))) { Hole(); return; }
            if (load && D == rt2) { Hole("constrained-unpredictable"); return; }
            bool writeback = mode is 1 or 3;
            if (!vector && writeback && A != 31 && (A == D || A == rt2)) { Hole("constrained-unpredictable"); return; }
            int bits = vector ? 32 << opc : opc == 2 ? 64 : 32;
            var basis = ReadX(A, 64, true);
            var updated = Address(basis, Signed(B(15, 7), 7) * bits / 8);
            var address = mode == 1 ? basis : updated;
            Access(vector, load, bits, signed, 64, D, address);
            Access(vector, load, bits, signed, 64, rt2, Address(address, bits / 8));
            if (writeback) WriteX(A, updated, true);
        }
    }
}
