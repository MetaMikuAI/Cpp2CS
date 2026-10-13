using Cpp2CS.Ir;
using Iced.Intel;

namespace Cpp2CS.X64;

public static partial class X64Lifter
{
    private sealed partial class Lifting
    {
        private LiftResult CompareImplicitStrings()
        {
            if (instruction.OpCount != 3 || !IsXmm(0) || !IsSimdSource(1, 128) || instruction.Op2Kind != OpKind.Immediate8)
                return Unsupported("PCMPISTRI 操作数未支持");
            int control = instruction.Immediate8, width = (control & 1) == 0 ? 8 : 16, count = 128 / width, mode = (control >> 2) & 3;
            bool signed = (control & 2) != 0;
            Value left = ReadXmm(0), right = ReadSimdSource(1, 128);
            List<Value> a = [], c = [], validA = [], validC = [];
            Value va = b.Const(1, 1), vc = va;
            for (int index = 0; index < count; index++)
            {
                a.Add(b.Extract(left, index * width, width));
                c.Add(b.Extract(right, index * width, width));
                va = b.And(va, b.BoolNot(b.Eq(a[index], b.Const(width, 0))));
                vc = b.And(vc, b.BoolNot(b.Eq(c[index], b.Const(width, 0))));
                validA.Add(va);
                validC.Add(vc);
            }
            List<Value> bits = [];
            for (int target = 0; target < count; target++)
            {
                Value result = b.Const(1, mode == 3 ? 1UL : 0UL);
                if (mode == 2)
                {
                    result = b.Select(validA[target], b.And(validC[target], b.Eq(a[target], c[target])), b.BoolNot(validC[target]));
                }
                else if (mode == 3)
                {
                    for (int index = 0; index < count - target; index++)
                    {
                        Value match = b.Or(b.BoolNot(validA[index]), b.And(validC[target + index], b.Eq(a[index], c[target + index])));
                        result = b.And(result, match);
                    }
                }
                else if (mode == 1)
                {
                    for (int index = 0; index < count; index += 2)
                    {
                        Value lower = b.BoolNot(signed ? b.Slt(c[target], a[index]) : b.Ult(c[target], a[index]));
                        Value upper = b.BoolNot(signed ? b.Slt(a[index + 1], c[target]) : b.Ult(a[index + 1], c[target]));
                        result = b.Or(result, b.And(b.And(validA[index], validA[index + 1]), b.And(lower, upper)));
                    }
                    result = b.And(result, validC[target]);
                }
                else
                {
                    for (int index = 0; index < count; index++) result = b.Or(result, b.And(validA[index], b.Eq(a[index], c[target])));
                    result = b.And(result, validC[target]);
                }
                if ((control & 16) != 0) result = b.Xor(result, (control & 32) == 0 ? b.Const(1, 1) : validC[target]);
                bits.Add(result);
            }
            Value mask = PackLanes(bits), found = b.BoolNot(b.Eq(mask, b.Const(count, 0))), selected = b.Const(32, (ulong)count);
            for (int step = 0; step < count; step++)
            {
                int index = (control & 64) == 0 ? count - 1 - step : step;
                selected = b.Select(bits[index], b.Const(32, (ulong)index), selected);
            }
            WriteRegister(Register.ECX, selected);
            b.Write("cf", found);
            b.Write("zf", b.BoolNot(validC[^1]));
            b.Write("sf", b.BoolNot(validA[^1]));
            b.Write("of", bits[0]);
            b.Write("af", b.Const(1, 0));
            b.Write("pf", b.Const(1, 0));
            return Next();
        }
    }
}
