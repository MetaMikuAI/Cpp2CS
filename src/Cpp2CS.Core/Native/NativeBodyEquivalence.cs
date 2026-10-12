using System.Text.Json;

namespace Cpp2CS.Native;

// 编译器可能复制共享泛型函数。只有完整指令和异常区域一致才接受另一入口的签名。
public sealed class NativeBodyEquivalence(ElfImage image, Arm64Decoder decoder)
{
    private readonly Dictionary<(ulong, ulong), bool> cache = [];
    public bool Equivalent(ulong left, ulong right)
    {
        if (left == right) return true;
        if (cache.TryGetValue((left, right), out var found)) return found;
        var a = UnwindBoundary.Read(image, left); var b = UnwindBoundary.Read(image, right);
        var size = a.End - a.Start;
        if (a.Unsupported is not null || b.Unsupported is not null || a.PersonalitySlot != b.PersonalitySlot ||
            a.Start != left || b.Start != right || size == 0 || size > 16384 || size != b.End - b.Start) return cache[(left, right)] = false;
        string Normalize(ulong start, UnwindBoundary boundary)
        {
            long Immediate(Instruction i, Operand operand) => operand.Kind == 2 && (i.Mnemonic is "b" or "bl" or "adr" || NativeGraph.IsConditional(i)) &&
                (ulong)operand.Immediate >= start && (ulong)operand.Immediate < start + size ? operand.Immediate - (long)start : operand.Immediate;
            return JsonSerializer.Serialize(new
            {
                instructions = decoder.Decode(image.Read(start, (int)size), start).Select(i => new { i.Mnemonic, i.Writeback, i.PostIndex,
                    operands = i.Operands.Select(o => new { o.Kind, o.Register, immediate = Immediate(i, o), o.Base, o.Index, o.Displacement, o.Extend, o.Shift, o.ShiftKind }) }),
                regions = boundary.ExceptionRegions.Select(r => new { start = r.Start - start, end = r.End - start, pad = r.LandingPad - start,
                    actions = r.Actions.Select(a => new { a.Filter, a.Kind, a.TypeInfo }) })
            });
        }
        return cache[(left, right)] = Normalize(left, a) == Normalize(right, b);
    }
}
