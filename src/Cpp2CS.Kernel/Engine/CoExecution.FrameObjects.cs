using System.Collections.Immutable;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;

namespace Cpp2CS.Kernel.Engine;

public sealed partial class CoExecution
{
    private static (Term Object, int Bit)? ObjectPart(State state, Term address, int bits)
    {
        if (state.Objects.IsEmpty) return null;
        Term root = address;
        long offset = 0;
        if (address is { Kind: TermKind.Operation, Op: Op.Add } && address.Operands[1].IsConstant)
        {
            root = address.Operands[0];
            offset = unchecked((long)(ulong)address.Operands[1].Value);
        }
        if (!state.Objects.TryGetValue(root, out var whole))
        {
            if (ContainsObject(address)) throw new Refuted(Verdict.MissingFact, "帧对象上的地址不是常量偏移");
            return null;
        }
        if (offset < 0 || (Int128)offset * 8 + bits > whole.Width)
            throw new Refuted(Verdict.MissingFact, "访问超出帧对象的存储区间");
        return (root, (int)(offset * 8));
    }

    private static bool ContainsObject(Term term)
    {
        if (term.Operands.IsEmpty) return false;
        var seen = new HashSet<Term>(ReferenceEqualityComparer.Instance);
        bool Visit(Term t) => t is { Kind: TermKind.Attribute, Attribute.Value: KernelAttributes.FrameAddress }
            || !t.Operands.IsEmpty && seen.Add(t) && t.Operands.Any(Visit);
        return Visit(term);
    }

    private void WriteObject(ref State state, (Term Object, int Bit) part, Term value)
    {
        var old = state.Objects[part.Object];
        var pieces = new List<Term>(3);
        if (part.Bit > 0) pieces.Add(terms.Slice(old, 0, part.Bit));
        pieces.Add(value);
        int end = part.Bit + value.Width;
        if (end < old.Width) pieces.Add(terms.Slice(old, end, old.Width - end));
        state = state with { Objects = state.Objects.SetItem(part.Object, terms.Concat(pieces)) };
    }

    private static void RequirePointee(Term atom, TypeShape parameter)
    {
        if (parameter.Kind != StackKind.ByRef || parameter.Entity == default || parameter.Entity != atom.Operands[3].Entity)
            throw new Refuted(Verdict.MissingFact, "帧对象的类型与形参所指的类型没有对应");
    }

    /// <summary>同一次不展开的调用、同一个托管指针实参，给出两个帧对象的对应（设计 18.1）。</summary>
    private bool BindObject(ref State state, Term given, Term expected, TypeShape parameter)
    {
        if (!state.Objects.TryGetValue(expected, out var value)) return false;
        RequirePointee(expected, parameter);
        if (state.Exposed.TryGetValue(expected, out var bound))
        {
            if (given != bound) throw new Refuted(Verdict.Insufficient, "同一帧对象再次交给调用时地址不同");
            return true;
        }
        if (leftTemplate is null)
        {
            if (FrameOffset(given, stackPointer) is null)
                throw new Refuted(Verdict.Insufficient, "模板的帧地址没有对应入口栈指针的常量偏移");
            foreach (var (other, address) in state.Exposed)
                if (!Disjoint(given, value.Width, address, state.Objects[other].Width))
                    throw new Refuted(Verdict.Insufficient, "两个帧对象对应的原生区间重叠");
        }
        else if (!state.Objects.TryGetValue(given, out var left) || left.Width != value.Width
            || given.Operands[3].Entity != parameter.Entity || state.Exposed.ContainsValue(given))
            throw new Refuted(Verdict.Insufficient, "两侧帧对象的大小或地址对应关系不同");
        state = state with { Exposed = state.Exposed.Add(expected, given) };
        return true;
    }

    private Term ReadInterval(ImmutableDictionary<long, Term> frame, long start, int bits)
    {
        var parts = new List<Term>();
        Int128 cursor = start, end = cursor + bits / 8;
        foreach (var (at, value) in frame.OrderBy(p => p.Key))
        {
            Int128 limit = Int128.Min((Int128)at + value.Width / 8, end);
            if (limit <= cursor) continue;
            if (at > cursor) break;
            parts.Add(terms.Slice(value, (int)((cursor - at) * 8), (int)((limit - cursor) * 8)));
            cursor = limit;
            if (cursor == end) return terms.Concat(parts);
        }
        throw new Refuted(Verdict.MissingFact, $"帧上偏移 {start} 处的 {bits} 位内容没有完整的写入依据");
    }

    private ImmutableDictionary<long, Term> WriteInterval(ImmutableDictionary<long, Term> frame, long start, Term value)
    {
        Int128 end = (Int128)start + value.Width / 8;
        var updated = frame;
        foreach (var (at, old) in frame)
        {
            Int128 limit = (Int128)at + old.Width / 8;
            if (limit <= start || end <= at) continue;
            updated = updated.Remove(at);
            if (at < start) updated = updated.SetItem(at, terms.Slice(old, 0, (int)((start - (Int128)at) * 8)));
            if (end < limit)
            {
                if (end > long.MaxValue) throw new Refuted(Verdict.MissingFact, "帧区间的末端超出偏移范围");
                updated = updated.SetItem((long)end, terms.Slice(old, (int)((end - at) * 8), (int)((limit - end) * 8)));
            }
        }
        return updated.SetItem(start, value);
    }

    /// <summary>在观察点比较全部已暴露对象。每个对象在事件之后有一个双方共用的新内容。</summary>
    private void ObserveObjects(ref State state)
    {
        if (state.Exposed.IsEmpty) return;
        int serial = state.Serial;
        foreach (var (atom, given) in state.Exposed)
        {
            var expected = state.Objects[atom];
            long offset = leftTemplate is null ? FrameOffset(given, stackPointer)!.Value : 0;
            var actual = leftTemplate is null ? ReadInterval(state.Frame, offset, expected.Width) : state.Objects[given];
            if (!state.Conditions.Same(actual, expected))
                throw new Refuted(Verdict.Insufficient, $"已暴露帧对象的内容不同：现场 {actual}，模板 {expected}");
            var fresh = terms.Attribute(new AttributeId(KernelAttributes.ExposedContent), expected.Width,
                terms.Constant(serial, 32), atom.Operands[0], atom.Operands[1], atom.Operands[2]);
            var objects = state.Objects.SetItem(atom, fresh);
            state = leftTemplate is null ? state with { Objects = objects, Frame = WriteInterval(state.Frame, offset, fresh) }
                : state with { Objects = objects.SetItem(given, fresh) };
        }
    }
}
