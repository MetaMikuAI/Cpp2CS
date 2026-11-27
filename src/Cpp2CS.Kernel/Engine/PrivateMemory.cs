using System.Collections.Immutable;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Kernel.Engine;

/// <summary>设计 7.10。地址由区域和字节偏移确定，写入和所有权随路径分开保存。</summary>
internal sealed record PrivateMemory(TermPool Terms, ImmutableArray<PrivateMemory.Area> Areas)
{
    internal enum Kind { Frame, Copy, Result }
    internal readonly record struct Part(int Area, long Offset, int Bits)
    {
        internal Int128 End => (Int128)Offset + Bits / 8;
        internal bool Overlaps(Part other) => Area == other.Area && Offset < other.End && other.Offset < End;
    }
    internal readonly record struct Word(int Bits, Term? Value, bool Handed = false, bool PartialResult = false);
    internal sealed record Area(Kind Kind, Term Base, int Bytes, Term? Initial)
    {
        internal ImmutableDictionary<long, Word> Words { get; init; } = ImmutableDictionary<long, Word>.Empty;
        internal bool UnknownInitial { get; init; }
    }

    internal static Term ArgumentValue(TermPool terms, int index, int bytes) =>
        terms.Attribute(new(KernelAttributes.ArgumentCopy), bytes * 8, terms.Constant(index, 32));

    internal static Term CallValue(TermPool terms, int bits, OccurrenceId id) =>
        terms.Attribute(new(KernelAttributes.IndirectCallResult), bits, terms.Constant(id.Block.Index, 32), terms.Constant(id.Index, 32));

    internal static PrivateMemory Create(TermPool terms, Term frame, ImmutableArray<Passing> passing, Passing? returned,
        Func<Slot, Term?> entry, Func<int, Term> initial)
    {
        var areas = ImmutableArray.CreateBuilder<Area>();
        areas.Add(new(Kind.Frame, frame, 0, null));
        for (int i = 0; i < passing.Length; i++)
            if (passing[i].Indirect > 0 && entry(passing[i].Pieces[0].Slot) is { } q)
                areas.Add(new(Kind.Copy, q, passing[i].Indirect, initial(i)));
        if (returned is { Indirect: > 0 } result && entry(result.Pieces[0].Slot) is { } r)
            areas.Add(new(Kind.Result, r, result.Indirect, null));
        return new(terms, areas.ToImmutable());
    }

    internal Kind? Mentions(Term value)
    {
        foreach (var area in Areas)
            if (EngineFacts.MentionsStack(value, area.Base)) return area.Kind;
        return null;
    }

    internal Part? Locate(Term address, int bits, out string reason)
    {
        reason = "";
        for (int i = 0; i < Areas.Length; i++)
        {
            var area = Areas[i];
            if (EngineFacts.FrameOffset(address, area.Base) is not long offset) continue;
            var part = new Part(i, offset, bits);
            if (part.End > (Int128)long.MaxValue + 1 || area.Kind != Kind.Frame && (offset < 0 || part.End > area.Bytes))
            {
                reason = "访问超出私有区域的大小";
                return null;
            }
            return part;
        }
        reason = Mentions(address) switch
        {
            Kind.Frame => $"地址由栈指针算出，但不是常量偏移：{address}",
            Kind.Copy => $"形参副本上的地址不是常量偏移：{address}",
            Kind.Result => $"结果位置上的地址不是常量偏移：{address}",
            _ => "",
        };
        return null;
    }

    internal string? RuntimeEscape(int count, CallOccurrence call, ImmutableArray<Term> operands)
    {
        if (Areas.Length == 1) return null;
        for (int i = 0; i < call.ArgumentSlots.Length; i++)
        {
            var slot = call.ArgumentSlots[i];
            if (slot.Kind == SlotKind.Integer && slot.Index < count && Mentions(operands[i + 1]) is Kind kind && kind != Kind.Frame)
                return Escape(kind, store: false);
        }
        return null;
    }

    internal static string Escape(Kind kind, bool store) => kind switch
    {
        Kind.Copy => store ? "形参副本地址被写进内存：形参副本逃逸" : "形参副本地址作为实参：形参副本逃逸",
        Kind.Result => store ? "结果位置地址被写进内存：结果位置逃逸" : "结果位置地址作为实参：结果位置逃逸",
        _ => store ? "帧地址被写入堆：帧对象逃逸" : "帧地址作为实参：帧对象逃逸",
    };

    /// <summary>普通读取须落在一次写入内。按成员取值与已暴露的帧对象可从多段已知内容拼起。</summary>
    internal Term? Read(Part part, bool assemble, out string reason)
    {
        var area = Areas[part.Area];
        var words = area.Words;
        reason = "";
        if (words.TryGetValue(part.Offset, out var exact) && exact.Bits >= part.Bits)
            return SliceWord(exact, 0, part.Bits, out reason);

        if (words.Any(p => p.Value.Handed && part.Overlaps(new(part.Area, p.Key, p.Value.Bits))))
        {
            reason = "读取已交给被调方的副本";
            return null;
        }
        Int128 cursor = part.Offset;
        var pieces = new List<Term>();
        foreach (var (at, word) in words.OrderBy(p => p.Key))
        {
            Int128 limit = (Int128)at + word.Bits / 8;
            if (cursor >= limit || at >= part.End) continue;
            if (!assemble && (at > part.Offset || limit < part.End))
            {
                reason = word.Handed ? "读取已交给被调方的副本" : "私有区域的读取与已有的写入部分重叠";
                return null;
            }
            if (at > cursor && !Initial(cursor, at))
            {
                reason = "私有区域的读取与已有的写入部分重叠";
                return null;
            }
            int bits = (int)((Int128.Min(limit, part.End) - cursor) * 8);
            var piece = SliceWord(word, (int)((cursor - at) * 8), bits, out reason);
            if (piece is null) return null;
            pieces.Add(piece);
            cursor += bits / 8;
        }
        if (cursor < part.End && !Initial(cursor, part.End))
        {
            if (pieces.Count > 0) reason = "私有区域的读取与已有的写入部分重叠";
            if (area.UnknownInitial) reason = "私有区域在各入边上的内容没有一致依据";
            return null;
        }
        return Terms.Concat(pieces);

        bool Initial(Int128 start, Int128 end)
        {
            if (area.Initial is null || area.UnknownInitial) return false;
            pieces.Add(Terms.Slice(area.Initial, (int)(start * 8), (int)((end - start) * 8)));
            cursor = end;
            return true;
        }
    }

    private Term? SliceWord(Word word, int offset, int bits, out string reason)
    {
        reason = word.Value != null ? "" : word.Handed ? "读取已交给被调方的副本" : "私有区域在各入边上的内容没有一致依据";
        return word.Value is { } value ? Terms.Slice(value, offset, bits) : null;
    }

    internal PrivateMemory Write(Part part, Term? value, bool handed = false, bool partialResult = false)
    {
        var area = Areas[part.Area];
        var updated = area.Words;
        foreach (var (at, old) in area.Words)
        {
            var previous = new Part(part.Area, at, old.Bits);
            if (!previous.Overlaps(part)) continue;
            updated = updated.Remove(at);
            void Keep(long start, int bit, int width)
            {
                updated = updated.SetItem(start, new(width, old.Value is { } v ? Terms.Slice(v, bit, width) : null, old.Handed, old.PartialResult));
            }
            if (at < part.Offset) Keep(at, 0, (int)(((Int128)part.Offset - at) * 8));
            if (part.End < previous.End) Keep((long)part.End, (int)((part.End - at) * 8), (int)((previous.End - part.End) * 8));
        }
        updated = updated.SetItem(part.Offset, new(part.Bits, value, handed, partialResult));
        return this with { Areas = Areas.SetItem(part.Area, area with { Words = updated }) };
    }

    internal Term? Aggregate(Part part, TypeShape type, string incomplete, out string reason)
    {
        reason = "值类型的成员未知";
        if (type.Members.IsDefaultOrEmpty || part.Bits != type.StorageBits) return null;
        var pieces = new List<Term>();
        int cursor = 0;
        foreach (var member in type.Members)
        {
            if (member.OffsetBits < 0 || member.Bits <= 0 || member.OffsetBits > part.Bits - member.Bits ||
                ((member.OffsetBits | member.Bits) & 7) != 0) return null;
            var range = new Part(part.Area, part.Offset + member.OffsetBits / 8, member.Bits);
            var value = Read(range, true, out string missing);
            if (value is null)
            {
                reason = missing == "读取已交给被调方的副本" ? missing : incomplete;
                return null;
            }
            if (cursor < member.OffsetBits) pieces.Add(Terms.Undefined(member.OffsetBits - cursor));
            int skip = Math.Max(0, cursor - member.OffsetBits);
            if (skip < value.Width) pieces.Add(Terms.Slice(value, skip, value.Width - skip));
            cursor = Math.Max(cursor, member.OffsetBits + value.Width);
        }
        if (cursor < part.Bits) pieces.Add(Terms.Undefined(part.Bits - cursor));
        reason = "";
        return Terms.Concat(pieces);
    }

    internal Term? Result(TypeShape type, out string reason)
    {
        for (int i = 0; i < Areas.Length; i++)
            if (Areas[i].Kind == Kind.Result) return Aggregate(new(i, 0, type.StorageBits), type, "结果位置没有写全", out reason);
        reason = "入口没有间接结果槽";
        return null;
    }

    internal sealed record Transfer(ImmutableArray<Part> Copies, Part? Result, ImmutableDictionary<int, Term> Arguments)
    {
        internal PrivateMemory Apply(PrivateMemory memory, Term? result)
        {
            foreach (var copy in Copies) memory = memory.Write(copy, null, handed: true);
            if (Result is not { } part) return memory;
            var area = memory.Areas[part.Area];
            return memory.Write(part, result!, partialResult: area.Kind == Kind.Result && part.Bits / 8 != area.Bytes);
        }
    }

    internal Transfer? Prepare(MethodShape shape, ImmutableArray<Passing> slots, Passing? returned, Func<Slot, Term?> argument, out string reason)
    {
        reason = "";
        var ranges = new List<(int Index, Part Part)>();
        Part? result = null;
        for (int i = 0; i <= slots.Length; i++)
        {
            bool output = i == slots.Length;
            if ((output ? returned : slots[i]) is not { Indirect: > 0 } passing) continue;
            if (argument(passing.Pieces[0].Slot) is not { } address)
            {
                reason = "调用没有给出经内存传递的地址槽";
                return null;
            }
            if (Locate(address, passing.Indirect * 8, out reason) is not { } part)
            {
                if (reason.Length == 0) reason = output ? "间接结果地址不在帧或结果位置" : "经内存传递的实参指向堆：尚未接入";
                else if (reason == "访问超出私有区域的大小") reason = "调用的传递区间超出私有区域的大小";
                return null;
            }
            if (output && Areas[part.Area].Kind == Kind.Copy)
            {
                reason = "间接结果地址不在帧或结果位置";
                return null;
            }
            if (output && Areas[part.Area] is { Kind: Kind.Result } area && part.Bits / 8 != area.Bytes &&
                area.Words.Any(w => w.Value.PartialResult && (w.Key < part.Offset || (Int128)w.Key + w.Value.Bits / 8 > part.End)))
            {
                reason = "结果位置的不同部分分别接收两次调用的返回值，规则未规定";
                return null;
            }
            if (ranges.Any(r => r.Part.Overlaps(part)))
            {
                reason = "一次调用的两段经内存传递的区域有重叠";
                return null;
            }
            if (output) result = part;
            else ranges.Add((i, part));
        }
        var arguments = ImmutableDictionary.CreateBuilder<int, Term>();
        foreach (var (index, part) in ranges)
        {
            var value = Aggregate(part, shape.Parameters[index], "经内存传递的实参有成员没有写全", out reason);
            if (value is null) return null;
            arguments.Add(index, value);
        }
        return new([.. ranges.Select(r => r.Part)], result, arguments.ToImmutable());
    }

    /// <summary>效果图只传播全部入边一致的写入；分歧和回边上的初始内容均不能作依据。</summary>
    internal PrivateMemory Merge(IReadOnlyList<PrivateMemory> incoming, bool loop)
    {
        if (!loop && incoming.Count == 0) return this;
        if (!loop && incoming.Count == 1) return incoming[0];
        var merged = this;
        for (int i = 0; i < Areas.Length; i++)
        {
            var first = loop ? Areas[i] : incoming[0].Areas[i];
            bool unknown = loop || incoming.Any(m => m.Areas[i].UnknownInitial);
            var area = first with { UnknownInitial = unknown };
            merged = merged with { Areas = merged.Areas.SetItem(i, area) };
            if (loop || incoming.All(m => ReferenceEquals(m.Areas[i].Words, first.Words))) continue;
            foreach (var (at, word) in incoming.SelectMany(m => m.Areas[i].Words).Distinct())
            {
                if (incoming.All(m => m.Areas[i].Words.TryGetValue(at, out var other) && word == other)) continue;
                merged = merged.Write(new(i, at, word.Bits), null);
            }
        }
        return merged;
    }
}
