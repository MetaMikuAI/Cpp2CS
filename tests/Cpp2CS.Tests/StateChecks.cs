using System.Collections.Immutable;
using System.Diagnostics;
using System.Numerics;
using Cpp2CS.Kernel.State;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Tests;

internal static class StateChecks
{
    public const string Command = "state";
    internal sealed class Fixture
    {
        public TermTable Terms { get; } = new();
        public BlockIdentity Entry { get; } = new();
        public Term Frame { get; }
        public FunctionBuilder Builder { get; }
        public Fixture() { Frame = Terms.Atom(new RootAtom(AddressRoot.Frame), 64); Builder = new(Terms, Entry, 64, new(Frame)); }
        public Term C(ulong n, int width = 64) => Terms.Constant(n, width);
        public Term At(long offset) => Terms.Apply(new CoreOperator(CoreOperation.Add), 64, Frame, Terms.Constant((new BigInteger(offset) + (BigInteger.One << 64)) % (BigInteger.One << 64), 64));
        public MemoryWrite Write(long offset, Term value) => new(new(), At(offset), value.Width, value);
        public MemoryRead Read(long offset, int width = 64) { var id = new ReadIdentity(); return new(id, At(offset), width, Terms.Atom(new ResultAtom(id), width)); }
        public NativeFunction Finish(params Statement[] statements) { Builder.Blocks.Add(new(Entry, [], [.. statements], new Return([]))); return Builder.Freeze(); }
    }
    private static T Good<T>(Outcome<T> result) => result.IsSuccess ? result.Value : throw new InvalidOperationException(result.Why?.ToString());
    public static int Run()
    {
        var a = new Assertions(); Alias(a); Forward(a); Branches(a); Calls(a); Caller(a); Scale();
        return a.Finish("状态模型");
    }
    private static void Alias(Assertions a)
    {
        var f = new Fixture(); var q = new StateQueries(); var c = q.CreateContext(f.Finish());
        Location L(Term t, int width = 64) => Good(c.Get(q.Locations, new(t, width)));
        AliasKind A(Location x, Location y) => Good(c.Get(q.Alias, new(x, y))).Kind;
        var frame = L(f.Frame); var image = L(f.Terms.Atom(new RootAtom(AddressRoot.Image), 64));
        var thread = L(f.Terms.Atom(new RootAtom(AddressRoot.Thread), 64)); var other = L(f.Terms.Atom(new EntryAtom(new(SlotKind.Integer)), 64));
        a.True(A(frame, image) == AliasKind.Disjoint && A(frame, thread) == AliasKind.Disjoint && A(image, thread) == AliasKind.Disjoint, "三个区域互不相交");
        a.True(A(image, image) == AliasKind.Overlap, "同区域不是必然不交");
        var overlap = Good(c.Get(q.Alias, new(frame, L(f.At(4)))));
        a.True(overlap == new Overlap(AliasKind.Overlap, 32, 0, 32), "按位重叠");
        a.True(A(frame, L(f.At(8))) == AliasKind.Disjoint, "相邻区间不重叠");
        a.True(A(frame, other) == AliasKind.Disjoint && A(other, frame) == AliasKind.Disjoint, "未逃逸帧与其他根不交");
        var escaped = new Fixture(); var qc = new StateQueries(); var ec = qc.CreateContext(escaped.Finish(new Call(new(), new ImageFunction(1), [new(new(SlotKind.Integer), escaped.Frame)], [])));
        var el = Good(ec.Get(qc.Locations, new(escaped.Frame, 64))); var eo = Good(ec.Get(qc.Locations, new(escaped.C(42), 64)));
        a.True(Good(ec.Get(qc.Alias, new(el, eo))).Kind == AliasKind.Unknown, "逃逸帧与其他根不能判定");
        a.True(A(other, L(f.C(12))) == AliasKind.Unknown && A(other, other) == AliasKind.Overlap, "不同项根未知，同项根可判定");
        var dynamic = L(f.Terms.Apply(new CoreOperator(CoreOperation.Add), 64, f.Frame, other.Root));
        a.True(dynamic.Offset is null && A(dynamic, frame) == AliasKind.Unknown, "非常量偏移不能判定");
        a.True(L(f.At(-8)).Offset == -8 && A(L(f.At(-8)), frame) == AliasKind.Disjoint, "负偏移按有符号区间");
        var another = L(f.Terms.Apply(new CoreOperator(CoreOperation.Add), 64, f.Frame,
            f.Terms.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64)));
        a.True(dynamic != another, "不同的未知偏移保留地址身份");
        a.True(!c.Get(q.Locations, new(f.Terms.Undefined(64), 64)).IsSuccess, "未定义地址分解失败带原因");
    }
    private static void Forward(Assertions a)
    {
        var f = new Fixture(); var r = f.Read(0); var narrow = f.Read(2, 16); var wide = f.Read(16, 32); var undef = f.Read(24);
        var q = new StateQueries(); var c = q.CreateContext(f.Finish(f.Write(0, f.C(0x12345678)), r, narrow,
            f.Write(16, f.C(0x5678, 16)), f.Write(18, f.C(0x1234, 16)), wide, f.Write(24, f.Terms.Undefined(64)), new Call(new(), new ImageFunction(1), [], []), undef));
        a.True(Good(c.Get(q.Read, r.Identity)) == f.C(0x12345678), "完整写后读");
        a.True(Good(c.Get(q.Read, narrow.Identity)) == f.C(0x1234, 16), "宽写窄读");
        a.True(Good(c.Get(q.Read, wide.Identity)) == f.C(0x12345678, 32), "窄写拼接");
        a.True(Good(c.Get(q.Read, undef.Identity)) == f.Terms.Undefined(64), "未定义位照样转发");
        var unknown = new Fixture(); var first = unknown.Read(0); var second = unknown.Read(0);
        var uq = new StateQueries(); var uc = uq.CreateContext(unknown.Finish(first, second));
        a.True(Good(uc.Get(uq.Read, first.Identity)) == Good(uc.Get(uq.Read, second.Identity)), "入口读取身份复用");
    }
    private static void Branches(Assertions a)
    {
        foreach (var same in new[] { true, false })
        {
            var f = new Fixture(); var left = new BlockIdentity(); var right = new BlockIdentity(); var end = new BlockIdentity(); var r = f.Read(0);
            f.Builder.Blocks.Add(new(f.Entry, [], [], new Branch(f.C(1, 1), left, right)));
            f.Builder.Blocks.Add(new(left, [], [f.Write(0, f.C(7))], new Jump(end)));
            f.Builder.Blocks.Add(new(right, [], [f.Write(0, f.C(same ? 7UL : 8UL))], new Jump(end)));
            f.Builder.Blocks.Add(new(end, [], [r], new Return([])));
            var q = new StateQueries(); var c = q.CreateContext(f.Builder.Freeze()); var value = Good(c.Get(q.Read, r.Identity));
            if (same) a.True(value == f.C(7), "两臂同值不合流");
            else
            {
                a.True(value.Identity is MemoryMerge, "两臂异值合流");
                var inputs = Good(c.Get(q.MergeInputs, (MemoryMerge)value.Identity!));
                a.True(inputs.Single(i => i.Predecessor == left).Value == f.C(7) && inputs.Single(i => i.Predecessor == right).Value == f.C(8), "查询合流的前驱值");
            }
        }
        var loop = new Fixture(); var body = new BlockIdentity(); var exit = new BlockIdentity(); var read = loop.Read(0);
        loop.Builder.Blocks.Add(new(loop.Entry, [], [loop.Write(0, loop.C(0))], new Jump(body)));
        var increment = loop.Terms.Apply(new CoreOperator(CoreOperation.Add), 64, read.Result, loop.C(1));
        loop.Builder.Blocks.Add(new(body, [], [read, loop.Write(0, increment)], new Branch(loop.C(1, 1), body, exit)));
        loop.Builder.Blocks.Add(new(exit, [], [], new Return([])));
        var queries = new StateQueries(); var context = queries.CreateContext(loop.Builder.Freeze());
        var merged = Good(context.Get(queries.Read, read.Identity));
        a.True(merged.Identity is MemoryMerge, "循环计数器合流");
        var incoming = Good(context.Get(queries.MergeInputs, (MemoryMerge)merged.Identity!));
        a.True(incoming.Single(i => i.Predecessor == body).Value == loop.Terms.Apply(new CoreOperator(CoreOperation.Add), 64, merged, loop.C(1)), "回边用稳定合流原子");
        var limited = new StateQueries(stepLimit: 1); var failure = limited.CreateContext(loop.Builder.Freeze()).Get(limited.Read, read.Identity);
        a.True(!failure.IsSuccess && failure.Why is not null, "迭代预算耗尽带原因");
        var pass = new Fixture(); var repeat = new BlockIdentity(); var pr = pass.Read(0);
        pass.Builder.Blocks.Add(new(pass.Entry, [], [pass.Write(0, pass.C(9))], new Jump(repeat)));
        pass.Builder.Blocks.Add(new(repeat, [], [pr, pass.Write(0, pr.Result)], new Jump(repeat)));
        var pq = new StateQueries(); a.True(Good(pq.CreateContext(pass.Builder.Freeze()).Get(pq.Read, pr.Identity)) == pass.C(9), "自身以外同定义不合流");
    }
    private static void Calls(Assertions a)
    {
        foreach (var escaped in new[] { false, true })
        {
            var f = new Fixture(); var r = f.Read(0); var q = new StateQueries();
            var call = new Call(new(), new ImageFunction(1), escaped ? [new(new(SlotKind.Integer), f.Frame)] : [], []);
            var c = q.CreateContext(f.Finish(f.Write(0, f.C(7)), call, r));
            var value = Good(c.Get(q.Read, r.Identity));
            a.True(escaped ? value.Identity is MemoryAtom { Definition: CallIdentity } : value == f.C(7), "跨调用按逃逸保留或改写");
        }
        var g = new Fixture(); var lower = g.Read(-8); var arg = g.Read(0); var next = g.Read(8); var gap = g.Read(24);
        var qs = new StateQueries(); var cs = qs.CreateContext(g.Finish(g.Write(-8, g.C(3)), g.Write(0, g.C(4)), g.Write(8, g.C(5)), g.Write(24, g.C(6)),
            new Call(new(), new ImageFunction(1), [], [], OutgoingArgumentArea: g.Frame), lower, arg, next, gap));
        a.True(Good(cs.Get(qs.Read, lower.Identity)) == g.C(3) && Good(cs.Get(qs.Read, gap.Identity)) == g.C(6), "实参区之前与间隙之后保留");
        a.True(Good(cs.Get(qs.Read, arg.Identity)).Identity is MemoryAtom && Good(cs.Get(qs.Read, next.Identity)).Identity is MemoryAtom, "未知栈实参区连续槽被改写");
        var h = new Fixture(); var read = h.Read(0); var unknownWrite = new MemoryWrite(new(), h.C(123), 64, h.C(8));
        var qh = new StateQueries(); var ch = qh.CreateContext(h.Finish(h.Write(0, h.C(7)), new Call(new(), new ImageFunction(1), [new(new(SlotKind.Integer), h.Frame)], []), unknownWrite, read));
        a.True(Good(ch.Get(qh.Read, read.Identity)).Identity is MemoryAtom m && m.Definition == unknownWrite.Identity, "不能判定写入成为最近定义");
        var known = new Fixture(); var kr0 = known.Read(0); var kr8 = known.Read(8);
        var kq = new StateQueries(new KnownStack()); var kc = kq.CreateContext(known.Finish(known.Write(0, known.C(2)), known.Write(8, known.C(3)),
            new Call(new(), new ImageFunction(1), [], [], OutgoingArgumentArea: known.Frame), kr0, kr8));
        a.True(Good(kc.Get(kq.Read, kr0.Identity)).Identity is MemoryAtom && Good(kc.Get(kq.Read, kr8.Identity)) == known.C(3), "效果来源给定栈实参区大小");
        var upper = new Fixture(); var ur = upper.Read(-8); var uq = new StateQueries();
        var uc = uq.CreateContext(upper.Finish(upper.Write(-8, upper.C(6)), new Call(new(), new ImageFunction(1), [new(new(SlotKind.Integer), upper.Frame)], []), ur));
        a.True(Good(uc.Get(uq.Read, ur.Identity)) == upper.C(6), "逃逸地址以下的槽跨调用保持");
    }
    private sealed class KnownStack : ICallEffectSource
    {
        public Outcome<CallEffects> Get(QueryContext context, Call call) => Outcome<CallEffects>.Success(new(false, 8, []));
    }
    private static void Caller(Assertions a)
    {
        var f = new Fixture(); var caller = f.Terms.Atom(new CallerValue(0), 64); var r = f.Read(0);
        var q = new StateQueries(); var c = q.CreateContext(f.Finish(f.Write(0, caller), r, new Call(new(), new ImageFunction(1), [new(new(SlotKind.Integer), r.Result)], [])));
        a.True(Good(c.Get(q.Read, r.Identity)) == caller, "保存后恢复调用方的值");
        var holes = Good(c.Get(q.CallerUses, 0));
        a.True(holes.Length == 1 && holes[0].Point.Before == 2 && holes[0].Caller == new CallerValue(0), "调用方值传给调用带位置报洞");
        StateFrontendChecks.Check(a);
    }
    private static void Scale()
    {
        var f = new Fixture(); var ids = Enumerable.Range(0, 1000).Select(i => i == 0 ? f.Entry : new BlockIdentity()).ToArray();
        var reads = new List<MemoryRead>();
        for (int i = 0; i < ids.Length; i++)
        {
            var r = f.Read(0); reads.Add(r);
            f.Builder.Blocks.Add(new(ids[i], [], i == 0 ? [f.Write(0, f.C(7)), r] : [r], i == ids.Length - 1 ? new Return([]) : new Jump(ids[i + 1])));
        }
        var q = new StateQueries(); var c = q.CreateContext(f.Builder.Freeze()); var timer = Stopwatch.StartNew();
        foreach (var r in reads) _ = Good(c.Get(q.Read, r.Identity));
        Console.WriteLine($"状态模型测量：1000 块、1000 次读取，{timer.Elapsed.TotalMilliseconds:F1} ms");
    }
}
