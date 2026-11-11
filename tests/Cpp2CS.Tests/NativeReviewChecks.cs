using System.Diagnostics;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Tests;

internal static partial class NativeChecks
{
    private static void ReviewContracts(Assertions a)
    {
        void Bad(string code, Fixture f, params Block[] blocks)
        {
            a.True(ExitChecker.Check(f.Finish(blocks)).Violations.Any(v => v.Code == code), "契约反例：" + code);
        }
        var f = new Fixture();
        var area = f.Terms.Apply(new CoreOperator(CoreOperation.Add), 64, f.Frame, f.C(16, 64));
        f.Builder.IncomingArgumentArea = area;
        var id = new CallIdentity();
        var result = f.Result(id);
        Pass(a, f.Finish(f.Block(Ret(result), new Call(id, new ComputedTarget(f.Frame), [], [new(Output, result)], OutgoingArgumentArea: area))), "栈实参区地址与调用加返回");
        var slot = new AbstractSlot(SlotKind.ArgumentArea, 8);
        f = new();
        f.Builder.Inputs.Add(new(slot, f.Terms.Atom(new EntryAtom(slot), 64)));
        Bad("slot", f, f.Block());
        f = new();
        Bad("slot", f, f.Block(null, new Call(new(), new ImageFunction(0), [new(slot, f.C())], [])));
        f = new();
        f.Builder.IncomingArgumentArea = f.C();
        Bad("width", f, f.Block());
        f = new();
        Bad("width", f, f.Block(null, new Call(new(), new ImageFunction(0), [], [], OutgoingArgumentArea: f.C())));
        f = new();
        Bad("undefined-atom", f, f.Block(null, new Call(new(), new ImageFunction(0), [], [], OutgoingArgumentArea: f.Terms.Atom(new Named("address"), 64))));
        foreach (var kind in new[] { AddressRoot.Frame, AddressRoot.Thread, (AddressRoot)99 })
        {
            f = new();
            f.Builder.ImageBase = f.Terms.Atom(new RootAtom(kind), 64);
            Bad("root", f, f.Block());
        }
        f = new();
        f.Builder.ThreadPointer = f.Terms.Atom(new RootAtom(AddressRoot.Thread), 32);
        Bad("width", f, f.Block());
        f = new();
        Bad("undefined-atom", f, f.Block(Ret(f.Terms.Atom(new RootAtom(AddressRoot.Image), 64))));
        f = new();
        Pass(a, f.Finish(f.Block(null, new Call(new(), new ImageFunction(ulong.MaxValue), [], []))), "单入口偏移与无本地处理入口的调用");
        f = new();
        var handler = new BlockIdentity();
        var target = new BlockIdentity();
        var exception = f.Terms.Atom(new ExceptionAtom(handler), 64);
        var selector = f.Terms.Atom(new SelectorAtom(handler), 32);
        var condition = f.Terms.Apply(new CoreOperator(CoreOperation.Equal), 1, selector, f.C());
        Pass(a, f.Finish(f.Block(null, new Call(new(), new ImageFunction(0), [], [], Unwind: handler)),
            new(handler, [], [], new Branch(condition, target, target), new(exception, selector, [new(ClauseKind.Cleanup, null)])),
            new(target, [], [], new ResumeUnwind(exception))), "处理入口选择值控制分支");
        f = new();
        exception = f.Terms.Atom(new ExceptionAtom(handler), 64);
        selector = f.Terms.Atom(new SelectorAtom(new()), 32);
        Bad("selector-identity", f, f.Block(), new(handler, [], [], new Return([]), new(exception, selector, [new(ClauseKind.Cleanup, null)])));
        f = new();
        selector = f.Terms.Atom(new SelectorAtom(handler), 32);
        exception = f.Terms.Atom(new ExceptionAtom(handler), 64);
        Bad("dominance", f, f.Block(Ret(selector), new Call(new(), new ImageFunction(0), [], [], Unwind: handler)),
            new(handler, [], [], new ResumeUnwind(exception), new(exception, selector, [new(ClauseKind.Cleanup, null)])));
        f = new();
        var copy = new BlockIdentity(f.Entry);
        var copied = new Block(copy, [], [], new Return([])) { Trace = new(0xabcdef) };
        var snapshot = f.Finish(f.Block(new Jump(copy)), copied);
        Pass(a, snapshot, "块复制身份");
        a.True(ReferenceEquals(copy.Origin, f.Entry), "块来源保留");
        a.True(!TextDump.Write(snapshot).Contains("abcdef") && TextDump.Write(snapshot, true).Contains("@0xabcdef"), "块地址仅用于可选追溯");
        a.True(TextDump.Write(snapshot).Contains("origin="), "转储块来源");
        f = new();
        handler = new();
        var readId = new ReadIdentity();
        var read = f.Result(readId);
        var mergeId = new MergeIdentity();
        var merged = f.Result(mergeId);
        exception = f.Terms.Atom(new ExceptionAtom(handler), 64);
        selector = f.Terms.Atom(new SelectorAtom(handler), 32);
        Pass(a, f.Finish(f.Block(null,
            new MemoryRead(readId, f.Frame, 32, read),
            new Call(new(), new ImageFunction(0), [], [], Unwind: handler),
            new Call(new(), new ImageFunction(4), [], [], Unwind: handler)),
            new(handler, [new(mergeId, merged, [new(f.Entry, read)])], [], Ret(merged),
                new(exception, selector, [new(ClauseKind.Cleanup, null)]))), "每个展开调用之前已定义的合流值可用");
        f = new();
        var unreachable = new BlockIdentity();
        readId = new();
        read = f.Result(readId);
        handler = new();
        exception = f.Terms.Atom(new ExceptionAtom(handler), 64);
        selector = f.Terms.Atom(new SelectorAtom(handler), 32);
        Pass(a, f.Finish(f.Block(), new(unreachable, [], [
            new MemoryRead(readId, f.Frame, 32, read),
            new Call(new(), new ImageFunction(0), [], [], Unwind: handler)], Ret(read)),
            new(handler, [], [], new ResumeUnwind(exception), new(exception, selector, [new(ClauseKind.Cleanup, null)]))),
            "不可达块内展开调用的正常续接保留局部顺序");
        var terms = new TermTable();
        var value = terms.Constant(3, 32);
        var add = terms.Apply(new CoreOperator(CoreOperation.Add), 32, value, value);
        a.True(value.ConstantValue == 3 && value.Operator is null && value.SliceLow is null, "常量带类型访问器");
        a.True(add.Operator is CoreOperator { Operation: CoreOperation.Add } && add.ConstantValue is null, "运算带类型访问器");
        a.True(terms.Slice(value, 2, 4).SliceLow == 2, "切片带类型访问器");
        foreach (var operation in Enum.GetValues<CoreOperation>())
            Reject(a, () => terms.Apply(new CoreOperator(operation), 32), "每种运算拒绝空操作数：" + operation);
        Reject(a, () => terms.Apply(new CoreOperator(CoreOperation.ReverseBytes), 7, terms.Constant(0, 7)), "字节反转拒绝非整字节");
        a.True(!Enum.GetNames<CoreOperation>().Contains("Bitcast"), "无同宽重解释操作");
        a.True(!Enum.GetNames<AddressRoot>().Contains("Other"), "其他不是地址根原子");
        a.True(typeof(FrameDescription).GetProperty("Objects") is null, "前端不划分静态帧对象");
        f = new();
        Term shared = f.C(1);
        for (int i = 0; i < 60; i++) shared = f.Terms.Apply(new CoreOperator(CoreOperation.Add), 32, shared, shared);
        var graph = f.Finish(f.Block(Ret(shared)));
        string dump = TextDump.Write(graph);
        a.True(dump.Split('\n').Count(line => line.StartsWith("term ")) == 60 && dump.Length < 8000, "深 60 层双引用仅定义 60 项且文本线性");
        a.True(dump == TextDump.Write(graph), "共享项编号确定");
    }

    private static void Scale(Assertions a)
    {
        foreach (string shape in new[] { "chain", "diamonds", "nested-loops" })
        {
            var f = new Fixture();
            const int count = 3000;
            var blocks = new List<Block> { f.Block(new Jump(new())) };
            var nodes = Enumerable.Range(0, count * 3 + 1).Select(_ => new BlockIdentity()).ToArray();
            blocks[0] = f.Block(new Jump(nodes[0]));
            for (int i = 0; i < count; i++)
            {
                if (shape == "chain") blocks.Add(new(nodes[i], [], [], new Jump(nodes[i + 1])));
                else if (shape == "diamonds")
                {
                    blocks.Add(new(nodes[3 * i], [], [], new Branch(f.C(1, 1), nodes[3 * i + 1], nodes[3 * i + 2])));
                    blocks.Add(new(nodes[3 * i + 1], [], [], new Jump(nodes[3 * i + 3])));
                    blocks.Add(new(nodes[3 * i + 2], [], [], new Jump(nodes[3 * i + 3])));
                }
                else
                {
                    // 头逐层进入，尾逐层退出并回到各自的头。
                    blocks.Add(new(nodes[i], [], [], new Jump(nodes[i + 1])));
                    blocks.Add(new(nodes[2 * count - i], [], [], new Branch(f.C(1, 1), nodes[i], nodes[2 * count - i + 1])));
                }
            }
            int end = shape == "diamonds" ? 3 * count : count;
            blocks.Add(new(nodes[end], [], [], shape == "nested-loops" ? new Jump(nodes[count + 1]) : new Return([])));
            if (shape == "nested-loops") blocks.Add(new(nodes[2 * count + 1], [], [], new Return([])));
            var function = f.Finish(blocks.ToArray());
            var watch = Stopwatch.StartNew();
            var result = ExitChecker.Check(function);
            watch.Stop();
            a.True(result.IsValid, shape + " 规模检查契约有效");
            a.True(watch.Elapsed < TimeSpan.FromSeconds(1), shape + " 出口检查小于一秒：" + watch.Elapsed.TotalMilliseconds);
            Console.WriteLine($"native {shape}: {blocks.Count} blocks, {watch.Elapsed.TotalMilliseconds:F1} ms");
        }
    }

    private static void DominanceOracle(Assertions a)
    {
        // 小图用集合不动点作为独立参照，覆盖回边、不可约循环和不同块存储顺序。
        var random = new Random(7821);
        for (int sample = 0; sample < 40; sample++)
        {
            const int count = 12;
            var targets = Enumerable.Range(0, count).Select(i => new[] { (i + 1) % count, random.Next(count) }).ToArray();
            var dom = Enumerable.Range(0, count).Select(i => i == 0 ? new HashSet<int> { 0 } : Enumerable.Range(0, count).ToHashSet()).ToArray();
            bool changed;
            do
            {
                changed = false;
                for (int i = 1; i < count; i++)
                {
                    var next = Enumerable.Range(0, count).ToHashSet();
                    for (int j = 0; j < count; j++) if (targets[j].Contains(i)) next.IntersectWith(dom[j]);
                    next.Add(i);
                    if (next.SetEquals(dom[i])) continue;
                    dom[i] = next;
                    changed = true;
                }
            } while (changed);
            for (int definition = 0; definition < count; definition++)
            {
                var f = new Fixture();
                var nodes = Enumerable.Range(0, count).Select(i => i == 0 ? f.Entry : new BlockIdentity()).ToArray();
                var id = new ReadIdentity();
                var value = f.Result(id);
                var blocks = Enumerable.Range(0, count).Select(i => new Block(nodes[i], [],
                    i == definition ? [new MemoryRead(id, f.Frame, 32, value), new MemoryWrite(f.Frame, 32, value)] : [new MemoryWrite(f.Frame, 32, value)],
                    new Branch(f.C(1, 1), nodes[targets[i][0]], nodes[targets[i][1]]))).Reverse().ToArray();
                var result = ExitChecker.Check(f.Finish(blocks));
                for (int use = 0; use < count; use++)
                {
                    string location = $"block[{count - 1 - use}].statement[{(use == definition ? 1 : 0)}]";
                    bool rejected = result.Violations.Any(v => v.Code == "dominance" && v.Location == location);
                    a.True(rejected == !dom[use].Contains(definition), "支配树与独立集合参照一致");
                }
            }
        }
    }
}
