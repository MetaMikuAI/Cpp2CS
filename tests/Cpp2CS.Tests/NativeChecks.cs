using Cpp2CS.Native.Images;
using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Tests;

internal static partial class NativeChecks
{
    public const string Command = "native";
    private sealed record Named(string Name) : AtomIdentity
    {
        public override string StableText => "test." + Name;
    }
    private sealed record CustomOperator(string Tag) : Operator
    {
        public override string Name => "test." + Tag;
        public override bool Accepts(int resultWidth, ImmutableArray<int> operandWidths) => resultWidth == 8 && operandWidths.SequenceEqual([8]);
    }
    private sealed class Fixture
    {
        internal readonly TermTable Terms = new();
        internal readonly BlockIdentity Entry = new();
        internal readonly FunctionBuilder Builder;
        internal readonly Term Frame;
        internal Fixture()
        {
            Frame = Terms.Atom(new RootAtom(AddressRoot.Frame), 64);
            Builder = new(Terms, Entry, 64, new(Frame));
        }
        internal Term C(int value = 0, int width = 32) => Terms.Constant(value, width);
        internal Block Block(Terminator? end = null, params Statement[] statements) => new(Entry, [], [.. statements], end ?? new Return([]));
        internal NativeFunction Finish(params Block[] blocks)
        {
            Builder.Blocks.AddRange(blocks);
            return Builder.Freeze();
        }
        internal Term Input(int index = 0, int width = 32)
        {
            var slot = new AbstractSlot(SlotKind.Integer, index);
            var term = Terms.Atom(new EntryAtom(slot), width);
            Builder.Inputs.Add(new(slot, term));
            return term;
        }
        internal Term Result(StableIdentity id, int width = 32, int index = 0) => Terms.Atom(new ResultAtom(id, index), width);
    }
    private static AbstractSlot Output => new(SlotKind.Integer);
    private static Return Ret(Term value) => new([new(Output, value)]);
    private static void Reject(Assertions a, Action action, string name)
    {
        bool rejected = false;
        try
        {
            action();
        }
        catch (ArgumentException)
        {
            rejected = true;
        }
        a.True(rejected, name);
    }
    public static int Run()
    {
        var a = new Assertions();
        ReviewContracts(a);
        Scale(a);
        DominanceOracle(a);
        Terms(a);
        ValidGraphs(a);
        InvalidGraphs(a);
        // 映像查询不属于 IR 词汇；IR 引用的公共类型仍递归纳入检查。
        var assembly = typeof(NativeFunction).Assembly;
        var pending = new Queue<Type>(assembly.GetExportedTypes().Where(t => t.Namespace != typeof(IImage).Namespace));
        var visited = new HashSet<Type>();
        var publicNames = new List<string>();
        while (pending.TryDequeue(out var type))
        {
            if (!visited.Add(type)) continue;
            if (type.HasElementType) pending.Enqueue(type.GetElementType()!);
            foreach (var argument in type.GetGenericArguments()) pending.Enqueue(argument);
            if (type.Assembly != assembly) continue;
            publicNames.Add(type.Name);
            foreach (var nested in type.GetNestedTypes(System.Reflection.BindingFlags.Public)) pending.Enqueue(nested);
            foreach (var member in type.GetMembers(System.Reflection.BindingFlags.Public | System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.Static | System.Reflection.BindingFlags.DeclaredOnly))
            {
                publicNames.Add(member.Name);
                if (member is System.Reflection.PropertyInfo property) pending.Enqueue(property.PropertyType);
                if (member is System.Reflection.FieldInfo field) pending.Enqueue(field.FieldType);
                if (member is System.Reflection.MethodInfo method) pending.Enqueue(method.ReturnType);
                if (member is System.Reflection.MethodBase callable)
                    foreach (var parameter in callable.GetParameters()) pending.Enqueue(parameter.ParameterType);
            }
        }
        a.True(!publicNames.Any(n => new[] { "Register", "Flag", "StackPointer", "Instruction", "Section" }.Any(word => n.Contains(word, StringComparison.OrdinalIgnoreCase))),
            "公开词汇不泄漏机器身份");
        return a.Finish("原生 IR");
    }
    private static void Terms(Assertions a)
    {
        var t = new TermTable();
        var c = t.Constant(5, 8);
        var u = t.Undefined(8);
        var why = new Reason("unsupported", "未支持的语义");
        var unknownId = new UnknownIdentity();
        var unknown = t.Unknown(8, why, unknownId);
        var atom = t.Atom(new Named("value"), 8);
        a.True(ReferenceEquals(c, t.Constant(5, 8)), "常量驻留");
        a.True(ReferenceEquals(u, t.Undefined(8)) && ReferenceEquals(unknown, t.Unknown(8, new("unsupported", "未支持的语义"), unknownId)), "未知与未定义驻留");
        a.True(!ReferenceEquals(unknown, t.Unknown(8, why)), "同原因的独立未知值不混同");
        a.True(!ReferenceEquals(c, u) && !ReferenceEquals(u, unknown) && !ReferenceEquals(unknown, t.Constant(0, 8)), "未知与未定义不混同常量");
        a.True(ReferenceEquals(atom, t.Atom(new Named("value"), 8)), "上层按值相等身份驻留");
        var add = new CoreOperator(CoreOperation.Add);
        a.True(ReferenceEquals(t.Apply(add, 8, c, atom), t.Apply(new CoreOperator(CoreOperation.Add), 8, c, atom)), "运算驻留");
        a.True(ReferenceEquals(t.Apply(new CustomOperator("opaque"), 8, c), t.Apply(new CustomOperator("opaque"), 8, c)), "上层运算驻留");
        a.True(ReferenceEquals(t.Slice(c, 1, 3), t.Slice(c, 1, 3)), "切片驻留");
        a.True(ReferenceEquals(t.Concat(c, atom), t.Concat(c, atom)) && t.Concat(c, atom).Width == 16, "低位在前拼接驻留");
        a.True(t.Constant(BigInteger.One << 127, 128).Width == 128, "常量支持宽位向量");
        Reject(a, () => t.Constant(256, 8), "拒绝越界常量");
        Reject(a, () => t.Constant(-1, 8), "拒绝负位型");
        Reject(a, () => t.Undefined(0), "拒绝零位宽");
        Reject(a, () => t.Unknown(8, new("", "")), "未知需要原因");
        Reject(a, () => t.Unknown(8, new("outer", "原因", new("", ""))), "原因链也必须完整");
        Reject(a, () => t.Atom(new Named("value"), 16), "同一原子不能改位宽");
        Reject(a, () => t.Apply(add, 8, c), "拒绝运算元数错误");
        Reject(a, () => t.Apply(add, 16, c, c), "拒绝结果位宽错误");
        Reject(a, () => t.Apply(add, 8, c, t.Constant(1, 16)), "拒绝操作数位宽错误");
        Reject(a, () => t.Apply(add, 8, c, new TermTable().Constant(1, 8)), "拒绝外表操作数");
        Reject(a, () => t.Slice(c, 7, 2), "拒绝切片越界");
        Reject(a, () => t.Slice(c, -1, 1), "拒绝负切片起点");
        Reject(a, () => t.Concat(), "拒绝空拼接");
        Reject(a, () => t.Concat(c, new TermTable().Constant(1, 8)), "拼接拒绝外表项");
        Reject(a, () => t.Apply(new CoreOperator(CoreOperation.Select), 8, c, c, c), "选择需要一位条件");
        Reject(a, () => t.Apply(new CoreOperator(CoreOperation.ZeroExtend), 8, c), "扩展必须增宽");
        Reject(a, () => t.Apply(new CoreOperator(CoreOperation.Truncate), 16, c), "截断必须减宽");
        Reject(a, () => t.Apply(new CoreOperator(CoreOperation.FloatAdd), 8, c, c), "浮点位宽检查");
        Reject(a, () => t.Apply(new CoreOperator((CoreOperation)999), 8, c, c), "拒绝未知核心运算");
        foreach (var operation in Enum.GetValues<CoreOperation>())
        {
            var op = new CoreOperator(operation);
            Term[] operands;
            int width;
            switch (operation)
            {
                case CoreOperation.Select:
                    operands = [t.Constant(1, 1), t.Constant(0, 32), t.Constant(1, 32)];
                    width = 32;
                    break;
                case CoreOperation.ZeroExtend or CoreOperation.SignExtend:
                    operands = [c];
                    width = 32;
                    break;
                case CoreOperation.Truncate:
                    operands = [t.Constant(1, 32)];
                    width = 8;
                    break;
                case >= CoreOperation.Equal and <= CoreOperation.UnsignedLessEqual:
                case >= CoreOperation.FloatEqual and <= CoreOperation.FloatUnordered:
                    operands = [t.Constant(0, 32), t.Constant(1, 32)];
                    width = 1;
                    break;
                case CoreOperation.FloatFusedMultiplyAdd:
                    operands = [t.Constant(0, 32), t.Constant(1, 32), t.Constant(2, 32)];
                    width = 32;
                    break;
                case CoreOperation.CountLeadingZeros or CoreOperation.PopulationCount or CoreOperation.ReverseBits or CoreOperation.ReverseBytes:
                case >= CoreOperation.FloatFloor and <= CoreOperation.FloatRoundToEven:
                case CoreOperation.Negate or CoreOperation.Not:
                case >= CoreOperation.FloatNegate and <= CoreOperation.FloatSqrt:
                case >= CoreOperation.SignedToFloat and <= CoreOperation.FloatConvert:
                    operands = [t.Constant(0, 32)];
                    width = 32;
                    break;
                default:
                    operands = [t.Constant(0, 32), t.Constant(1, 32)];
                    width = 32;
                    break;
            }
            a.True(t.Apply(op, width, operands).Width == width, "核心运算形状：" + operation);
        }
    }
    private static void Pass(Assertions a, NativeFunction function, string name)
    {
        var result = ExitChecker.Check(function);
        a.True(result.IsValid, name + ": " + string.Join(";", result.Violations.Select(x => x.Code + " " + x.Location)));
        if (result.IsValid) a.True(TextDump.Write(function) == TextDump.Write(function), name + "转储稳定");
    }
    private static NativeFunction Diamond(bool reverse)
    {
        var f = new Fixture();
        var condition = f.Input(width: 1);
        var left = new BlockIdentity();
        var right = new BlockIdentity();
        var exit = new BlockIdentity();
        var id = new MergeIdentity();
        var result = f.Result(id);
        var incoming = new[] { new Incoming(left, f.C(1)), new Incoming(right, f.C(2)) };
        if (reverse) Array.Reverse(incoming);
        var blocks = new[] { f.Block(new Branch(condition, left, right)), new Block(left, [], [], new Jump(exit)),
            new Block(right, [], [], new Jump(exit)), new Block(exit, [new(id, result, [.. incoming])], [], Ret(result)) };
        if (reverse) Array.Reverse(blocks);
        return f.Finish(blocks);
    }
    private static void ValidGraphs(Assertions a)
    {
        var f = new Fixture();
        var input = f.Input();
        var readId = new ReadIdentity();
        var read = f.Result(readId);
        var callId = new CallIdentity();
        var output = f.Result(callId);
        var allocationId = new FrameIdentity();
        var allocation = f.Result(allocationId, 64);
        var image = f.Terms.Atom(new RootAtom(AddressRoot.Image), 64);
        f.Builder.ImageBase = image;
        var global = f.Terms.Apply(new CoreOperator(CoreOperation.Add), 64, image, f.C(16, 64));
        var thread = f.Terms.Atom(new RootAtom(AddressRoot.Thread), 64);
        f.Builder.ThreadPointer = thread;
        var function = f.Finish(f.Block(Ret(output), new MemoryWrite(new WriteIdentity(), global, 32, input), new MemoryRead(readId, global, 32, read) { Trace = new(0x123456) },
            new DynamicAllocation(allocationId, f.C(16, 64), 16, allocation),
            new Call(callId, new ImageFunction(16), [new(Output, read)], [new(Output, output)])));
        Pass(a, function, "直线读写、分配和调用");
        a.True(!TextDump.Write(function).Contains("123456", StringComparison.Ordinal) && TextDump.Write(function, true).Contains("@0x123456", StringComparison.Ordinal), "默认不转储追溯地址");
        var snapshot = f.Builder.Freeze();
        f.Builder.Blocks.Clear();
        a.True(snapshot.Blocks.Length == 1, "冻结复制构造器集合");
        Pass(a, Diamond(false), "分支合流");
        a.True(TextDump.Write(Diamond(false)) == TextDump.Write(Diamond(true)), "构造顺序与合流输入顺序不影响可达图编号");
        var loop = new Fixture();
        var head = new BlockIdentity();
        var body = new BlockIdentity();
        var end = new BlockIdentity();
        var mergeId = new MergeIdentity();
        var counter = loop.Result(mergeId);
        var next = loop.Terms.Apply(new CoreOperator(CoreOperation.Add), 32, counter, loop.C(1));
        var condition = loop.Terms.Apply(new CoreOperator(CoreOperation.UnsignedLess), 1, counter, loop.C(10));
        Pass(a, loop.Finish(loop.Block(new Jump(head)), new(head, [new(mergeId, counter, [new(loop.Entry, loop.C()), new(body, next)])], [], new Branch(condition, body, end)),
            new(body, [], [], new Jump(head)), new(end, [], [], Ret(counter))), "循环与回边合流");
        var eh = new Fixture();
        var handler = new BlockIdentity();
        var ehId = new CallIdentity();
        var result = eh.Result(ehId);
        var exception = eh.Terms.Atom(new ExceptionAtom(handler), 64);
        Pass(a, eh.Finish(eh.Block(Ret(result), new Call(ehId, new ImportedTarget(new ImportSymbol("callee", "library")), [], [new(Output, result)], Unwind: handler)),
            new(handler, [], [], new ResumeUnwind(exception), new(exception, eh.Terms.Atom(new SelectorAtom(handler), 32), [new(ClauseKind.Cleanup, [])]))), "带展开边的调用");
        foreach (var clauses in new System.Collections.Immutable.ImmutableArray<ExceptionClause>[]
        {
            [new(ClauseKind.Catch, [new PointerTarget.Internal(0x120)])],
            [new(ClauseKind.CatchAll, [])],
            [new(ClauseKind.ExceptionSpecification, [])],
            [new(ClauseKind.ExceptionSpecification, [new PointerTarget.Internal(0x120), new PointerTarget.Import(new("type", "library", 7), 2)])]
        })
        {
            var clauseFixture = new Fixture();
            var clauseHandler = new BlockIdentity();
            var clauseCall = new CallIdentity();
            var clauseResult = clauseFixture.Result(clauseCall);
            var clauseException = clauseFixture.Terms.Atom(new ExceptionAtom(clauseHandler), 64);
            var clauseFunction = clauseFixture.Finish(clauseFixture.Block(Ret(clauseResult), new Call(clauseCall, new ImportedTarget(new("callee", "library", 3)), [], [new(Output, clauseResult)], Unwind: clauseHandler)),
                new(clauseHandler, [], [], new ResumeUnwind(clauseException), new(clauseException, clauseFixture.Terms.Atom(new SelectorAtom(clauseHandler), 32), clauses)));
            Pass(a, clauseFunction, "映像异常子句直接用于处理入口");
            var dump = TextDump.Write(clauseFunction);
            a.True(dump.Contains("#3", StringComparison.Ordinal) && dump.Contains(clauses[0].Kind.ToString(), StringComparison.Ordinal), "转储保留导入序号和子句种类");
        }
        foreach (var clause in new ExceptionClause[]
        {
            new(ClauseKind.Catch, []), new(ClauseKind.CatchAll, [new PointerTarget.Internal(1)]),
            new(ClauseKind.Cleanup, [new PointerTarget.Internal(1)]), new(ClauseKind.Catch, [new PointerTarget.Unknown("缺少证据")]),
            new(ClauseKind.ExceptionSpecification, default)
        })
        {
            var clauseFixture = new Fixture();
            var clauseHandler = new BlockIdentity();
            var clauseCall = new CallIdentity();
            var clauseResult = clauseFixture.Result(clauseCall);
            var clauseException = clauseFixture.Terms.Atom(new ExceptionAtom(clauseHandler), 64);
            var clauseFunction = clauseFixture.Finish(clauseFixture.Block(Ret(clauseResult), new Call(clauseCall, new ImageFunction(0), [], [new(Output, clauseResult)], Unwind: clauseHandler)),
                new(clauseHandler, [], [], new ResumeUnwind(clauseException), new(clauseException, clauseFixture.Terms.Atom(new SelectorAtom(clauseHandler), 32), [clause])));
            a.True(ExitChecker.Check(clauseFunction).Violations.Any(d => d.Code == "clause"), "拒绝非法匹配集合");
        }
        var sw = new Fixture();
        var one = new BlockIdentity();
        var two = new BlockIdentity();
        Pass(a, sw.Finish(sw.Block(new JumpTable(sw.C(1), [new(1, one), new(2, two)], two)),
            new(one, [], [], new Return([])), new(two, [], [], new Unreachable())), "跳转表");
        var nr = new Fixture();
        Pass(a, nr.Finish(nr.Block(new Unreachable(), new Call(new(), new ImportedTarget(new ImportSymbol("exit", "")), [], [], true))), "不返回调用");
        var unknown = new Fixture();
        var hole = unknown.Terms.Unknown(32, new("unsupported", "尚未提升"));
        var holeFunction = unknown.Finish(unknown.Block(Ret(hole), new MemoryWrite(new WriteIdentity(), unknown.Frame, 32, hole)));
        Pass(a, holeFunction, "未知是合法的值");
        a.True(ExitChecker.Check(holeFunction).Holes is [{ Reason.Code: "unsupported" }], "洞按驻留未知项去重并保留原因");
        var copy = new ReadIdentity(readId);
        a.True(ReferenceEquals(copy.Origin, readId) && !ReferenceEquals(copy, readId), "复制有新身份和来源");
        var slots = new Fixture();
        foreach (var slot in new[] { new AbstractSlot(SlotKind.Integer), new(SlotKind.Floating), new(SlotKind.IndirectResult) })
            slots.Builder.Inputs.Add(new(slot, slots.Terms.Atom(new EntryAtom(slot), 64), slot.Kind == SlotKind.IndirectResult ? InputRole.IndirectResult : InputRole.Argument));
        Pass(a, slots.Finish(slots.Block()), "全部抽象槽类型");
    }
    private static void InvalidGraphs(Assertions a)
    {
        void Bad(string code, Func<Fixture, NativeFunction> make)
        {
            var result = ExitChecker.Check(make(new()));
            a.True(result.Violations.Any(x => x.Code == code && x.Location.Length > 0 && x.Message.Length > 0), "反例必须报告 " + code);
        }
        Bad("foreign-term", f => f.Finish(f.Block(Ret(new TermTable().Constant(1, 32)))));
        Bad("width", f => f.Finish(f.Block(null, new MemoryWrite(new WriteIdentity(), f.Frame, 64, f.C()))));
        Bad("width", f => f.Finish(f.Block(new Branch(f.C(), f.Entry, f.Entry))));
        Bad("target", f => f.Finish(f.Block(new Jump(new()))));
        Bad("entry", f => f.Finish(new Block(new(), [], [], new Return([]))));
        Bad("duplicate-block", f => f.Finish(f.Block(), f.Block()));
        Bad("entry-merge", f => { var id = new MergeIdentity(); return f.Finish(f.Block() with { Merges = [new(id, f.Result(id), [])] }); });
        Bad("merge-predecessors", f => { var block = new BlockIdentity(); var id = new MergeIdentity(); return f.Finish(f.Block(new Jump(block)), new(block, [new(id, f.Result(id), [])], [], new Return([]))); });
        Bad("merge-predecessors", f => { var block = new BlockIdentity(); var id = new MergeIdentity(); return f.Finish(f.Block(new Jump(block)), new(block, [new(id, f.Result(id), [new(f.Entry, f.C()), new(f.Entry, f.C())])], [], new Return([]))); });
        Bad("undefined-atom", f => f.Finish(f.Block(Ret(f.Terms.Atom(new Named("missing"), 32)))));
        Bad("dominance", f => { var id = new ReadIdentity(); var result = f.Result(id); return f.Finish(f.Block(null, new MemoryWrite(new WriteIdentity(), f.Frame, 32, result), new MemoryRead(id, f.Frame, 32, result))); });
        Bad("duplicate-definition", f => { var value = f.Input(); f.Builder.Inputs.Add(f.Builder.Inputs[0]); return f.Finish(f.Block(Ret(value))); });
        Bad("definition-kind", f => { f.Builder.Inputs.Add(new(Output, f.C())); return f.Finish(f.Block()); });
        Bad("result-identity", f => f.Finish(f.Block(null, new MemoryRead(new(), f.Frame, 32, f.Terms.Atom(new Named("bad-result"), 32)))));
        Bad("duplicate-identity", f => { var id = new CallIdentity(); return f.Finish(f.Block(null, new Call(id, new ImportedTarget(new ImportSymbol("callee", "")), [], []), new Call(id, new ImportedTarget(new ImportSymbol("callee", "")), [], []))); });
        Bad("slot", f => f.Finish(f.Block(null, new Call(new(), new ImportedTarget(new ImportSymbol("callee", "")), [new(new((SlotKind)99), f.C())], []))));
        Bad("slot", f => f.Finish(f.Block(new Return([new(new(SlotKind.Integer, -1), f.C())]))));
        Bad("slot", f => f.Finish(f.Block(new Return([new(new(SlotKind.IndirectResult, 1), f.C())]))));
        Bad("duplicate-slot", f => f.Finish(f.Block(new Return([new(Output, f.C()), new(Output, f.C())]))));
        Bad("entry-identity", f => { f.Builder.Inputs.Add(new(Output, f.Terms.Atom(new Named("input"), 32))); return f.Finish(f.Block()); });
        Bad("input-role", f => { f.Input(); f.Builder.Inputs[0] = f.Builder.Inputs[0] with { Role = InputRole.IndirectResult }; return f.Finish(f.Block()); });
        Bad("root", f => { f.Builder.ImageBase = f.Terms.Atom(new Named("root"), 64); return f.Finish(f.Block()); });

        Bad("alignment", f => { var id = new FrameIdentity(); return f.Finish(f.Block(null, new DynamicAllocation(id, f.C(4, 64), 3, f.Result(id, 64)))); });
        Bad("noreturn", f => f.Finish(f.Block(null, new Call(new(), new ImportedTarget(new ImportSymbol("exit", "")), [], [], true))));
        Bad("call-target", f => f.Finish(f.Block(null, new Call(new(), new ComputedTarget(f.C()), [], []))));
        Bad("switch-case", f => f.Finish(f.Block(new JumpTable(f.C(), [new(0, f.Entry), new(0, f.Entry)], f.Entry))));
        Bad("handler-edge", f => { var handler = new BlockIdentity(); return f.Finish(f.Block(null, new Call(new(), new ImportedTarget(new ImportSymbol("callee", "")), [], [], Unwind: handler)), new(handler, [], [], new Return([]))); });
        Bad("exception-identity", f => { var handler = new BlockIdentity(); var exception = f.Terms.Atom(new Named("exception"), 64); return f.Finish(f.Block(null, new Call(new(), new ImportedTarget(new ImportSymbol("callee", "")), [], [], Unwind: handler)), new(handler, [], [], new ResumeUnwind(exception), new(exception, f.Terms.Atom(new SelectorAtom(handler), 32), [new(ClauseKind.Cleanup, [])]))); });
        Bad("clause", f => { var handler = new BlockIdentity(); var exception = f.Terms.Atom(new ExceptionAtom(handler), 64); return f.Finish(f.Block(null, new Call(new(), new ImportedTarget(new ImportSymbol("callee", "")), [], [], Unwind: handler)), new(handler, [], [], new ResumeUnwind(exception), new(exception, f.Terms.Atom(new SelectorAtom(handler), 32), []))); });
        Bad("collection", f => f.Finish(f.Block() with { Statements = default }));
        Bad("dominance", f =>
        {
            var handler = new BlockIdentity(); var id = new CallIdentity(); var result = f.Result(id); var exception = f.Terms.Atom(new ExceptionAtom(handler), 64);
            return f.Finish(f.Block(Ret(result), new Call(id, new ImportedTarget(new ImportSymbol("callee", "")), [], [new(Output, result)], Unwind: handler)),
                new(handler, [], [], Ret(result), new(exception, f.Terms.Atom(new SelectorAtom(handler), 32), [new(ClauseKind.Cleanup, [])])));
        });
        Bad("dominance", f =>
        {
            var left = new BlockIdentity(); var right = new BlockIdentity(); var exit = new BlockIdentity(); var readId = new ReadIdentity(); var read = f.Result(readId); var mergeId = new MergeIdentity(); var value = f.Result(mergeId);
            return f.Finish(f.Block(new Branch(f.C(1, 1), left, right)), new(left, [], [new MemoryRead(readId, f.Frame, 32, read)], new Jump(exit)),
                new(right, [], [], new Jump(exit)), new(exit, [new(mergeId, value, [new(left, read), new(right, read)])], [], Ret(value)));
        });
        Bad("dominance", f =>
        {
            var handler = new BlockIdentity(); var readId = new ReadIdentity(); var read = f.Result(readId);
            var mergeId = new MergeIdentity(); var merged = f.Result(mergeId); var exception = f.Terms.Atom(new ExceptionAtom(handler), 64);
            return f.Finish(f.Block(null,
                new Call(new(), new ImportedTarget(new ImportSymbol("first", "")), [], [], Unwind: handler),
                new MemoryRead(readId, f.Frame, 32, read),
                new Call(new(), new ImportedTarget(new ImportSymbol("second", "")), [], [], Unwind: handler)),
                new(handler, [new(mergeId, merged, [new(f.Entry, read)])], [], Ret(merged), new(exception, f.Terms.Atom(new SelectorAtom(handler), 32), [new(ClauseKind.Cleanup, [])])));
        });
        Bad("width", f =>
        {
            var exit = new BlockIdentity(); var id = new MergeIdentity();
            return f.Finish(f.Block(new Jump(exit)), new(exit, [new(id, f.Result(id), [new(f.Entry, f.C(0, 8))])], [], new Return([])));
        });
        Bad("width", f => { var id = new ReadIdentity(); return f.Finish(f.Block(null, new MemoryRead(id, f.C(), 64, f.Result(id)))); });
        Bad("handler-edge", f =>
        {
            var handler = new BlockIdentity(); var exception = f.Terms.Atom(new ExceptionAtom(handler), 64);
            return f.Finish(f.Block(new Jump(handler)), new(handler, [], [], new ResumeUnwind(exception), new(exception, f.Terms.Atom(new SelectorAtom(handler), 32), [new(ClauseKind.Cleanup, [])])));
        });
        var many = new Fixture();
        var bad = many.Finish(many.Block(new Branch(many.C(), new(), new()), new MemoryWrite(new WriteIdentity(), many.C(), 64, many.C())));
        a.True(ExitChecker.Check(bad).Violations.Length >= 4, "一次返回多个独立违例");
    }
}
