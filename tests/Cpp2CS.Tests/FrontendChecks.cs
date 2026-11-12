using System.Collections.Immutable;
using System.Diagnostics;
using System.Numerics;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Tests;

internal static class FrontendChecks
{
    public const string Command = "frontend";
    private static readonly Register R0 = new("a", 64), R1 = new("b", 64), R2 = new("c", 64), R3 = new("d", 64),
        Sp = new("stack", 64), V = new("wide", 128), Z = new("zero", 1), C = new("carry", 1);
    private static readonly ImmutableArray<Register> Registers = [R0, R1, R2, R3, Sp, V, Z, C];
    // 返回地址占入口栈顶八字节，随后八字节为调用者保留区；第零整数槽位于 c，结果位于 b。
    private static readonly RegisterConvention Convention = new([new(R2, new(SlotKind.Integer))],
        [new(R1, new(SlotKind.Integer))], [R3], Sp, 16, 8, [R3]);
    private enum Op { Move, Add, Copy, Partial, Low, Load, Store, Compare, Branch, Jump, Indirect, Call, Return, Trap, Bad, Push, Pop, Image, Thread, ImportCall, ComputedCall, Guard, Resume, BeginCatch, EndCatch, Rethrow }
    private sealed record Ins(Op Op, Register? To = null, Register? From = null, ulong Value = 0, ulong Other = 0);
    private sealed class Toy(IReadOnlyDictionary<ulong, Ins> code, int extraRegisters = 0, ImmutableArray<TryRegion> regions = default) : IInstructionSet, IExceptionFlowProvider, IExceptionModel
    {
        public ImmutableArray<TryRegion> Regions { get; } = regions.IsDefault ? [] : regions;
        public IExceptionModel ExceptionModel => this;
        public void EnterHandler(IRegisterState state, Term exception, Term selector)
        { state.Write(R0, exception); state.Write(R1, selector); }
        public bool IsResumeUnwind(CallTarget target) => target is ImportedTarget { Symbol.Name: "_Unwind_Resume" };
        public Term ResumeException(IRegisterReader state) => state.Read(R0);
        public ImmutableArray<Register> Registers { get; } = [.. FrontendChecks.Registers,
            .. Enumerable.Range(0, extraRegisters).Select(i => new Register("unused" + i, 64))];
        public DecodeResult Decode(ulong address) => !code.TryGetValue(address, out var ins)
            ? new(null, new("missing-instruction", "玩具代码没有此指令。"))
            : new(new(1, e => Emit(ins, e)), null);
        private static void Emit(Ins i, IEmitter e)
        {
            Term Constant(ulong value, int width = 64) => e.Terms.Constant(value, width);
            Term Add(Term left, ulong right) => e.Terms.Apply(new CoreOperator(CoreOperation.Add), left.Width, left, Constant(right, left.Width));
            switch (i.Op)
            {
                case Op.Move: e.Write(i.To!, Constant(i.Value, i.To!.Width)); break;
                case Op.Add: e.Write(i.To!, Add(e.Read(i.To!), i.Value)); break;
                case Op.Copy: e.Write(i.To!, e.Read(i.From!)); break;
                case Op.Partial: e.Write(i.To!, e.Terms.Concat(Constant(i.Value, 8), e.Terms.Slice(e.Read(i.To!), 8, i.To!.Width - 8))); break;
                case Op.Low: e.Write(i.To!, e.Terms.Concat(e.Terms.Slice(e.Read(i.From!), 0, 8), Constant(0, i.To!.Width - 8))); break;
                case Op.Load: e.Write(i.To!, e.Load(Add(e.Read(Sp), i.Value), i.To!.Width)); break;
                case Op.Store: e.Store(Add(e.Read(Sp), i.Value), e.Read(i.From!)); break;
                case Op.Compare:
                    e.Write(Z, e.Terms.Apply(new CoreOperator(CoreOperation.Equal), 1, e.Read(i.From!), Constant(i.Value)));
                    e.Write(C, e.Terms.Apply(new CoreOperator(CoreOperation.UnsignedLess), 1, e.Read(i.From!), Constant(i.Value))); break;
                case Op.Branch: e.Branch(e.Read(i.From ?? Z), i.Value, i.Other); break;
                case Op.Jump: e.Jump(i.Value); break;
                case Op.Indirect: e.IndirectJump(e.Read(i.From!)); break;
                case Op.Call: e.Call(new ImageFunction(i.Value)); break;
                case Op.Resume: e.Call(new ImportedTarget(new ImportSymbol("_Unwind_Resume"))); break;
                case Op.BeginCatch: e.Call(new ImportedTarget(new ImportSymbol("__cxa_begin_catch"))); break;
                case Op.EndCatch: e.Call(new ImportedTarget(new ImportSymbol("__cxa_end_catch"))); break;
                case Op.Rethrow: e.Call(new ImportedTarget(new ImportSymbol("__cxa_rethrow"))); break;
                case Op.Image: e.Write(i.To!, e.ImageAddress(i.Value)); break;
                case Op.Thread: e.Write(i.To!, e.ThreadPointer); break;
                case Op.ImportCall: e.Call(new ImportedTarget(new ImportSymbol("toy_import"))); break;
                case Op.ComputedCall: e.Call(new ComputedTarget(e.Read(i.From!))); break;
                case Op.Return: e.Return(); break;
                case Op.Trap: e.Trap(); break;
                case Op.Guard: e.TrapIf(e.Terms.Apply(new CoreOperator(CoreOperation.Equal), 1, e.Read(i.From!), Constant(i.Value))); break;
                case Op.Bad: e.Fail(new("toy-unsupported", "不支持的玩具指令。")); break;
                case Op.Push:
                    e.Write(Sp, e.Terms.Apply(new CoreOperator(CoreOperation.Subtract), 64, e.Read(Sp), Constant(8)));
                    e.Store(e.Read(Sp), e.Read(i.From!)); break;
                case Op.Pop: e.Write(i.To!, e.Load(e.Read(Sp), 64)); e.Write(Sp, Add(e.Read(Sp), 8)); break;
            }
        }
    }
    private sealed class Facts : IFlowFacts
    {
        public bool DoesNotReturn(CallTarget target) => target is ImageFunction { EntryOffset: 901 };
        public IndirectResolution ResolveIndirect(ulong address, Term target, IIndirectContext context) => address == 1
            ? new IndirectTable(target, [new(0, 2), new(1, 4)], 6) : new IndirectUnknown(new("indirect-target", "间接目标无法判定。"));
    }
    private static Dictionary<ulong, Ins> Code(params Ins[] instructions) => instructions.Select((i, n) => (i, n)).ToDictionary(x => (ulong)x.n, x => x.i);
    private static LiftResult Lift(Dictionary<ulong, Ins> code, bool reverse = false, int extra = 0) => FunctionLifter.Lift(
        new Toy(code, extra), Convention, new Facts(), new(0, code.Keys.Max() + 1, FunctionEvidence.SymbolTable), 0, discoveryOrder: reverse ? Comparer<ulong>.Create((a, b) => b.CompareTo(a)) : null);
    private static NativeFunction Good(Assertions checks, Dictionary<ulong, Ins> code, bool determinism = true)
    {
        var result = Lift(code);
        checks.True(result.Function is not null && result.Failure is null, "提升成功：" + result.Failure);
        var function = result.Function ?? throw new InvalidOperationException(result.Failure?.ToString());
        checks.True(ExitChecker.Check(function) is { IsValid: true, Holes.IsEmpty: true }, "产物通过出口且无洞");
        if (determinism)
        {
            checks.True(TextDump.Write(function, true) == TextDump.Write(Lift(code).Function!, true), "重复提升转储一致");
            checks.True(TextDump.Write(function, true) == TextDump.Write(Lift(code, true).Function!, true), "逆地址发现转储一致");
            var shuffled = FunctionLifter.Lift(new Toy(code), Convention, new Facts(), new(0, code.Keys.Max() + 1, FunctionEvidence.SymbolTable), 0,
                discoveryOrder: Comparer<ulong>.Create((a, b) => unchecked(a * 6364136223846793005UL).CompareTo(unchecked(b * 6364136223846793005UL))));
            checks.True(TextDump.Write(function, true) == TextDump.Write(shuffled.Function!, true), "打乱地址优先次序的转储一致");
        }
        return function;
    }
    public static int Run()
    {
        var checks = new Assertions();
        var straight = Good(checks, Code(new(Op.Copy, R1, R2), new(Op.Add, R1, Value: 3), new(Op.Return)));
        checks.True(Execute(straight, 7) == 10, "直线执行");
        var diamond = Good(checks, Code(new(Op.Compare, From: R2, Value: 0), new(Op.Branch, Value: 2, Other: 4),
            new(Op.Move, R1, Value: 11), new(Op.Jump, Value: 5), new(Op.Move, R1, Value: 22), new(Op.Return)));
        checks.True(Execute(diamond, 0) == 11 && Execute(diamond, 1) == 22, "分支合流执行");
        checks.True(diamond.Blocks.Sum(b => b.Merges.Length) == 1, "只为被返回的寄存器合流");
        var middle = Good(checks, Code(new(Op.Move, R1, Value: 0), new(Op.Add, R1, Value: 1),
            new(Op.Compare, From: R1, Value: 3), new(Op.Branch, Value: 4, Other: 1), new(Op.Return)));
        checks.True(Execute(middle, 0) == 3, "跳入已发现块中间并拆块");
        var nested = Good(checks, Code(new(Op.Move, R0, Value: 0), new(Op.Move, R1, Value: 0),
            new(Op.Move, R3, Value: 0), new(Op.Add, R1, Value: 1), new(Op.Add, R3, Value: 1),
            new(Op.Compare, From: R3, Value: 3), new(Op.Branch, Value: 7, Other: 3),
            new(Op.Add, R0, Value: 1), new(Op.Compare, From: R0, Value: 2),
            new(Op.Branch, Value: 10, Other: 2), new(Op.Return)));
        checks.True(Execute(nested, 0) == 6, "嵌套循环");
        var backedges = Good(checks, Code(new(Op.Move, R1, Value: 0), new(Op.Add, R1, Value: 1),
            new(Op.Compare, From: R1, Value: 5), new(Op.Branch, Value: 9, Other: 4),
            new(Op.Compare, From: R2, Value: 0), new(Op.Branch, Value: 6, Other: 7),
            new(Op.Jump, Value: 1), new(Op.Add, R0, Value: 1), new(Op.Jump, Value: 1), new(Op.Return)));
        checks.True(Execute(backedges, 0) == 5 && Execute(backedges, 1) == 5, "多个回边");
        var entryLoop = Good(checks, Code(new(Op.Add, R2, Value: 1), new(Op.Compare, From: R2, Value: 3),
            new(Op.Branch, Value: 3, Other: 0), new(Op.Copy, R1, R2), new(Op.Return)));
        checks.True(Execute(entryLoop, 0) == 3, "入口回边使用独立前置入口");
        var partial = Good(checks, Code(new(Op.Move, R1, Value: 0x1234), new(Op.Partial, R1, Value: 0x56), new(Op.Return)));
        checks.True(Execute(partial, 0) == 0x1256, "部分写保留高位");
        var expectedPartial = partial.Terms.Constant(0x1256, 64);
        checks.True(partial.Blocks.Select(b => b.End).OfType<Return>().Single().Results[0].Value == expectedPartial,
            "部分写通过项表的切片与拼接入口规范化");
        var low = Good(checks, Code(new(Op.Move, V, Value: 0x1234), new(Op.Partial, V, Value: 0x56), new(Op.Low, R1, V), new(Op.Return)));
        checks.True(Execute(low, 0) == 0x56, "向量与子寄存器切片");
        var stack = Good(checks, Code(new(Op.Copy, R0, R2), new(Op.Push, From: R0), new(Op.Pop, R1), new(Op.Return)));
        checks.True(Execute(stack, 37) == 37 && stack.Blocks.SelectMany(b => b.Statements).Count() == 2, "SP 变化与栈读写保留");
        var calls = Good(checks, Code(new(Op.Move, R3, Value: 47), new(Op.Call, Value: 900),
            new(Op.Store, From: R3, Value: 24), new(Op.Return)));
        var call = calls.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single();
        checks.True(call.Arguments.Single().Value.Identity is EntryAtom { Slot.Kind: SlotKind.Integer }, "调用实参来自 c 的入口槽");
        checks.True(calls.Blocks.Select(b => b.End).OfType<Return>().Single().Results.Single().Value == call.Results.Single().Value, "调用结果是新定义");
        checks.True(calls.Blocks.SelectMany(b => b.Statements).OfType<MemoryWrite>().Single().Value.ConstantValue == 47, "调用保存 d");
        var clobber = Good(checks, Code(new(Op.Call, Value: 900), new(Op.Low, R1, R0), new(Op.Add, R1, Value: 1), new(Op.Return)));
        var clobberedValue = clobber.Blocks.Select(b => b.End).OfType<Return>().Single().Results[0].Value;
        var expectedClobber = clobber.Terms.Apply(new CoreOperator(CoreOperation.Add), 64,
            clobber.Terms.Concat(clobber.Terms.Undefined(8), clobber.Terms.Constant(0, 56)), clobber.Terms.Constant(1, 64));
        checks.True(clobberedValue == expectedClobber && new TermEvaluator(_ => 0).Evaluate(clobberedValue) is { Status: EvaluationStatus.Undefined, DefinedMask.IsZero: true },
            "调用破坏后的低位按规范形保留，算术结果每位未定义");
        var independent = Good(checks, Code(new(Op.Call, Value: 900), new(Op.Low, R0, R0), new(Op.Add, R0, Value: 1), new(Op.Move, R1, Value: 17), new(Op.Return)));
        checks.True(Execute(independent, 0) == 17, "未定义计算不污染无关结果");
        var tail = Good(checks, Code(new Ins(Op.Jump, Value: 900)));
        checks.True(tail.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single().Target is ImageFunction { EntryOffset: 900 }
            && tail.Blocks.Any(b => b.End is Return), "范围外跳转为调用加返回");
        checks.True(tail.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single().Trace?.NativeAddress == 0, "尾调用追溯到跳转指令而非被调入口");
        var twoTails = Good(checks, Code(new(Op.Compare, From: R2, Value: 0), new(Op.Branch, Value: 2, Other: 3),
            new(Op.Jump, Value: 900), new(Op.Jump, Value: 900)));
        checks.True(twoTails.Blocks.SelectMany(b => b.Statements).OfType<Call>().Select(c => c.Trace!.NativeAddress).Order().SequenceEqual(new ulong[] { 2, 3 }),
            "同目标的不同尾调用保留独立调用点");
        var noReturn = Good(checks, Code(new(Op.Call, Value: 901), new(Op.Bad)));
        checks.True(noReturn.Blocks.Last().End is Unreachable && noReturn.Blocks.Last().Statements.OfType<Call>().Single().Results.IsEmpty, "不返回调用停止发现");
        var table = Good(checks, Code(new(Op.Copy, R0, R2), new(Op.Indirect, From: R0),
            new(Op.Move, R1, Value: 10), new(Op.Return), new(Op.Move, R1, Value: 20), new(Op.Return), new(Op.Move, R1, Value: 30), new(Op.Return)));
        checks.True(Execute(table, 0) == 10 && Execute(table, 1) == 20 && Execute(table, 9) == 30, "解析器的跳转表与默认边");
        var bad = Lift(Code(new(Op.Move, R1, Value: 0), new(Op.Bad)));
        checks.True(bad is { Function: null, Failure.Address: 1, Failure.Reason.Code: "toy-unsupported" }, "失败保留地址和原因且无部分函数");
        checks.True(Lift(Code(new Ins(Op.Indirect, From: R2))) is { Function: null, Failure.Address: 0, Failure.Reason.Code: "indirect-target" }, "未知间接跳转报洞");
        var caller = Good(checks, Code(new(Op.Push, From: R3), new(Op.Pop, R3), new(Op.Move, R1), new(Op.Return)));
        checks.True(caller.Blocks.SelectMany(b => b.Statements).OfType<MemoryWrite>().Single().Value.Identity is CallerValue { Index: 0 }
            && caller.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>().Count() == 1, "保存恢复保留普通帧读写");
        checks.True(Lift(Code(new(Op.Push, From: R3), new(Op.Return))) is { Function: null, Failure.Address: 1, Failure.Reason.Code: "stack-restore" }, "未恢复 SP 报洞");
        var image = Good(checks, Code(new(Op.Image, R1, Value: 128), new(Op.Return)));
        checks.True(Walk(image.Blocks.Select(b => b.End).OfType<Return>().Single().Results[0].Value)
            .Any(t => t.Identity is RootAtom { Kind: AddressRoot.Image }), "映像地址保留映像根");
        var thread = Good(checks, Code(new(Op.Thread, R1), new(Op.Return)));
        checks.True(thread.Blocks.Select(b => b.End).OfType<Return>().Single().Results[0].Value.Identity is RootAtom { Kind: AddressRoot.Thread }, "线程指针为约定原子");
        var imports = Good(checks, Code(new(Op.ImportCall), new(Op.Return)));
        checks.True(imports.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single().Target is ImportedTarget, "导入调用目标");
        var computed = Good(checks, Code(new(Op.ComputedCall, From: R2), new(Op.Return)));
        checks.True(computed.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single().Target is ComputedTarget { Value.Identity: EntryAtom }, "间接调用目标参与 SSA");
        var trap = Good(checks, Code(new Ins(Op.Trap)));
        checks.True(trap.Blocks.Last().End is Unreachable, "陷入为不可达");
        var trivial = Good(checks, Code(new(Op.Compare, From: R2, Value: 0), new(Op.Branch, Value: 2, Other: 4),
            new(Op.Move, R1, Value: 7), new(Op.Jump, Value: 5), new(Op.Move, R1, Value: 7), new(Op.Return)));
        checks.True(trivial.Blocks.All(b => b.Merges.IsEmpty), "相同输入的平凡合流消去");
        var sameExpressions = Good(checks, Code(new(Op.Compare, From: R2, Value: 0), new(Op.Branch, Value: 2, Other: 5),
            new(Op.Copy, R1, R2), new(Op.Add, R1, Value: 1), new(Op.Jump, Value: 8),
            new(Op.Copy, R1, R2), new(Op.Add, R1, Value: 1), new(Op.Jump, Value: 8), new(Op.Return)));
        checks.True(sameExpressions.Blocks.All(b => b.Merges.IsEmpty) && Execute(sameExpressions, 4) == 5,
            "操作数归位后相等的表达式不保留平凡合流");
        ExceptionRegions(checks);
        RevisedContracts(checks);
        ConditionalTrap(checks);
        PartialPreservation(checks);
        MultipleSlots(checks);
        InternalAtom(checks);
        Scale(checks);
        RealisticScale(checks);
        return checks.Finish("共用前端");
    }
    private static void ExceptionRegions(Assertions checks)
    {
        ImmutableArray<ExceptionClause> clauses = [new(ClauseKind.Cleanup, [])];
        var code = Code(new(Op.Move, R3, Value: 7), new(Op.Move, V, Value: 17), new(Op.Call, Value: 900),
            new(Op.Move, R3, Value: 9), new(Op.Call, Value: 901), new(Op.Bad),
            new(Op.Store, From: R3), new(Op.Store, From: V, Value: 8), new(Op.Store, From: R2, Value: 24),
            new(Op.Store, From: R0, Value: 32), new(Op.Store, From: R1, Value: 40), new(Op.Resume));
        var convention = Convention with { PreservedParts = [new(V, 0, 32)], CallerValues = [R3, V] };
        var regions = ImmutableArray.Create(new TryRegion(2, 1, 6, clauses), new TryRegion(4, 1, 6, clauses));
        LiftResult With(Dictionary<ulong, Ins> instructions, ImmutableArray<TryRegion> areas, bool reverse = false) =>
            FunctionLifter.Lift(new Toy(instructions, regions: areas), convention, new Facts(),
                new(0, instructions.Keys.Max() + 1, FunctionEvidence.UnwindTable), 0,
                discoveryOrder: reverse ? Comparer<ulong>.Create((a, b) => b.CompareTo(a)) : null);
        var lifted = With(code, regions);
        checks.True(lifted.Function is not null, "异常区域提升成功：" + lifted.Failure);
        if (lifted.Function is not { } function) return;
        checks.True(ExitChecker.Check(function) is { IsValid: true, Holes.IsEmpty: true }, "异常图通过出口");
        var handler = function.Blocks.Single(b => b.Handler is not null);
        var calls = function.Blocks.SelectMany(b => b.Statements).OfType<Call>().ToArray();
        checks.True(calls.Length == 2 && calls.All(c => c.Unwind == handler.Identity) && calls[1].DoesNotReturn,
            "返回与不返回调用都带展开边");
        checks.True(handler.Trace?.NativeAddress == 6 && handler.Handler!.Exception.Identity is ExceptionAtom e && e.Handler == handler.Identity
            && handler.Handler.Selector.Identity is SelectorAtom selector && selector.Handler == handler.Identity
            && handler.Handler.Clauses.SequenceEqual(clauses), "额外处理入口定义两个入口项并保留子句表");
        var body = function.Blocks.Single(b => b.Identity == ((Jump)handler.End).Target);
        var writes = body.Statements.OfType<MemoryWrite>().ToArray();
        var merge = handler.Merges.Single(m => m.Result == writes[0].Value);
        checks.True(merge.Inputs.Select(i => i.Value.ConstantValue).SequenceEqual(new BigInteger?[] { 7, 9 }),
            "被调保存值按每条展开边取调用点状态，后续写入不污染前一条边");
        checks.True(writes[1].Value == function.Terms.Concat(function.Terms.Constant(17, 32), function.Terms.Undefined(96))
            && writes[2].Value.Kind == TermKind.Undefined, "部分保存位保持，其余寄存器位未定义");
        checks.True(writes[3].Value == handler.Handler!.Exception && writes[4].Value == handler.Handler.Selector
            && body.End is ResumeUnwind resume && resume.Exception == handler.Handler.Exception,
            "入口值参与语义，继续展开使用当前异常项且不保留调用");
        checks.True(TextDump.Write(function, true) == TextDump.Write(With(code, regions, true).Function!, true), "异常图与发现次序无关");
        var directoryCode = Code(new(Op.Move, R0, Value: 42), new(Op.Call, Value: 902));
        var directory = FunctionLifter.Lift(new Toy(directoryCode), convention,
            new ExceptionFlowFacts(new Facts(), target => target is ImageFunction { EntryOffset: 902 }),
            new(0, 2, FunctionEvidence.SymbolTable), 0).Function!;
        checks.True(directory.Blocks.Any(b => b.End is ResumeUnwind { Exception.ConstantValue: { } value } && value == 42)
            && directory.Blocks.All(b => b.Statements.All(s => s is not Call)), "目录识别的继续展开调用成为终结");
        var plain = With(Code(new(Op.Call, Value: 900), new(Op.Return)), [new(0, 1, null, [])]).Function!;
        checks.True(plain.Blocks.All(b => b.Handler is null) && plain.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single().Unwind is null,
            "没有处理入口的区域不产生展开边");
        var ordinary = With(Code(new(Op.BeginCatch), new(Op.EndCatch), new(Op.Rethrow), new(Op.Return)), []).Function!;
        checks.True(ordinary.Blocks.SelectMany(b => b.Statements).OfType<Call>().Count() == 3, "捕获与重抛入口仍是普通调用");
        var builder = new FunctionBuilder(function.Terms, function.Entry, function.AddressWidth, function.Frame)
        { ImageBase = function.ImageBase, ThreadPointer = function.ThreadPointer, IncomingArgumentArea = function.IncomingArgumentArea };
        builder.Inputs.AddRange(function.Inputs);
        builder.Blocks.AddRange(function.Blocks.Select(b => b.Identity == function.Entry ? b with { End = new Jump(handler.Identity) } : b));
        checks.True(ExitChecker.Check(builder.Freeze()).Violations.Any(v => v.Code == "handler-edge"), "出口拒绝普通跳转进入处理入口");
        var invalidEntry = new FunctionBuilder(function.Terms, handler.Identity, function.AddressWidth, function.Frame)
        { ImageBase = function.ImageBase, ThreadPointer = function.ThreadPointer, IncomingArgumentArea = function.IncomingArgumentArea };
        invalidEntry.Inputs.AddRange(function.Inputs); invalidEntry.Blocks.AddRange(function.Blocks);
        checks.True(ExitChecker.Check(invalidEntry.Freeze()).Violations.Any(v => v.Code == "handler-entry"),
            "出口拒绝从函数入口直接进入处理入口");
        var live = With(Code(new(Op.Move, R3, Value: 7), new(Op.Call, Value: 900), new(Op.Move, R3, Value: 9),
            new(Op.Call, Value: 901), new(Op.Copy, R0, R3), new(Op.Resume)),
            [new(1, 1, 4, clauses), new(3, 1, 4, clauses)]).Function!;
        checks.True(live.Blocks.Single(b => b.Handler is not null).Merges.Length == 1, "只由继续展开使用的合流保持活跃");
        var shared = With(Code(new(Op.Compare, From: R2), new(Op.Branch, Value: 2, Other: 4),
            new(Op.Call, Value: 900), new(Op.Jump, Value: 4), new(Op.Store, From: R0), new(Op.Return)), [new(2, 1, 4, clauses)]).Function!;
        var landing = shared.Blocks.Single(b => b.Handler is not null);
        var common = shared.Blocks.Single(b => b.Identity == ((Jump)landing.End).Target);
        checks.True(ExitChecker.Check(shared).IsValid && common.Handler is null && common.Merges.Length != 0
            && shared.Blocks.Any(b => b.Identity != landing.Identity && b.End is Jump j && j.Target == common.Identity),
            "同地址指令体可经普通流进入，异常入口保持只经展开边进入");
        var different = With(Code(new(Op.Call, Value: 900), new(Op.Call, Value: 901), new(Op.Bad), new(Op.Bad), new(Op.Resume)),
            [new(0, 1, 4, clauses), new(1, 1, 4, [new(ClauseKind.CatchAll, [])])]).Function!;
        checks.True(ExitChecker.Check(different).IsValid && different.Blocks.Count(b => b.Handler is not null) == 2
            && different.Blocks.Where(b => b.Handler is not null).Select(b => b.Handler!.Clauses.Single().Kind).ToHashSet()
                .SetEquals(new[] { ClauseKind.Cleanup, ClauseKind.CatchAll }), "同地址不同子句表各自定义入口，指令体在普通合流处接合");
        var dormant = With(Code(new(Op.Call, Value: 901), new(Op.Call, Value: 900), new(Op.Return),
            new(Op.Store, From: R0), new(Op.Resume)), [new(1, 1, 3, clauses)]);
        checks.True(dormant.Function is not null && ExitChecker.Check(dormant.Function).IsValid
            && dormant.Function.Blocks.SelectMany(b => b.Merges).All(m => !m.Inputs.IsEmpty),
            "没有可达调用点的处理入口仍被提升，局部合流保持不可达分量的定义次序");
        var framed = With(Code(new(Op.Push, From: R3), new(Op.Call, Value: 901), new(Op.Pop, R3), new(Op.Return)),
            [new(1, 1, 2, clauses)]);
        checks.True(framed.Function is not null, "展开边的栈指针保持调用点的帧偏移");
        if (framed.Function is { } frameFunction)
        {
            var state = new Cpp2CS.Kernel.State.StateQueries(); var context = state.CreateContext(frameFunction);
            var read = frameFunction.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>().Single();
            checks.True(context.Get(state.Read, read.Identity) is { IsSuccess: true, Value.Identity: CallerValue { Index: 0 } },
                "状态读取经展开边、异常入口与共用指令体找到调用前的帧写入");
        }
    }
    private sealed class Resolver(Func<ulong, Term, IIndirectContext, IndirectResolution> resolve) : IFlowFacts
    {
        public bool DoesNotReturn(CallTarget target) => false;
        public IndirectResolution ResolveIndirect(ulong address, Term target, IIndirectContext context) => resolve(address, target, context);
    }
    private static void RevisedContracts(Assertions checks)
    {
        LiftResult With(Dictionary<ulong, Ins> code, IFlowFacts? facts = null, RegisterConvention? convention = null) =>
            FunctionLifter.Lift(new Toy(code), convention ?? Convention, facts ?? new Facts(), new(0, code.Keys.Max() + 1, FunctionEvidence.SymbolTable), 0);
        var returnAddress = With(Code(new(Op.Store, From: R0), new(Op.Return)), convention: Convention with { CallerValues = [R3, R0] });
        checks.True(returnAddress.Function!.Blocks.SelectMany(b => b.Statements).OfType<MemoryWrite>().Single().Value.Identity is CallerValue { Index: 1 },
            "返回地址单元按调用方序号进入普通写入，不要求它跨调用保存");
        var framed = With(Code(new(Op.Copy, R3, Sp), new(Op.Push, From: R2), new(Op.Call, Value: 900),
            new(Op.Copy, Sp, R3), new(Op.Return)));
        checks.True(framed.Function is not null, "跨调用保留的帧指针恢复 SP");
        var offset = With(Code(new(Op.Add, Sp, Value: 8), new(Op.Return)), convention: Convention with { ReturnStackOffset = 8 });
        checks.True(With(Code(new Ins(Op.Jump, Value: 900)), convention: Convention with { ReturnStackOffset = 8 }).Function is not null,
            "尾调用不执行返回指令的弹栈");
        checks.True(offset.Function is not null, "返回指令弹栈后的非零约定偏移");
        checks.True(With(Code(new Ins(Op.Return)), convention: Convention with { ReturnStackOffset = 8 }).Failure?.Reason.Code == "stack-restore", "返回偏移必须精确相等");
        checks.True(With(Code(new(Op.Push, From: R3), new(Op.Jump, Value: 900))).Failure is { Address: 1, Reason.Code: "stack-restore" }, "直接尾调用检查 SP");
        var tailFacts = new Resolver((_, target, _) => new IndirectTailCall(target));
        var tail = With(Code(new(Op.Copy, R0, R2), new(Op.Indirect, From: R0)), tailFacts);
        checks.True(tail.Function is not null && tail.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single().Target is ComputedTarget { Value.Identity: EntryAtom }
            && tail.Function.Blocks.Any(b => b.End is Return), "块内接好的间接目标成为尾调用");
        checks.True(With(Code(new(Op.Push, From: R3), new(Op.Indirect, From: R2)), tailFacts).Failure is { Address: 1, Reason.Code: "stack-restore" }, "间接尾调用检查 SP");
        bool readBound = false, followedInput = false;
        var resolver = new Resolver((address, target, context) =>
        {
            if (address == 4)
            {
                var bound = context.Conditions.Single();
                readBound = bound.IsTrue && bound.Condition.Operator is CoreOperator { Operation: CoreOperation.UnsignedLess }
                    && bound.Condition.Operands.Any(t => t.ConstantValue == 2);
                var placeholder = Walk(target).First(t => t.Identity?.StableText.StartsWith("frontend.input.", StringComparison.Ordinal) == true);
                followedInput = context.InUniquePredecessor(placeholder) is not null;
                checks.True(target.Operator is CoreOperator { Operation: CoreOperation.Add }, "解析时已接好前一条指令的目标运算");
                return new IndirectTable(context.InUniquePredecessor(placeholder)!, [new(0, 5)], 7);
            }
            return new IndirectTable(target, [new(0, 7)], 9);
        });
        var code = Code(new(Op.Copy, R0, R2), new(Op.Compare, From: R2, Value: 2), new(Op.Branch, From: C, Value: 3, Other: 9),
            new(Op.Add, R0, Value: 1), new(Op.Indirect, From: R0), new(Op.Copy, R0, R2), new(Op.Indirect, From: R0),
            new(Op.Move, R1, Value: 20), new(Op.Return), new(Op.Move, R1, Value: 30), new(Op.Return));
        var tables = With(code, resolver);
        checks.True(tables.Function is not null && tables.Function.Blocks.Count(b => b.End is JumpTable) == 2, "解析新增块后发现第二个间接跳转");
        checks.True(readBound && followedInput, "解析器实际读取前驱条件、方向和入口占位的来源");
        var partial = With(Code(new(Op.Store, From: V), new(Op.Return)), convention: Convention with { CallerValues = [R3, V], PreservedParts = [new(V, 0, 32)] });
        checks.True(partial.Function is not null && Walk(partial.Function.Blocks.SelectMany(b => b.Statements).OfType<MemoryWrite>().Single().Value)
            .Any(t => t.Identity is CallerValue { Index: 1 })
            && partial.Function.Blocks.SelectMany(b => b.Statements).OfType<MemoryWrite>().Single().Value == partial.Function.Terms.Concat(
                partial.Function.Terms.Slice(partial.Function.Terms.Atom(new CallerValue(1), 128), 0, 32), partial.Function.Terms.Undefined(96)), "入口部分保存的位来自有序调用方值，其余位未定义");
    }
    private static void ConditionalTrap(Assertions checks)
    {
        // 条件陷阱留在块内：条件接到块状态上，其后的写入照常生效，不产生新的块。
        var guarded = Lift(Code(new(Op.Copy, R0, R2), new(Op.Guard, From: R0, Value: 0), new(Op.Move, R1, Value: 5), new(Op.Return)));
        var traps = guarded.Function?.Blocks.SelectMany(b => b.Statements).OfType<TrapWhen>().ToArray() ?? [];
        checks.True(traps.Length == 1 && traps[0].Condition.Operator is CoreOperator { Operation: CoreOperation.Equal }
            && Walk(traps[0].Condition).Any(t => t.Identity is EntryAtom), "条件陷阱的条件是入口值上的项");
        checks.True(guarded.Function!.Blocks.Count(b => b.Statements.Length != 0 || b.End is Return) == 1
            && guarded.Function.Blocks.Any(b => b.End is Return r && r.Results.Single().Value.ConstantValue == 5), "条件陷阱不拆块，其后的语义照常");
        checks.True(TextDump.Write(guarded.Function).Contains("trap ", StringComparison.Ordinal), "文本转储输出条件陷阱");
    }
    private static void PartialPreservation(Assertions checks)
    {
        var convention = Convention with { PreservedParts = [new(V, 0, 32)], CallerValues = [R3, V] };
        var code = Code(new(Op.Move, V, Value: 0x1234), new(Op.Call, Value: 900), new(Op.Store, From: V), new(Op.Return));
        var result = FunctionLifter.Lift(new Toy(code), convention, new Facts(), new(0, 4, FunctionEvidence.SymbolTable), 0);
        checks.True(result.Function is not null && ExitChecker.Check(result.Function).IsValid, "部分保存单元通过出口");
        var function = result.Function!;
        var expected = function.Terms.Concat(function.Terms.Slice(function.Terms.Constant(0x1234, 128), 0, 32), function.Terms.Undefined(96));
        var write = function.Blocks.SelectMany(b => b.Statements).OfType<MemoryWrite>().Single();
        checks.True(write.Value == expected, "调用保留低 32 位并破坏其余 96 位");
    }
    private static void MultipleSlots(Assertions checks)
    {
        var convention = Convention with
        {
            Arguments = [new(R2, new(SlotKind.Integer)), new(V, new(SlotKind.Floating)),
                new(R0, new(SlotKind.IndirectResult), InputRole.IndirectResult)],
            Results = [new(R1, new(SlotKind.Integer)), new(V, new(SlotKind.Floating))]
        };
        var code = Code(new(Op.Call, Value: 900), new(Op.Return));
        var result = FunctionLifter.Lift(new Toy(code), convention, new Facts(), new(0, 2, FunctionEvidence.SymbolTable), 0);
        checks.True(result.Function is not null && ExitChecker.Check(result.Function).IsValid, "整数、浮点、间接结果槽共同归位");
        var function = result.Function!;
        var call = function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single();
        checks.True(call.Arguments.Length == 3 && call.Results.Length == 2 && function.Inputs.Single(i => i.Slot.Kind == SlotKind.IndirectResult).Role == InputRole.IndirectResult,
            "各类槽位和入口角色保持");
        checks.True(call.Results.Select((r, i) => r.Value.Identity is ResultAtom a && a.Definition == call.Identity && a.Index == i).All(x => x), "多个调用结果身份及序号");
        var incoming = function.IncomingArgumentArea!;
        checks.True(incoming.Operands[1].ConstantValue == 16 && call.OutgoingArgumentArea!.Operands[1].ConstantValue == 8,
            "入口栈实参区和调用栈实参区独立偏移");
    }
    private sealed record PrivateAtom : AtomIdentity { public override string StableText => "private"; }
    private static void InternalAtom(Assertions checks)
    {
        var terms = new TermTable(); var id = new BlockIdentity();
        var builder = new FunctionBuilder(terms, id, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
        builder.Blocks.Add(new(id, [], [], new Return([new(new(SlotKind.Integer), terms.Atom(new PrivateAtom(), 64))])));
        checks.True(ExitChecker.Check(builder.Freeze()).Violations.Any(v => v.Code == "atom-vocabulary"), "出口拦截内部原子");
    }
    private static IEnumerable<Term> Walk(Term root)
    {
        var stack = new Stack<Term>(); stack.Push(root); var seen = new HashSet<Term>();
        while (stack.TryPop(out var term))
        {
            if (!seen.Add(term)) continue;
            yield return term;
            foreach (var child in term.Operands) stack.Push(child);
        }
    }
    private static BigInteger Execute(NativeFunction function, ulong argument)
    {
        var values = new Dictionary<Term, BigInteger>();
        var memory = new Dictionary<BigInteger, BigInteger>();
        foreach (var input in function.Inputs) values[input.Value] = argument;
        values[function.Frame.Base] = 4096;
        BigInteger Eval(Term term)
        {
            if (values.TryGetValue(term, out var value)) return value;
            if (term.ConstantValue is { } constant) return constant;
            if (term.Kind == TermKind.Slice) return (Eval(term.Operands[0]) >> term.SliceLow!.Value) & ((BigInteger.One << term.Width) - 1);
            if (term.Kind == TermKind.Concat)
            {
                BigInteger bits = 0; int offset = 0;
                foreach (var child in term.Operands) { bits |= Eval(child) << offset; offset += child.Width; }
                return bits;
            }
            if (term.Operator is CoreOperator op)
            {
                var a = Eval(term.Operands[0]); var b = Eval(term.Operands[1]);
                return op.Operation switch
                {
                    CoreOperation.Add => (a + b) & ((BigInteger.One << term.Width) - 1),
                    CoreOperation.Subtract => (a - b) & ((BigInteger.One << term.Width) - 1),
                    CoreOperation.Equal => a == b ? 1 : 0,
                    CoreOperation.UnsignedLess => a < b ? 1 : 0,
                    _ => throw new InvalidOperationException("检查求值器不支持此运算。")
                };
            }
            throw new InvalidOperationException("读取了无定义的检查值。");
        }
        var blocks = function.Blocks.ToDictionary(b => b.Identity);
        var current = function.Entry; BlockIdentity? previous = null;
        for (int steps = 0; steps < 10000; steps++)
        {
            var block = blocks[current];
            var incoming = block.Merges.Select(m => (m.Result, Value: Eval(m.Inputs.Single(i => i.Predecessor == previous).Value))).ToArray();
            foreach (var (result, value) in incoming) values[result] = value;
            foreach (var statement in block.Statements)
                switch (statement)
                {
                    case MemoryWrite w: memory[Eval(w.Address)] = Eval(w.Value); break;
                    case MemoryRead r: values[r.Result] = memory[Eval(r.Address)]; break;
                    case Call c: foreach (var slot in c.Results) values[slot.Value] = 99; break;
                }
            previous = current;
            switch (block.End)
            {
                case Return r: return Eval(r.Results[0].Value);
                case Jump j: current = j.Target; break;
                case Branch b: current = Eval(b.Condition) != 0 ? b.True : b.False; break;
                case JumpTable t: current = t.Cases.FirstOrDefault(c => c.Value == Eval(t.Selector))?.Target ?? t.Default; break;
                default: throw new InvalidOperationException("检查执行进入不可达。");
            }
        }
        throw new InvalidOperationException("检查执行超过步数预算。");
    }
    private sealed class Synthetic : IInstructionSet
    {
        public ImmutableArray<Register> Registers => FrontendChecks.Registers;
        public DecodeResult Decode(ulong address) => new(new(1, e =>
        {
            var old = e.Read(R1);
            var argument = e.Read(R2);
            var source = address % 5 == 0 ? e.Load(e.Read(Sp), 64) : old;
            if (address % 5 == 4) e.Store(e.Read(Sp), old);
            e.Write(R1, e.Terms.Apply(new CoreOperator(CoreOperation.Add), 64, source, argument));
            if (address == 99_999) e.Return();
            else if (address % 10 == 9) e.Jump(address + 1);
        }), null);
    }
    private static void RealisticScale(Assertions checks)
    {
        // 仅检查程序通过反射统计驻留表，避免为测量扩大原生项的公共接口。
        var phases = new Dictionary<LiftPhase, double>();
        double previous = 0;
        var allocated = GC.GetAllocatedBytesForCurrentThread();
        var timer = Stopwatch.StartNew();
        var result = FunctionLifter.Lift(new Synthetic(), Convention, new Facts(), new(0, 100_000, FunctionEvidence.SymbolTable), 0, phaseCompleted: phase =>
            {
                var now = timer.Elapsed.TotalMilliseconds;
                phases[phase] = phases.GetValueOrDefault(phase) + now - previous;
                previous = now;
            });
        timer.Stop();
        allocated = GC.GetAllocatedBytesForCurrentThread() - allocated;
        checks.True(result.Function is not null && result.Function.Blocks.Length == 10_001, "十万指令、一万机器块及独立入口通过出口");
        var table = (System.Collections.IDictionary)typeof(TermTable).GetField("terms", System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic)!.GetValue(result.Function!.Terms)!;
        var contains = new Dictionary<Term, bool>();
        int placeholders = 0, composites = 0;
        foreach (Term term in table.Values)
        {
            bool input = term.Identity?.StableText.StartsWith("frontend.input.", StringComparison.Ordinal) == true;
            bool nested = term.Operands.Any(t => contains[t]);
            contains.Add(term, input || nested);
            if (input) placeholders++;
            else if (nested) composites++;
        }
        Console.WriteLine($"前端合成测量：100000 指令，10000 机器块，{timer.Elapsed.TotalMilliseconds:F1} ms，{timer.Elapsed.TotalMicroseconds / 100000:F2} us/指令；驻留 {table.Count} 项，占位 {placeholders} ({100.0 * placeholders / table.Count:F2}%)，含占位的复合项 {composites} ({100.0 * composites / table.Count:F2}%)，合计 {100.0 * (placeholders + composites) / table.Count:F2}%");
        Console.WriteLine($"前端阶段：{string.Join(", ", phases.Select(p => $"{p.Key}={p.Value:F1} ms"))}；分配 {allocated:N0} B");
    }
    private static void Scale(Assertions checks)
    {
        var code = new Dictionary<ulong, Ins>();
        const int groups = 1200;
        for (int g = 0; g < groups; g++)
        {
            ulong start = (ulong)(g * 10);
            code[start] = new(Op.Move, R1, Value: (ulong)g);
            for (ulong i = 1; i < 8; i++) code[start + i] = new(Op.Add, R1, Value: i);
            code[start + 8] = new(Op.Compare, From: R2, Value: (ulong)g);
            code[start + 9] = new(Op.Branch, Value: start + 10, Other: start + 20);
        }
        code[12000] = new(Op.Return); code[12010] = new(Op.Return);
        _ = Lift(Code(new(Op.Move, R1), new(Op.Return)));
        var before = GC.GetAllocatedBytesForCurrentThread(); var timer = Stopwatch.StartNew();
        var result = Lift(code); timer.Stop(); var bytes = GC.GetAllocatedBytesForCurrentThread() - before;
        checks.True(result.Function is not null && ExitChecker.Check(result.Function).IsValid, "规模产物通过出口");
        checks.True(timer.Elapsed.TotalSeconds < 1, "12002 条指令提升及 SSA（含出口）小于一秒");
        before = GC.GetAllocatedBytesForCurrentThread(); var large = Lift(code, extra: 4096);
        var largeBytes = GC.GetAllocatedBytesForCurrentThread() - before;
        checks.True(large.Function is not null && largeBytes - bytes < 4_000_000, "4096 个未使用寄存器不产生逐块矩阵");
        Console.WriteLine($"前端规模：{code.Count} 条指令，{result.Function?.Blocks.Length} 块，{timer.Elapsed.TotalMilliseconds:F1} ms，分配 {bytes:N0} B；增加 4096 寄存器后 {largeBytes:N0} B");
    }
}
