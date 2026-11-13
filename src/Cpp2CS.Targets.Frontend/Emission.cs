using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Targets.Frontend;

internal abstract record Transfer;
internal sealed record Direct(ulong Target) : Transfer;
internal sealed record Conditional(Term Condition, ulong Yes, ulong No) : Transfer;
internal sealed record TableTransfer(IndirectTable Resolution) : Transfer;
internal sealed record Indirect(Term Target) : Transfer;
internal sealed record Finished(Terminator End) : Transfer;

internal sealed class Emission(ulong address, TermTable terms, ImmutableArray<Register> registers,
    RegisterConvention convention, IFlowFacts facts, IExceptionModel? exceptionModel = null, bool captureUnwind = false,
    Func<CallTarget, CallTargetResolution>? resolveCallTarget = null) : IEmitter, IOrderedMemoryEmitter, IExclusiveMemoryEmitter
{
    internal Dictionary<Register, Term> State { get; } = [];
    internal List<Statement> Statements { get; } = [];
    internal Dictionary<CallIdentity, Dictionary<Register, Term>> UnwindStates { get; } = [];
    internal Transfer? End { get; private set; }
    internal Reason? Failure { get; private set; }
    public TermTable Terms => terms;
    private int Width => convention.StackPointer.Width;
    private void Open()
    {
        if (End is not null) throw new InvalidOperationException("终结后不能继续发射。");
    }
    private void Own(Term value)
    {
        if (value.Table != terms) throw new ArgumentException("值必须来自本函数项表。");
    }
    private void Register(Register register)
    {
        if (!registers.Contains(register)) throw new ArgumentException("寄存器不在目标文件中。");
    }
    public Term Read(Register register)
    {
        Open(); Register(register);
        if (!State.TryGetValue(register, out var value))
            State.Add(register, value = terms.Atom(new RegisterInput(address, register), register.Width));
        return value;
    }
    public void Write(Register register, Term value)
    {
        Open(); Register(register); Own(value);
        if (value.Width != register.Width) throw new ArgumentException("写入必须覆盖完整存储单元。");
        State[register] = value;
    }
    public Term Load(Term pointer, int width) => Load(pointer, width, false);
    public Term LoadAcquire(Term pointer, int width) => Load(pointer, width, true);
    private Term Load(Term pointer, int width, bool acquire)
    {
        Open(); Own(pointer);
        var id = new ReadIdentity();
        var result = terms.Atom(new ResultAtom(id), width);
        Statements.Add(new MemoryRead(id, pointer, width, result) { Acquire = acquire, Trace = new(address) });
        return result;
    }
    public void Store(Term pointer, Term value) => Store(pointer, value, false);
    public void StoreRelease(Term pointer, Term value) => Store(pointer, value, true);
    private void Store(Term pointer, Term value, bool release)
    {
        Open(); Own(pointer); Own(value);
        Statements.Add(new MemoryWrite(new WriteIdentity(), pointer, value.Width, value) { Release = release, Trace = new(address) });
    }
    public Term LoadExclusive(Term pointer, int width, bool acquire)
    {
        Open(); Own(pointer);
        var id = new ExclusiveIdentity();
        var result = terms.Atom(new ResultAtom(id), width);
        Statements.Add(new ExclusiveRead(id, pointer, width, result, acquire) { Trace = new(address) });
        return result;
    }
    public Term StoreExclusive(Term pointer, Term value, bool release)
    {
        Open(); Own(pointer); Own(value);
        var id = new ExclusiveIdentity();
        var status = terms.Atom(new ResultAtom(id), 32);
        Statements.Add(new ExclusiveWrite(id, pointer, value.Width, value, status, release) { Trace = new(address) });
        return status;
    }
    public void ClearExclusive()
    {
        Open();
        Statements.Add(new ExclusiveClear(new()) { Trace = new(address) });
    }
    public void Fence(string domain, FenceOrdering ordering)
    {
        Open();
        Statements.Add(new MemoryFence(new(), domain) { Ordering = ordering, Trace = new(address) });
    }
    public void TrapIf(Term condition)
    {
        Open(); Own(condition);
        if (condition.Width != 1) throw new ArgumentException("陷阱条件必须是 1 位。");
        Statements.Add(new TrapWhen(new TrapIdentity(), condition) { Trace = new(address) });
    }
    public void Call(CallTarget target)
    {
        Open();
        if (resolveCallTarget is not null)
        {
            var resolution = resolveCallTarget(target);
            if (resolution.Failure is { } failure) { Fail(failure); return; }
            target = resolution.Target ?? throw new InvalidOperationException("调用目标解析未提供目标或失败原因。");
        }
        if (exceptionModel is not null && (exceptionModel.IsResumeUnwind(target) || facts.ResumesUnwind(target)))
        {
            End = new Finished(new ResumeUnwind(exceptionModel.ResumeException(this)));
            return;
        }
        var id = new CallIdentity();
        if (captureUnwind)
            UnwindStates.Add(id, convention.Preserved.Concat(convention.PreservedParts.Select(p => p.Register))
                .Append(convention.StackPointer).Distinct().ToDictionary(r => r, r =>
                    convention.PreservedParts.Any(p => p.Register == r)
                        ? RegisterValues.KeepParts(terms, r, Read(r), convention.PreservedParts) : Read(r)));
        var arguments = convention.Arguments.Select(s => new SlotValue(s.Slot, Read(s.Register))).ToImmutableArray();
        var area = Offset(Read(convention.StackPointer), convention.OutgoingAreaOffset);
        var noReturn = facts.DoesNotReturn(target);
        var results = noReturn ? [] : convention.Results.Select((s, i) =>
            new SlotValue(s.Slot, terms.Atom(new ResultAtom(id, i), s.Register.Width))).ToImmutableArray();
        Statements.Add(new Call(id, target, arguments, results, noReturn, OutgoingArgumentArea: area) { Trace = new(address) });
        foreach (var register in registers)
            if (register != convention.StackPointer && !convention.Preserved.Contains(register))
                State[register] = convention.PreservedParts.Any(p => p.Register == register)
                    ? RegisterValues.KeepParts(terms, register, Read(register), convention.PreservedParts)
                    : terms.Undefined(register.Width);
        for (int i = 0; i < results.Length; i++) State[convention.Results[i].Register] = results[i].Value;
        if (noReturn) End = new Finished(new Unreachable());
    }
    public void Jump(ulong target) { Open(); End = new Direct(target); }
    public void Branch(Term condition, ulong whenTrue, ulong whenFalse)
    {
        Open(); Own(condition);
        if (condition.Width != 1) throw new ArgumentException("分支条件必须为一位。");
        End = new Conditional(condition, whenTrue, whenFalse);
    }
    public void IndirectJump(Term target)
    {
        Open(); Own(target);
        End = new Indirect(target);
    }

    public void Return()
    {
        Open();
        var results = convention.Results.Select(s => new SlotValue(s.Slot, Read(s.Register))).ToImmutableArray();
        End = new Finished(new Return(results));
    }
    public void Trap() { Open(); End = new Finished(new Unreachable()); }
    public Term ImageAddress(ulong offset) => Offset(terms.Atom(new RootAtom(AddressRoot.Image), Width), offset);
    public Term ThreadPointer => terms.Atom(new RootAtom(AddressRoot.Thread), Width);
    public void Fail(Reason reason) => Failure ??= reason;
    private Term Offset(Term basis, BigInteger offset) => offset.IsZero ? basis : terms.Apply(new CoreOperator(CoreOperation.Add),
        basis.Width, basis, terms.Constant((offset % (BigInteger.One << basis.Width) + (BigInteger.One << basis.Width)) % (BigInteger.One << basis.Width), basis.Width));
}

/// <summary>统一替换项 DAG 与程序操作数；显式栈避免长表达式耗尽调用栈。</summary>
internal sealed class TermRewrite(TermTable terms, Func<Term, Term?> replace, bool followReplacement = false)
{
    private readonly Dictionary<Term, Term> cache = [];
    internal Term Map(Term root)
    {
        var todo = new Stack<(Term Value, bool Ready)>();
        todo.Push((root, false));
        while (todo.TryPop(out var item))
        {
            var term = item.Value;
            if (cache.ContainsKey(term)) continue;
            if (replace(term) is { } replacement && replacement != term)
            {
                if (!followReplacement) { cache[term] = replacement; continue; }
                if (cache.TryGetValue(replacement, out var mapped)) cache[term] = mapped;
                else { todo.Push((term, true)); todo.Push((replacement, false)); }
                continue;
            }
            if (term.Operands.IsEmpty) { cache[term] = term; continue; }
            if (!item.Ready)
            {
                todo.Push((term, true));
                foreach (var child in term.Operands) if (!cache.ContainsKey(child)) todo.Push((child, false));
                continue;
            }
            var operands = term.Operands.Select(t => cache[t]).ToArray();
            cache[term] = term.Kind switch
            {
                TermKind.Operation => terms.Apply(term.Operator!, term.Width, operands),
                TermKind.Slice => terms.Slice(operands[0], term.SliceLow!.Value, term.Width),
                TermKind.Concat => terms.Concat(operands),
                _ => throw new InvalidOperationException("未知的项结构。")
            };
        }
        return cache[root];
    }
    internal Statement Statement(Statement statement) => statement switch
    {
        ExclusiveRead r => r with { Address = Map(r.Address) },
        ExclusiveWrite w => w with { Address = Map(w.Address), Value = Map(w.Value) },
        ExclusiveClear or MemoryFence => statement,
        MemoryRead r => r with { Address = Map(r.Address) },
        MemoryWrite w => w with { Address = Map(w.Address), Value = Map(w.Value) },
        TrapWhen t => t with { Condition = Map(t.Condition) },
        Call c => c with
        {
            Target = c.Target is ComputedTarget t ? new ComputedTarget(Map(t.Value)) : c.Target,
            Arguments = Slots(c.Arguments), OutgoingArgumentArea = c.OutgoingArgumentArea is { } a ? Map(a) : null
        },
        _ => throw new InvalidOperationException("尚未支持的前端语句。")
    };
    internal ImmutableArray<SlotValue> Slots(ImmutableArray<SlotValue> slots) => slots.Select(s => s with { Value = Map(s.Value) }).ToImmutableArray();
    internal Terminator End(Terminator end) => end switch
    {
        Branch b => b with { Condition = Map(b.Condition) },
        JumpTable t => t with { Selector = Map(t.Selector) },
        Return r => r with { Results = Slots(r.Results) },
        ResumeUnwind r => r with { Exception = Map(r.Exception) },
        _ => end
    };
    internal Transfer Transfer(Transfer transfer) => transfer switch
    {
        Indirect i => i with { Target = Map(i.Target) },
        Conditional c => c with { Condition = Map(c.Condition) },
        TableTransfer t => t with { Resolution = t.Resolution with { Selector = Map(t.Resolution.Selector) } },
        Finished f => f with { End = End(f.End) },
        _ => transfer
    };
}

/// <summary>保存位段只是单元内的位搬运，不产生子寄存器存储。</summary>
internal static class RegisterValues
{
    internal static Term KeepParts(TermTable terms, Register register, Term source, ImmutableArray<PreservedPart> parts)
    {
        var pieces = new List<Term>();
        int position = 0;
        foreach (var part in parts.Where(p => p.Register == register).OrderBy(p => p.Low))
        {
            if (part.Low > position) pieces.Add(terms.Undefined(part.Low - position));
            pieces.Add(terms.Slice(source, part.Low, part.Width));
            position = part.Low + part.Width;
        }
        if (position < register.Width) pieces.Add(terms.Undefined(register.Width - position));
        return terms.Concat(pieces.ToArray());
    }
}
