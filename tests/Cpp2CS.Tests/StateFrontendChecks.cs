using System.Collections.Immutable;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Tests;

internal static class StateFrontendChecks
{
    // 与 FrontendChecks 一样，每条玩具指令直接调用公共发射接口。
    private static readonly Register Saved = new("saved", 64), Sp = new("stack", 64), Fp = new("frame", 64), Wide = new("wide", 128), Result = new("result", 64);
    private sealed class Toy(ImmutableArray<Action<IEmitter>> code) : IInstructionSet
    {
        public ImmutableArray<Register> Registers => [Saved, Sp, Fp, Wide, Result];
        public DecodeResult Decode(ulong address) => new(new(1, code[(int)address]), null);
    }
    private sealed class Facts : IFlowFacts
    {
        public bool DoesNotReturn(CallTarget target) => false;
        public IndirectResolution ResolveIndirect(ulong address, Term target, IIndirectContext context) => new IndirectUnknown(new("test.indirect", "用例不含间接跳转。"));
    }
    public static void Check(Assertions a)
    {
        Term Add(IEmitter e, Term value, ulong n) => e.Terms.Apply(new CoreOperator(CoreOperation.Add), 64, value, e.Terms.Constant(n, 64));
        ImmutableArray<Action<IEmitter>> code = [
            e => e.Write(Fp, e.Read(Sp)),
            e => e.Store(Add(e, e.Read(Sp), 16), e.Read(Saved)),
            e => e.Store(Add(e, e.Read(Sp), 32), e.Read(Wide)),
            e => e.Write(Sp, e.Terms.Apply(new CoreOperator(CoreOperation.Subtract), 64, e.Read(Sp), e.Terms.Constant(64, 64))),
            e => e.Call(new ImageFunction(100)),
            e => e.Write(Sp, e.Read(Fp)),
            e => e.Write(Saved, e.Load(Add(e, e.Read(Sp), 16), 64)),
            e => e.Write(Wide, e.Load(Add(e, e.Read(Sp), 32), 128)),
            e => e.Write(Result, e.Terms.Constant(0, 64)),
            e => e.Return()
        ];
        var convention = new RegisterConvention([], [new(Result, new(SlotKind.Integer))], [Saved, Fp], Sp, 0, 0, [Saved, Fp, Wide])
        { PreservedParts = [new(Wide, 0, 32)] };
        var lifted = FunctionLifter.Lift(new Toy(code), convention, new Facts(), new(0, (ulong)code.Length, FunctionEvidence.SymbolTable), 0);
        a.True(lifted.Function is not null, "保存恢复与帧指针恢复 SP 提升成功");
        if (lifted.Function is not { } f) throw new InvalidOperationException(lifted.Failure?.ToString());
        var q = new StateQueries(); var c = q.CreateContext(f); var reads = f.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>().ToArray();
        var restored = c.Get(q.Read, reads[0].Identity);
        a.True(restored.IsSuccess && restored.Value == f.Terms.Atom(new CallerValue(0), 64), "保存的寄存器跨调用读回调用方值");
        var partial = c.Get(q.Read, reads[1].Identity);
        a.True(partial.IsSuccess && partial.Value == f.Terms.Concat(f.Terms.Slice(f.Terms.Atom(new CallerValue(2), 128), 0, 32), f.Terms.Undefined(96)), "部分保存位与未定义位恢复");
        var uses = c.Get(q.CallerUses, 0);
        a.True(uses.IsSuccess && uses.Value.IsEmpty, "序言尾声没有可观察的调用方值使用");
    }
}
