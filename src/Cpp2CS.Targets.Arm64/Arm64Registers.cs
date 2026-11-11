using System.Collections.Immutable;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Targets.Arm64;

public static class Arm64Registers
{
    public static ImmutableArray<Register> X { get; } = [.. Enumerable.Range(0, 31).Select(i => new Register($"x{i}", 64))];
    public static Register Sp { get; } = new("sp", 64);
    public static ImmutableArray<Register> V { get; } = [.. Enumerable.Range(0, 32).Select(i => new Register($"v{i}", 128))];
    public static Register N { get; } = new("n", 1);
    public static Register Z { get; } = new("z", 1);
    public static Register C { get; } = new("c", 1);
    public static Register Overflow { get; } = new("v", 1);
    public static ImmutableArray<Register> All { get; } = [.. X, Sp, .. V, N, Z, C, Overflow];
    // 调用方序号：x19–x29、v8–v15 的保存部分、x30。
    public static RegisterConvention Convention { get; } = new(
        [.. Enumerable.Range(0, 8).Select(i => new RegisterSlot(X[i], new(SlotKind.Integer, i))),
         .. Enumerable.Range(0, 8).Select(i => new RegisterSlot(V[i], new(SlotKind.Floating, i))),
         new(X[8], new(SlotKind.IndirectResult), InputRole.IndirectResult)],
        [.. Enumerable.Range(0, 2).Select(i => new RegisterSlot(X[i], new(SlotKind.Integer, i))),
         .. Enumerable.Range(0, 4).Select(i => new RegisterSlot(V[i], new(SlotKind.Floating, i)))],
        X.Skip(19).Take(11).ToImmutableHashSet(), Sp, 0, 0,
        [.. X.Skip(19).Take(11), .. V.Skip(8).Take(8), X[30]])
    {
        PreservedParts = [.. V.Skip(8).Take(8).Select(r => new PreservedPart(r, 0, 64))]
    };
}

public sealed class Arm64FlowFacts(Func<CallTarget, bool>? doesNotReturn = null) : IFlowFacts
{
    public bool DoesNotReturn(CallTarget target) => doesNotReturn?.Invoke(target) ?? false;
    public IndirectResolution ResolveIndirect(ulong address, Term target, IIndirectContext context)
    {
        if (context.Image is { } image && image.IsExecutable(address, 4)
            && (image.ReadUnsigned(address, 4) & 0xfffffc1f) == 0xd65f0000)
            return new IndirectUnknown(new("arm64.indirect-ret", "非默认寄存器 RET 尚未证明为返回。"));
        return IndirectResolver.Resolve(target, context);
    }
}
