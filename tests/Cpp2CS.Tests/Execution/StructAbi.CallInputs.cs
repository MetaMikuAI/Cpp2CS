using Cpp2CS.Ir;
using Cpp2CS.Lifting;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests.Execution;

internal sealed partial class StructAbi
{
    private readonly FunctionLifter inputLifter = new(index.Facts);
    private readonly Dictionary<MethodRef, int[]> unusedInputs = new();

    // 调用事件只规范化被调原生代码完全不读的标量寄存器输入。
    // 证据来自未化简机器 SSA 和独立 ABI，不能取自恢复体；实参求值、调用及内存比较不变。
    public ulong[] CallInputs(MethodRef method, ulong[] arguments)
    {
        if (!unusedInputs.TryGetValue(method, out var unused))
        {
            unused = FindUnused();
            unusedInputs.Add(method, unused);
        }
        if (unused.Length == 0) return arguments;
        var observed = (ulong[])arguments.Clone();
        foreach (var i in unused) observed[i] = 0;
        return observed;

        int[] FindUnused()
        {
            var definition = method.Method;
            if (definition.Address == 0 || definition.IsVirtual || definition.GenericParameters.Count != 0
                || definition.Owner.GenericParameters.Count != 0 || Side.IsGenericInstance(method)) return [];
            var types = ArgumentTypes(method);
            if (types.Length != arguments.Length || types.Any(t => index.Types.Kind(t) is not
                (TypeKind.Reference or TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double))) return [];
            var signature = Signature(method);
            Expr? returned = signature.Return is not { } value ? null
                : new Intrinsic("return", value.Pieces.Select(p => (Expr)new Read(p.Register, p.Width)).ToArray(), 64);
            var reads = NativeInputs.Reads(inputLifter.Lift(definition.Address, returned, simplify: false));
            if (reads is null) return [];
            return Arguments(signature).Select((location, i) => (location, i))
                .Where(p => p.location is { StackOffset: null, Indirect: false, Pieces: [var piece] }
                    && !reads.Contains(piece.Register)).Select(p => p.i).ToArray();
        }
    }
}
