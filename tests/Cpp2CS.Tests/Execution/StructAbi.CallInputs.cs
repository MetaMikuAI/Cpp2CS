using Cpp2CS.Facts;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Lifting;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests.Execution;

internal sealed partial class StructAbi
{
    private readonly FunctionLifter inputLifter = new(index.Facts);
    private readonly Dictionary<MethodRef, int[]> unusedInputs = new();
    private readonly Dictionary<ulong, HashSet<Storage>?> nativeInputReads = new();

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
            if (types.Any(t => index.Types.Kind(t) is not
                (TypeKind.Reference or TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Struct))) return [];
            var signature = Signature(method);
            var offsets = new int[types.Length];
            var total = 0;
            for (var i = 0; i < types.Length; i++)
            {
                offsets[i] = total;
                total += Classifier.Leaves(types[i]).Length;
            }
            if (total != arguments.Length) return [];
            var reads = NativeInputReads(definition.Address);
            if (reads is null) return [];
            return Arguments(signature).Select((location, i) => (location, i))
                .Where(p => index.Types.Kind(types[p.i]) != TypeKind.Struct
                    && p.location is { StackOffset: null, Indirect: false, Pieces: [var piece] }
                    && !reads.Contains(piece.Register)).Select(p => offsets[p.i]).ToArray();
        }
    }

    // 固定目标的转传输入逐层核对原始 SSA；递归与未知身份均不能证明未用。
    private HashSet<Storage>? NativeInputReads(ulong entry)
    {
        if (nativeInputReads.TryGetValue(entry, out var cached)) return cached;
        nativeInputReads[entry] = null;
        var methods = index.Facts.EntriesAt(entry).Select(e => e.Method).OfType<MethodRef>().Distinct().ToArray();
        if (methods.Length == 0 || methods.Any(m => m.Method.IsVirtual || m.Method.GenericParameters.Count != 0
            || m.Method.Owner.GenericParameters.Count != 0 || Side.IsGenericInstance(m)
            || m.Method.Address != entry && m.Method.Address != 0)) return null;
        var returned = methods.SelectMany(m => Signature(m).Return?.Pieces ?? []).Distinct()
            .Select(p => (Expr)new Read(p.Register, p.Width)).ToArray();
        var lifted = inputLifter.Lift(entry, returned.Length == 0 ? null : new Intrinsic("return", returned, 64), simplify: false);
        var tails = InterfaceTailProof.Find(lifted.Function, c => c is { Kind: CallKind.Direct or CallKind.Tail, Target: Const target }
            && index.Facts.Helpers.At(target.Value)?.Kind == HelperKind.InterfaceLookup && index.Facts.Code.RegionOf(target.Value) != CodeRegion.Managed);
        return nativeInputReads[entry] = NativeInputs.Reads(lifted,
            (call, register) => call is { Op: null, Kind: CallKind.Direct or CallKind.Tail, Target: Const target }
                && NativeInputReads(target.Value) is { } inputs && !inputs.Contains(register), tails.Contains);
    }
}
