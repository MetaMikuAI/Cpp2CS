using Cpp2CS.Ir;
using Cpp2CS.Idioms;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Facts.Derived;

/// <summary>按恢复器实例缓存的原生输入证明；递归中的结果保持未知。</summary>
internal sealed class NativeCalleeFacts(ProgramFacts facts, bool recoverUnusedInputs)
{
    private readonly ManagedAbi abi = new(facts.Layouts);
    private readonly Cpp2CS.Machine.Lifting.FunctionLifter inputLifter = new(facts);
    internal readonly Dictionary<ulong, HashSet<Storage>?> nativeInputs = new();
    internal readonly Dictionary<ulong, bool> unusedResultBuffers = new();

    internal bool UnusedResultBuffer(ulong entry)
    {
        if (!unusedResultBuffers.TryGetValue(entry, out var unused))
        {
            var convention = inputLifter.Machine.Convention;
            // 未知签名保留全部可能的返回寄存器，x8 只承担间接返回地址，不是托管参数寄存器。
            var returned = convention.IntegerResults.Concat(convention.FloatResults)
                .Select(r => (Expr)new Read(r, r.Bank == Bank.Vec ? 128 : 64)).ToArray();
            var reads = Cpp2CS.Machine.Lifting.NativeInputs.Reads(inputLifter.Lift(entry, new Intrinsic("return", returned, 64), simplify: false));
            unused = convention.IndirectResult is { } buffer && reads is not null && !reads.Contains(buffer);
            unusedResultBuffers.Add(entry, unused);
        }
        return unused;
    }

    internal bool UnusedInput(ulong entry, Storage register)
    {
        if (!nativeInputs.TryGetValue(entry, out var reads))
        {
            // 递归调用暂不证明未用；后续只缓存完整分析的结果。
            nativeInputs.Add(entry, null);
            var methods = facts.EntriesAt(entry).Select(e => e.Method).OfType<MethodRef>().ToArray();
            reads = null;
            if (methods.Length > 0 && methods.All(m => (m.Method.Address == entry || m.Method.Address == 0)
                && !m.TypeArguments.Concat(m.MethodArguments).Any(FieldLayouts.IsFullyShared)))
            {
                var signatures = methods.Select(m => abi.Classify(m, out _)).ToArray();
                if (signatures.All(s => s is not null))
                {
                    // 同地址的多个所有者取返回寄存器并集，不能把另一签名的返回输入误判为未用。
                    var returned = signatures.SelectMany(s => s!.Return?.Pieces ?? []).Distinct()
                        .Select(p => (Expr)new Read(p.Register, p.Width)).ToArray();
                    var lifted = inputLifter.Lift(entry, returned.Length == 0 ? null : new Intrinsic("return", returned, 64), simplify: false);
                    var delegates = recoverUnusedInputs ? DelegateCallNormalizer.InputReads(facts, lifted.Function) : [];
                    var interfaceTails = InterfaceTailProof.Find(lifted.Function, call => call is { Kind: CallKind.Direct or CallKind.Tail, Target: Const target } && facts.Code.RegionOf(target.Value) != CodeRegion.Managed && facts.Helpers.At(target.Value)?.Kind == HelperKind.InterfaceLookup);
                    // 委托尾跳转沿用完整布局与 Invoke ABI 证明；原始字段读取仍参与入口依赖分析。
                    reads = Cpp2CS.Machine.Lifting.NativeInputs.Reads(lifted,
                        recoverUnusedInputs ? (call, input) => delegates.TryGetValue(call, out var used) ? !used.Contains(input)
                            : call is { Op: null, Kind: CallKind.Direct or CallKind.Tail, Target: Const target } && UnusedInput(target.Value, input) : null,
                        call => delegates.ContainsKey(call) || interfaceTails.Contains(call));
                }
            }
            nativeInputs[entry] = reads;
        }
        return reads is not null && !reads.Contains(register);
    }

    internal CallingConvention Convention => inputLifter.Machine.Convention;
}
