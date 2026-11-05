using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Calls;

/// <summary>调用点的形状：可能的托管目标及其机器签名。运行时操作没有托管签名。</summary>
public sealed record CallShape(Call Call, IReadOnlyList<MethodRef> Candidates, MachineSignature? Signature)
{
    /// <summary>被调方机器码不读取的输入寄存器：原生代码对这些位置的 IL 实参没有约束。</summary>
    public IReadOnlySet<Storage> Unused { get; init; } = new HashSet<Storage>();
    /// <summary>经运行时分派的托管调用：按托管签名传参，以 callvirt 调用。</summary>
    public bool IsDispatch => Call.Op?.Kind is OpKind.CallVirtual or OpKind.CallInterface or OpKind.CallDelegate or OpKind.CallGenericVirtual;
    public bool IsRuntime => Call.Op is not null && !IsDispatch
        && !(Call.Op.Kind is OpKind.CallMethodPointer or OpKind.InvokeGeneric && Candidates.Count == 1);
}

/// <summary>
/// 按事实解析调用目标。直接调用的地址可能被多个方法共用（相同代码折叠），候选全部保留，由类型约束选择；
/// 候选的机器签名不一致时签名为 null。
/// </summary>
public sealed class CallShapes(ProgramFacts facts, ManagedAbi abi, Func<ulong, Storage, bool> unused)
{
    public ProgramFacts Facts => facts;
    private readonly Dictionary<ulong, (MethodRef[] Candidates, MachineSignature? Signature)> direct = [];

    public CallShape Of(Call call)
    {
        if (call.Op is { Kind: OpKind.InvokeGeneric, Operand: MethodRef invoked })
            return new(call, [invoked], abi.Invoker(invoked));
        if (call.Resolved is { } resolved)
            return new(call, [resolved], abi.Machine(resolved, out _));
        if (call.Op is { Operand: MethodRef method } && call.Op.Kind is OpKind.CallGenericVirtual or OpKind.InvokeGeneric or OpKind.InvokeConstrainedGeneric or OpKind.CallMethodPointer)
            return new(call, [method], abi.Machine(method, out _));
        if (call is { Op: null, Kind: CallKind.Direct or CallKind.Tail, Target: Const target })
        {
            var (candidates, signature) = Direct(target.Value);
            if (signature is null && Named(call) is var (named, namedSignature))
                (candidates, signature) = ([named], namedSignature);
            var ignored = signature?.Arguments.SelectMany(a => a.Pieces).Select(p => p.Register)
                .Where(r => r.Bank is Bank.Gpr or Bank.Vec && unused(target.Value, r)).ToHashSet() ?? [];
            return new(call, candidates, signature) { Unused = ignored };
        }
        return new(call, [], null);
    }

    private (MethodRef[], MachineSignature?) Direct(ulong address)
    {
        if (direct.TryGetValue(address, out var known)) return known;
        var candidates = facts.EntriesAt(address)
            .Where(e => e.Kind is EntryKind.Method or EntryKind.GenericMethod && e.Method is not null)
            .Select(e => e.Method!).Distinct().ToArray();
        if (candidates.Length == 0 && facts.AdjustorTargets.At(address) is { } adjusted) candidates = [adjusted.Method];
        // 未登记在方法指针表中的方法：事实层由调用证据推断出定义，实例取自见证。
        if (candidates.Length == 0 && facts.Unregistered.At(address) is { } inferred)
            candidates = inferred.Witnesses.Select(w => w.Instance).Distinct().DefaultIfEmpty(new MethodRef(inferred.Definition, [], [])).ToArray();
        var signatures = candidates.Select(c => abi.Machine(c, out _)).ToArray();
        var signature = signatures.Length > 0 && signatures.All(s => s is not null && SameShape(s, signatures[0]!)) ? signatures[0] : null;
        return direct[address] = (candidates, signature);
    }

    /// <summary>
    /// 共享泛型代码的调用传入确切实例的 MethodInfo：某个实参是方法实体，且该方法签名的 MethodInfo 正落在这个实参的寄存器上时，
    /// 它就是被调用的方法（共享实例未登记在入口表中时由此得到签名）。
    /// </summary>
    private (MethodRef, MachineSignature)? Named(Call call)
    {
        for (var i = 0; i < call.Arguments.Length && i < call.Sources.Length; i++)
            if (call.Arguments[i] is Symbol { Kind: SymbolKind.Method, Value: MethodRef method }
                && abi.Machine(method, out _) is { MethodInfo: { } info } signature && info.Register == call.Sources[i])
                return (method, signature);
        return null;
    }

    /// <summary>直接调用目标的各候选及其机器签名（检查用）。</summary>
    public IEnumerable<(MethodRef Method, MachineSignature? Signature, string? Problem)> Candidates(ulong address) =>
        Direct(address).Item1.Select(c => (c, abi.Machine(c, out var problem), problem));

    /// <summary>两个签名占用相同的机器位置并有相同的内存效果。</summary>
    private static bool SameShape(MachineSignature a, MachineSignature b) =>
        a.Arguments.Length == b.Arguments.Length && a.Arguments.Zip(b.Arguments).All(p => Same(p.First, p.Second))
        && (a.Return is null) == (b.Return is null) && (a.Return is null || Same(a.Return, b.Return!))
        && a.MethodInfo == b.MethodInfo;

    private static bool Same(MachineValue a, MachineValue b) => a.Index == b.Index && a.Transfer == b.Transfer && a.Size == b.Size
        && a.Access == b.Access && a.Pieces.AsSpan().SequenceEqual(b.Pieces);
}
