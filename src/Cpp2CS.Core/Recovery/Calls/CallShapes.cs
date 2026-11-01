using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Calls;

/// <summary>调用点的形状：可能的托管目标及其机器签名。运行时操作没有托管签名。</summary>
public sealed record CallShape(Call Call, IReadOnlyList<MethodRef> Candidates, MachineSignature? Signature)
{
    public bool IsRuntime => Call.Op is not null;
}

/// <summary>
/// 按事实解析调用目标。直接调用的地址可能被多个方法共用（相同代码折叠），候选全部保留，由类型约束选择；
/// 候选的机器签名不一致时签名为 null。
/// </summary>
public sealed class CallShapes(ProgramFacts facts, ManagedAbi abi)
{
    private readonly Dictionary<ulong, (MethodRef[] Candidates, MachineSignature? Signature)> direct = [];

    public CallShape Of(Call call)
    {
        if (call.Op is { Operand: MethodRef method } && call.Op.Kind is OpKind.CallGenericVirtual or OpKind.InvokeGeneric or OpKind.InvokeConstrainedGeneric)
            return new(call, [method], abi.Machine(method, out _));
        if (call is { Op: null, Kind: CallKind.Direct or CallKind.Tail, Target: Const target })
        {
            var (candidates, signature) = Direct(target.Value);
            return new(call, candidates, signature);
        }
        return new(call, [], null);
    }

    private (MethodRef[], MachineSignature?) Direct(ulong address)
    {
        if (direct.TryGetValue(address, out var known)) return known;
        var candidates = facts.EntriesAt(address)
            .Where(e => e.Kind is EntryKind.Method or EntryKind.GenericMethod && e.Method is not null)
            .Select(e => e.Method!).Distinct().ToArray();
        var signatures = candidates.Select(c => abi.Machine(c, out _)).ToArray();
        var signature = signatures.Length > 0 && signatures.All(s => s is not null && SameShape(s, signatures[0]!)) ? signatures[0] : null;
        return direct[address] = (candidates, signature);
    }

    /// <summary>两个签名占用相同的机器位置并有相同的内存效果。</summary>
    private static bool SameShape(MachineSignature a, MachineSignature b) =>
        a.Arguments.Length == b.Arguments.Length && a.Arguments.Zip(b.Arguments).All(p => Same(p.First, p.Second))
        && (a.Return is null) == (b.Return is null) && (a.Return is null || Same(a.Return, b.Return!))
        && a.MethodInfo == b.MethodInfo;

    private static bool Same(MachineValue a, MachineValue b) => a.Index == b.Index && a.Transfer == b.Transfer && a.Size == b.Size
        && a.Access == b.Access && a.Pieces.AsSpan().SequenceEqual(b.Pieces);
}
