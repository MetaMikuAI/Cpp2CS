using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Runtime;
using Cpp2CS.Ssa;

namespace Cpp2CS.Managed;

/// <summary>调用的输入、结果存储；不包含调用破坏的其他寄存器。</summary>
public sealed record CallShape(Storage[] Reads, Storage[] Results);

/// <summary>在 SSA 之前使用已知签名；未知目标或不支持的传参方式保留保守约定。</summary>
public sealed class ManagedCallModel(Func<Call, Callee?> resolve, IManagedAbi abi, CallingConvention convention) : ICallModel
{
    private readonly ConservativeCallModel fallback = new(convention);
    private readonly Dictionary<ulong, CallShape?> shapes = new();

    public CallShape? Shape(Call call)
    {
        if (call.Kind is not (CallKind.Direct or CallKind.Tail) || call.Target is not Const target) return null;
        if (shapes.TryGetValue(target.Value, out var cached)) return cached;
        return shapes[target.Value] = Classify(resolve(call));
    }

    public IReadOnlyList<Storage> Reads(Call call) => Shape(call)?.Reads ?? fallback.Reads(call);
    public IReadOnlyList<Storage> Results(Call call) => call.Kind is CallKind.Tail or CallKind.TailIndirect
        ? [] : Shape(call)?.Results ?? fallback.Results(call);
    public IReadOnlyList<Storage> Clobbers(Call call) => convention.Clobbered;

    private CallShape? Classify(Callee? callee)
    {
        switch (callee)
        {
            case ManagedCallee managed:
            {
                if (managed.Owners.Count == 0) return null;
                var reads = new List<Storage>();
                var results = new List<Storage>();
                foreach (var owner in managed.Owners)
                {
                    if (abi.Classify(owner.Method, out _) is not { } signature) return null;
                    if (signature.Arguments.Any(a => a.Passing == Passing.Stack)) return null;
                    reads.AddRange(signature.Arguments.SelectMany(a => a.Pieces).Select(p => p.Register));
                    if (signature.MethodInfo is { } methodInfo) reads.Add(methodInfo.Register);
                    if (signature.Return is { } value)
                    {
                        if (value.Passing == Passing.Indirect) reads.Add(value.Pieces[0].Register);
                        else results.AddRange(value.Pieces.Select(p => p.Register));
                    }
                }
                return new CallShape(reads.Distinct().ToArray(), results.Distinct().ToArray());
            }
            case HelperCallee { Helper: var helper }:
            {
                if (HelperShape(helper.Kind) is not { } shape) return null;
                return new CallShape(shape.Arguments.Select(i => convention.IntegerArguments[i]).ToArray(),
                    shape.Returns || helper.ReturnedArgument is not null ? [convention.IntegerResults[0]] : []);
            }
            default:
                return null;
        }
    }

    /// <summary>辅助函数的整数参数位置及整数返回值；其余函数暂不收窄。</summary>
    private static (int[] Arguments, bool Returns)? HelperShape(HelperKind kind) => kind switch
    {
        HelperKind.InitMetadata or HelperKind.NullCheck or HelperKind.EnsureInit or HelperKind.ObjectNew or HelperKind.CxaBeginCatch => ([0], true),
        HelperKind.ClassInit or HelperKind.Rethrow or HelperKind.UnwindResume or HelperKind.Terminate => ([0], false),
        HelperKind.WriteBarrier or HelperKind.Raise or HelperKind.Throw => ([0, 1], false),
        HelperKind.NewArray or HelperKind.Box or HelperKind.Unbox or HelperKind.IsInst or HelperKind.IsAssignableFrom
            or HelperKind.GetException or HelperKind.GenericVirtualMethod => ([0, 1], true),
        HelperKind.InterfaceLookup or HelperKind.Memcpy or HelperKind.Memset => ([0, 1, 2], true),
        HelperKind.CxaEndCatch => ([], false),
        _ => null,
    };
}
