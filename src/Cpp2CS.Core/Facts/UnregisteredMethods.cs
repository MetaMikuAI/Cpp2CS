using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Facts;

/// <summary>
/// 未注册入口的定义身份；实例见证不是该地址的统一 MethodRef。
/// Abi 的类型字段来自一个正见证，只查询其共同传递形态；调用的具体类型必须从该调用的 MethodRef 取得。
/// </summary>
public sealed record UnregisteredMethod(ulong Address, MethodDef Definition, AbiSignature Abi,
    IReadOnlyList<MethodWitness> Witnesses, IReadOnlyList<ulong> ShapeMatches, IReadOnlyList<CodeEntry> Adjustors);
public sealed record MethodWitness(ulong Caller, ulong Site, MethodRef Instance);
public sealed record OwnerDecision(ulong Address, string Reason, int Sites, int Witnesses, int Instances, int? Definition);

/// <summary>只用注册事实建立的 A+B 证据。构建时不查询正在推断的表，避免自证循环。</summary>
public sealed partial class UnregisteredMethods
{
    public static UnregisteredMethods Empty { get; } = new();
    private readonly Dictionary<ulong, UnregisteredMethod> accepted = [];
    private readonly List<OwnerDecision> decisions = [];
    public IReadOnlyCollection<UnregisteredMethod> All => accepted.Values;
    public IReadOnlyList<OwnerDecision> Decisions => decisions;
    public UnregisteredMethod? At(ulong address) => accepted.GetValueOrDefault(address);

    public static bool IsClosed(MethodRef method) => Closed(method.DeclaringType)
        && method.MethodArguments.Count == method.Method.GenericParameters.Count && method.MethodArguments.All(Closed);

    private static bool Closed(TypeRef type) => type switch
    {
        GenericParameterRef => false,
        DefinitionRef d => d.Arguments.Count == d.Definition.GenericParameters.Count && d.Arguments.All(Closed),
        ArrayRef a => Closed(a.Element),
        ByRefRef r => Closed(r.Element),
        PointerRef p => Closed(p.Element),
        _ => true,
    };

    /// <summary>每次只接受隐藏参数位置上的完整 Method 符号，不从其他参数或表达式子项猜实例。</summary>
    public static MethodRef? Resolve(UnregisteredMethod identity, Call call, Func<Expr, Expr> expand, ManagedAbi abi, out string reason)
    {
        reason = "MethodInfo 在栈上";
        if (identity.Abi.MethodInfo is not { } hidden) return null;
        var index = Array.IndexOf(call.Sources, hidden.Register);
        if (index < 0 || index >= call.Arguments.Length) { reason = "MethodInfo 实参缺失"; return null; }
        var value = expand(call.Arguments[index]);
        if (value is not Symbol { Kind: SymbolKind.Method, Value: MethodRef method })
        {
            reason = value switch
            {
                Const { Value: 0 } => "MethodInfo 为零",
                Use { Variable.Version: 0 } or Entry => "MethodInfo 入口转传，实例未知",
                Load { Address: FrameAddress } or FrameAddress => "MethodInfo 在栈上，实例未证明",
                _ => "MethodInfo 未知或非单一符号",
            };
            return null;
        }
        if (method.Method != identity.Definition) { reason = "MethodInfo 与定义身份冲突"; return null; }
        if (!IsClosed(method)) { reason = "MethodInfo 不是封闭实例"; return null; }
        if (abi.Classify(method, out _) is not { } signature || Shape(signature) != Shape(identity.Abi))
        { reason = "MethodInfo 实例 ABI 不吻合"; return null; }
        reason = "";
        return method;
    }

    public static string Shape(AbiSignature signature)
    {
        static string Value(AbiValue? value) => value is null ? "void" : $"{value.Passing}:" + string.Join(",", value.Pieces.Select(p => $"{p.Register}:{p.Width}@{p.Offset}"));
        return $"{Value(signature.This)}|{string.Join(';', signature.Parameters.Select(Value))}|{signature.MethodInfo}|{Value(signature.Return)}";
    }
}
