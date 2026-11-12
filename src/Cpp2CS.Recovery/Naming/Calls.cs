using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Model;
using Cpp2CS.Native.Abi;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Naming;

/// <summary>装配处提供经过证明的目录对应；null 表示没有已知对应，不猜测目标。</summary>
public interface IRuntimeFunctionMap { RuntimeFunction? Find(CallTarget target); }
public enum CallKind { Managed, Runtime, System, Indirect, Unknown }
public sealed record ClassifiedCall(CallKind Kind, CallCandidates? Candidates = null, RuntimeFunction? Function = null,
    ImmutableDictionary<string, BoundValue>? Inputs = null, BoundValue? Result = null, Term? Target = null, Reason? Why = null)
{
    public RuntimeOperation? Operation => Function?.Operation;
    /// <summary>运行时函数与系统函数按 C 层签名的绑定；给出被调方实际读取的输入槽。</summary>
    public BoundCall? Binding { get; init; }
}
public sealed class CallNamingQuery(MethodBinder binder, IBindingCodeMap code, IRuntimeFunctionMap runtime,
    RuntimeFunctionCatalog catalog) : Query<CallIdentity, ClassifiedCall>
{
    public override Outcome<ClassifiedCall> Compute(QueryContext c, CallIdentity key)
    {
        var call = c.Snapshot.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single(x => x.Identity == key);
        ClassifiedCall result;
        if (call.Target is ComputedTarget indirect) result = new(CallKind.Indirect, Target: indirect.Value);
        else if (call.Target is ImageFunction image && code.At(image.EntryOffset).Length > 0)
            result = new(CallKind.Managed, binder.Call(call, image, code, c.Snapshot.Terms));
        else
        {
            var function = call.Target is ImportedTarget import
                ? catalog.Functions.SingleOrDefault(f => f.Recognition.Import == import.Symbol.Name) : runtime.Find(call.Target);
            if (function is null) result = new(CallKind.Unknown, Why: new("naming.call-target", "目标没有托管身份或目录对应。"));
            else
            {
                var kind = function.Recognition.Import is not null ? CallKind.System : CallKind.Runtime;
                var binding = function.Signature is { } signature ? binder.Call(call, signature, c.Snapshot.Terms) : null;
                result = binding?.Value is { } value ? new(kind, Function: function,
                    Inputs: function.Arguments.Select((name, i) => (name, value.Arguments[i])).ToImmutableDictionary(x => x.name, x => x.Item2), Result: value.Result) { Binding = value }
                    : new(kind, Function: function, Why: new("naming.call-binding", binding?.Failure?.Detail ?? string.Join("；", function.Unsupported)));
            }
        }
        return Outcome<ClassifiedCall>.Success(result);
    }
}

public sealed record SharedCallTarget(MethodRef Method, BoundCall Binding);

/// <summary>共用代码只提供 C 层签名；封闭托管身份必须来自隐藏的方法信息实参。</summary>
public sealed class SharedCallQuery(MethodBinder binder, CallNamingQuery calls, ValueNamingQuery? names,
    BoundSourceQuery sources) : Query<CallIdentity, SharedCallTarget>
{
    public override Outcome<SharedCallTarget> Compute(QueryContext c, CallIdentity key)
    {
        Outcome<SharedCallTarget> No(string kind, string message, Reason? cause = null) =>
            Outcome<SharedCallTarget>.Failure(new("binding.shared-call." + kind, message, cause));
        var named = c.Get(calls, key);
        if (!named.IsSuccess) return named.Propagate<SharedCallTarget>();
        if (named.Value.Candidates is not { Candidates.Length: > 0 } candidates
            || !candidates.Candidates.Any(x => x.Entry.Kind == BindingEntryKind.SharedGeneric))
            return No("witness", "调用没有泛型实例入口候选。");
        SignatureBinding? common = null;
        foreach (var candidate in candidates.Candidates)
        {
            var signature = binder.Entry(candidate.Entry);
            if (signature.Value is not { } value)
                return No("signature", "候选的 C 层签名不可得：" + signature.Failure!.Detail);
            if (common is not null && !Same(common.Signature, value.Signature))
                return No("signature", "候选的 C 层签名不一致。");
            common ??= value;
        }
        var block = c.Snapshot.Blocks.Single(b => b.Statements.OfType<Call>().Any(x => x.Identity == key));
        var call = block.Statements.OfType<Call>().Single(x => x.Identity == key);
        var bound = binder.Call(call, common!, c.Snapshot.Terms);
        if (bound.Value is not { } binding)
            return No("signature", "共享调用无法按公共 C 层签名绑定：" + bound.Failure!.Detail);
        if (names is null) return No("witness", "方法信息实参没有命名来源。");
        var information = c.Get(sources, new(binding.MethodInformation?.Source, new(block.Identity, block.Statements.IndexOf(call))));
        if (!information.IsSuccess) return No("witness", "方法信息实参没有可用的项。", information.Why);
        var entity = c.Get(names, information.Value);
        if (!entity.IsSuccess) return No("witness", "方法信息实参命名失败。", entity.Why);
        if (entity.Value.Name is not EntityName { Entity: MethodEntity { Method: var method } })
            return No("witness", "方法信息实参不是已命名的方法实体。", entity.Value.Why);
        if (!ManagedCSignatureBuilder.IsClosed(method))
            return No("witness", "方法信息见证的泛型实参未完整封闭。");
        if (!candidates.Candidates.Any(x => x.Entry.Kind == BindingEntryKind.SharedGeneric && x.Entry.Method?.Method == method.Method))
            return No("mismatch", "方法信息见证的定义与泛型实例入口候选不符。");
        var concrete = binder.Entry(method, BindingEntryKind.Ordinary);
        if (concrete.Value is not { } target || !Same(common!.Signature, target.Signature))
            return No("mismatch", "方法信息见证的 C 层签名与候选不符：" + concrete.Failure?.Detail);
        var result = binder.Call(call, target, c.Snapshot.Terms);
        return result.Value is { } valueBinding ? Outcome<SharedCallTarget>.Success(new(method, valueBinding))
            : No("signature", "见证实例无法绑定：" + result.Failure!.Detail);
    }

    private static bool Same(CSignature left, CSignature right) => left.IsVariadic == right.IsVariadic
        && Same(left.ReturnType, right.ReturnType) && left.Parameters.Length == right.Parameters.Length
        && left.Parameters.Zip(right.Parameters).All(p => Same(p.First, p.Second));

    private static bool Same(CType left, CType right) => (left, right) switch
    {
        (CAggregate a, CAggregate b) => a.Size == b.Size && a.Alignment == b.Alignment
            && a.Fields.Length == b.Fields.Length && a.Fields.Zip(b.Fields).All(p =>
                p.First.Offset == p.Second.Offset && Same(p.First.Type, p.Second.Type)),
        (CArray a, CArray b) => a.Count == b.Count && Same(a.Element, b.Element),
        _ => left == right,
    };
}
