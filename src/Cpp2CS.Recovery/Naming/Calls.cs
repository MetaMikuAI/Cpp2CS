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
    public RuntimeManagedMethod? ManagedMethod => Function?.ManagedMethod ?? Operation?.Il.Method;
    /// <summary>运行时函数与系统函数按 C 层签名的绑定；给出被调方实际读取的输入槽。</summary>
    public BoundCall? Binding { get; init; }
}
public sealed class CallNamingQuery(MethodBinder binder, IBindingCodeMap code, IRuntimeFunctionMap runtime,
    RuntimeFunctionCatalog catalog) : Query<CallIdentity, ClassifiedCall>
{
    private sealed class CallIndexQuery : Query<int, ImmutableDictionary<CallIdentity, Call>>
    {
        public override Outcome<ImmutableDictionary<CallIdentity, Call>> Compute(QueryContext context, int key) =>
            Outcome<ImmutableDictionary<CallIdentity, Call>>.Success(context.Snapshot.Blocks.SelectMany(block => block.Statements)
                .OfType<Call>().ToImmutableDictionary(call => call.Identity));
    }
    private readonly CallIndexQuery index = new();

    /// <summary>只查询经过代码地图和目录确认的身份，不绑定实参或读取逐方法状态。</summary>
    public RuntimeFunction? RuntimeIdentity(CallTarget target)
    {
        if (target is ComputedTarget || target is ImageFunction image && code.At(image.EntryOffset).Length != 0) return null;
        return target switch
        {
            NamedFunction named => catalog.Functions.SingleOrDefault(f => f.MangledName == named.Name),
            ImportedTarget import => catalog.FindImport(import.Symbol.Name),
            _ => runtime.Find(target),
        };
    }

    public override Outcome<ClassifiedCall> Compute(QueryContext c, CallIdentity key)
    {
        var found = c.Get(index, 0);
        if (!found.IsSuccess) return found.Propagate<ClassifiedCall>();
        var call = found.Value[key];
        ClassifiedCall result;
        if (call.Target is ComputedTarget indirect) result = new(CallKind.Indirect, Target: indirect.Value);
        else if (call.Target is ImageFunction image && code.At(image.EntryOffset).Length > 0)
            result = new(CallKind.Managed, binder.Call(call, image, code, c.Snapshot.Terms));
        else
        {
            var function = RuntimeIdentity(call.Target);
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

/// <summary>共用代码只提供 C 层签名；托管身份来自方法信息，开放实参以当前定义的见证核对 ABI。</summary>
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
        var method = entity.Value.Name switch
        {
            EntityName { Entity: MethodEntity methodInfo } => methodInfo.Method,
            ParameterName { MethodInformation: true } => names.DefinitionMethod,
            _ => null,
        };
        if (method is null)
        {
            // 方法信息实参为空：被调方不使用泛型上下文。调用的是哪个实例由接收者给出——
            // 接收者静态类型的继承链上，候选方法的声明类型的那个实例。没有接收者时不定。
            if (information.Value.ConstantValue is not { IsZero: true })
                return No("witness", "方法信息实参不是已命名的方法实体。", entity.Value.Why);
            if (binding.This is not { } self) return No("receiver", "方法信息实参为空且调用没有接收者。");
            var receiverTerm = c.Get(sources, new(self.Source, new(block.Identity, block.Statements.IndexOf(call))));
            if (!receiverTerm.IsSuccess) return No("receiver", "方法信息实参为空且接收者没有可用的项。", receiverTerm.Why);
            var receiver = c.Get(names, receiverTerm.Value);
            if (!receiver.IsSuccess) return No("receiver", "方法信息实参为空且接收者命名失败。", receiver.Why);
            if (receiver.Value.StaticType is not DefinitionRef receiverType)
                return No("receiver", "方法信息实参为空且接收者没有静态类型。", receiver.Value.Why);
            var matches = new HashSet<MethodRef>();
            foreach (var candidate in candidates.Candidates)
            {
                if (candidate.Entry.Kind != BindingEntryKind.SharedGeneric || candidate.Entry.Method is not { } shared
                    || shared.Method.GenericParameters.Count != 0) continue;
                for (TypeRef? current = receiverType; current is DefinitionRef d; current = d.Definition.BaseType?.Substitute(d.Arguments, []))
                    if (d.Definition == shared.Method.Owner) { matches.Add(new(shared.Method, d.Arguments, [])); break; }
            }
            if (matches.Count == 0) return No("receiver", "方法信息实参为空，接收者类型的继承链上没有候选方法的声明类型。");
            if (matches.Count > 1) return No("ambiguous", "方法信息实参为空，接收者类型对应多个候选方法。");
            method = matches.Single();
        }
        var native = method;
        if (!ManagedCSignatureBuilder.IsClosed(method))
        {
            if (names.Witness is not { } witness || !witness.Knows(method))
                return No("witness", "方法信息见证含有本定义之外或不完整的泛型实参。");
            native = witness.Close(method);
        }
        if (!candidates.Candidates.Any(x => x.Entry.Kind == BindingEntryKind.SharedGeneric && x.Entry.Method?.Method == method.Method))
            return No("mismatch", "方法信息见证的定义与泛型实例入口候选不符。");
        var concrete = binder.Entry(native, BindingEntryKind.Ordinary);
        if (concrete.Value is not { } target || !Same(common!.Signature, target.Signature))
            return No("mismatch", "方法信息见证的 C 层签名与候选不符：" + concrete.Failure?.Detail);
        var result = binder.Call(call, target with { Entry = new(method, BindingEntryKind.Ordinary) }, c.Snapshot.Terms);
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
