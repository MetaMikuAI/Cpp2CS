using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
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
                    Inputs: function.Arguments.Select((name, i) => (name, value.Arguments[i])).ToImmutableDictionary(x => x.name, x => x.Item2), Result: value.Result)
                    : new(kind, Function: function, Why: new("naming.call-binding", binding?.Failure?.Detail ?? string.Join("；", function.Unsupported)));
            }
        }
        return Outcome<ClassifiedCall>.Success(result);
    }
}
