using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

/// <summary>访问器的行为已由其代码验证为一次直接字段读写；Body 是需要随调用写出的实现。</summary>
public sealed record AccessorProof(MethodRef Method, ulong Address, FieldRef Field, bool IsSetter, ManagedBody Body);
public sealed record AccessorUse(ulong Address, AccessorProof Proof);

/// <summary>从元数据的属性关联寻找候选，只接受有代码且行为等价的访问器，不依赖字段或方法命名。</summary>
public sealed class Accessors(RecoverySession session)
{
    private readonly Dictionary<(MethodRef Method, bool Setter), AccessorProof?> proofs = new();
    private readonly Dictionary<(FieldRef Field, bool Setter), IReadOnlyList<AccessorProof>> candidates = new();
    private Dictionary<MethodRef, ulong[]>? code;

    public AccessorProof? Find(FieldValue field, bool setter, TypeDef caller)
    {
        var key = (field.Field, setter);
        if (!candidates.TryGetValue(key, out var found))
        {
            var matches = new List<AccessorProof>();
            if (field.Field.DeclaringType is DefinitionRef owner)
                foreach (var property in owner.Definition.Properties)
                {
                    var definition = setter ? property.Setter : property.Getter;
                    if (definition is null) continue;
                    var method = new MethodRef(definition, owner.Arguments, []);
                    if (Prove(method, setter) is { } proof && proof.Field == field.Field) matches.Add(proof);
                }
            candidates[key] = found = matches;
        }
        return found.FirstOrDefault(p => ManagedAccess.Method(session.Types, caller, p.Method, field.Receiver.Type));
    }

    public AccessorProof? Prove(MethodRef method, bool setter)
    {
        var key = (method, setter);
        if (proofs.TryGetValue(key, out var cached)) return cached;
        proofs[key] = null;
        var definition = method.Method;
        if (definition.IsStatic || definition.IsAbstract || definition.GenericParameters.Count > 0
            || (definition.IsVirtual && (definition.Attributes & MethodAttributes.Final) == 0)
            || (definition.ImplAttributes & MethodImplAttributes.Synchronized) != 0) return null;
        if (definition.Parameters.Count != (setter ? 1 : 0) || ManagedTypes.IsVoid(definition.ReturnType) != setter) return null;
        var addresses = Addresses(method);
        if (addresses.Length == 0) return null;
        AccessorProof? result = null;
        foreach (var address in addresses)
        {
            if (session.Functions.At(address) is not { } range || range.Start != address) return null;
            var prepared = session.Analyze(method, address, range);
            if (Match(session, prepared, setter) is not { } field) return null;
            if (result is not null && result.Field != field) return null;
            var recovered = BodyRecovery.Recover(session, prepared, recoverAccessors: false);
            if (recovered.Body is null) return null;
            result ??= new AccessorProof(method, address, field, setter, recovered.Body);
        }
        return proofs[key] = result;
    }

    private ulong[] Addresses(MethodRef method)
    {
        if (method.Method.Address is var address && address != 0 && method.TypeArguments.Count == 0 && method.MethodArguments.Count == 0
            && session.Model.Code.TryGetValue(address, out var owners) && owners.Any(o => o.Method == method)) return [address];
        code ??= session.Model.Code.SelectMany(p => p.Value.Select(o => (o.Method, Address: p.Key)))
            .GroupBy(p => p.Method).ToDictionary(g => g.Key, g => g.Select(p => p.Address).Distinct().ToArray());
        return code.GetValueOrDefault(method) ?? [];
    }

    /// <summary>单块、无其他读写或调用的访问器。只在这个封闭范围内展开局部定义，避免改变读取时机。</summary>
    internal static FieldRef? Match(RecoverySession session, PreparedMethod prepared, bool setter)
    {
        var function = prepared.Function;
        if (prepared.Problems.Count > 0 || function.Problems.Count > 0 || function.Blocks.Count != 1
            || function.EntryBlock.Handler is not null || function.EntryBlock.IsLandingPad) return null;
        var statements = function.EntryBlock.Statements;
        if (statements.OfType<Nop>().Any(n => n.Text is not ("hint #0" or "prfm" or "branch to next"))) return null;
        if (statements.Any(s => s is not (Define or Store or Return or Nop)) || statements.OfType<Return>().Count() != 1
            || statements.LastOrDefault(s => s is not Nop) is not Return returned || returned.Buffer is not null || returned.Pieces.Length != 0) return null;
        var loads = statements.SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).Count(e => e is Load);
        var stores = statements.OfType<Store>().ToArray();
        if (loads != (setter ? 0 : 1) || stores.Length != (setter ? 1 : 0)) return null;
        var definitions = new Dictionary<Variable, Expr>();
        Expr Expand(Expr value) => Fold.Simplify(ExprMap.Map(value, e => e is Use u && definitions.TryGetValue(u.Variable, out var source)
            ? Fold.Convert(u.Width > source.Width ? ConvKind.ZeroExtend : ConvKind.Truncate, source, u.Width) : null));
        foreach (var define in statements.OfType<Define>()) definitions.Add(define.Target, Expand(define.Value));
        var values = new ValueRecovery(session, prepared);
        if (values.SignatureProblem is not null) return null;
        var method = prepared.Method;
        var valueType = (setter ? method.Method.Parameters[0].Type : method.Method.ReturnType).Substitute(method.TypeArguments, method.MethodArguments);
        if (!setter)
        {
            if (returned.Value is null || values.RecoverAs(Expand(returned.Value), valueType, out _) is not
                FieldValue { Receiver: ArgumentValue { Index: -1 } } read || read.Type != valueType) return null;
            return read.Field;
        }
        var store = stores[0];
        if (returned.Value is not null || values.Location(Expand(store.Target), store.Value.Width, out _) is not
            FieldValue { Receiver: ArgumentValue { Index: -1 } } write || write.Type != valueType) return null;
        return values.RecoverAs(Expand(store.Value), valueType, out _) is ArgumentValue { Index: 0 } ? write.Field : null;
    }
}
