using Cpp2CS.Facts;
using Cpp2CS.Ir;
using static Cpp2CS.Recovery.MethodRecovery;

namespace Cpp2CS.Recovery;

internal static class CallResolution
{
    // ---------- 调用目标（地址分解见 MethodRecovery.Memory.cs） ----------
    internal static Dictionary<Storage, Expr> ArgumentsOf(Call call) => call.ArgumentsBySource();
    internal static MethodRef? Resolve(this RecoveryScope ctx, Call call)
    {
        if (ctx.State.Calls.callBindings.Cached(call, ctx.analyses.Version) is { } cached)
            return cached;
        var result = ctx.ResolveOnce(call);
        // 封闭实例：经自身 MethodInfo/RGCTX 得到的方法保留泛型参数形式（如 IUniTaskSource<T>.GetResult），代入实例的实参。
        if ((ctx.ClosedInstance || ctx.SharedDefinition) && result is not null)
            result = result with
            {
                TypeArguments = result.TypeArguments.Select(t => t.Substitute(ctx.method.TypeArguments, ctx.method.MethodArguments)).ToArray(),
                MethodArguments = result.MethodArguments.Select(t => t.Substitute(ctx.method.TypeArguments, ctx.method.MethodArguments)).ToArray(),
            };
        ctx.State.Calls.callBindings.Remember(call, result, ctx.analyses.Version);
        return result;
    }

    internal static MethodRef? ResolveOnce(this RecoveryScope ctx, Call call)
    {
        if (call.Op is null && call.Target is Const inferredTarget && ctx.facts.Unregistered.At(inferredTarget.Value) is { } identity)
            return UnregisteredMethods.Resolve(identity, call, ctx.Expand, ctx.owner.abi, out _);
        var receiver = ConstructionRules.Receiver(call) is { } r ? ctx.TypeOfValue(r) : null;
        if (receiver is GenericParameterRef { ReferenceBase: { } constraint })
            receiver = constraint;
        switch (call.Op)
        {
            case { Kind: OpKind.CallMethodPointer, Operand: MethodRef pointerMethod }:
                return pointerMethod;
            case null when call.Target is Const target:
                {
                    var candidates = ctx.facts.EntriesAt(target.Value).Where(e => e.Kind is EntryKind.Method or EntryKind.GenericMethod && e.Method is not null).Select(e => e.Method!.Method).Distinct().ToArray();
                    // 未注册的本地副本：与接收者类型上某个方法 L2 形状相同（CopyOf），按该方法解析。
                    if (candidates.Length == 0)
                    {
                        foreach (var candidateType in ctx.ReceiverTypes(call, receiver))
                            if (candidateType is DefinitionRef { Arguments.Count: 0 } receiverType && ctx.owner.NativeMethods.CopyOf(target.Value, receiverType.Definition) is { } copy)
                                return new MethodRef(copy, [], []);
                        return ctx.ConversionCopy(call, target.Value);
                    }

                    var symbolic = call.Arguments.Select(ctx.Expand).OfType<Symbol>().Where(s => s.Kind == SymbolKind.Method).Select(s => (MethodRef)s.Value).FirstOrDefault(m => candidates.Contains(m.Method));
                    if (symbolic is not null)
                        return symbolic;
                    // RGCTX 的 constrained 项携带值类型及接口身份；用槽位核对直接目标后保留该实例实参。
                    for (var i = 0; i < call.Arguments.Length; i++)
                        if (ctx.Expand(call.Arguments[i]) is Symbol { Kind: SymbolKind.Constrained, Value: ValueTuple<TypeRef, MethodRef> constrained } && ConstrainedImplementation(constrained.Item1, constrained.Item2, candidates) is { } implementation && ctx.owner.abi.Classify(implementation, out _)?.MethodInfo?.Register == call.Sources[i])
                            return implementation;
                    // 编译器生成的嵌套类型沿用外层泛型实参；未读取 this 的直接入口仍可由这层身份解析。
                    if (candidates is [var nestedTarget] && nestedTarget.GenericParameters.Count == 0 && nestedTarget.Owner.GenericParameters.Count > 0 && nestedTarget.Owner.GenericParameters.Count <= ctx.method.TypeArguments.Count)
                    {
                        for (var parent = ctx.method.Method.Owner; parent is not null; parent = parent.DeclaringType)
                        {
                            if (parent != nestedTarget.Owner)
                                continue;
                            var inferred = new MethodRef(nestedTarget, ctx.method.TypeArguments.Take(parent.GenericParameters.Count).ToArray(), []);
                            if (inferred.Method.IsStatic || ctx.owner.abi.Classify(inferred, out _)?.This is { } unused && ctx.UnusedInput(call, inferred, unused))
                                return inferred;
                        }
                    }

                    // 唯一直接入口的 this 若确实未用，前一次调用留下的无关对象不能否定其方法身份。
                    if (candidates is [var unique] && !unique.IsStatic && unique.GenericParameters.Count == 0 && unique.Owner.GenericParameters.Count == 0 && receiver is not null && !ctx.types.IsAssignable(receiver, new DefinitionRef(unique.Owner, [])))
                    {
                        var direct = new MethodRef(unique, [], []);
                        if (ctx.owner.abi.Classify(direct, out _)?.This is { } unusedThis && ctx.UnusedInput(call, direct, unusedThis))
                            return direct;
                    }

                    var available = new List<CallCandidate>();
                    foreach (var candidate in candidates.OrderBy(c => c.Index))
                    {
                        if (candidate.GenericParameters.Count > 0)
                        {
                            available.Add(new(MethodRef.Open(candidate), "native-entry", "call.generic-arguments-missing"));
                            continue;
                        }

                        if (candidate.Owner.GenericParameters.Count == 0)
                        {
                            var compatible = candidate.IsStatic || receiver is null || ctx.types.IsAssignable(receiver, new DefinitionRef(candidate.Owner, [])) || receiver is ByRefRef || ConstructionRules.Receiver(call) is Use reference && ctx.CheckedReference(reference, new DefinitionRef(candidate.Owner, []), call.Address);
                            available.Add(new(new(candidate, [], []), "native-entry+receiver", compatible ? null : "call.receiver-incompatible"));
                            continue;
                        }

                        if (!candidate.IsStatic && (CallResolution.Instantiation(receiver, candidate.Owner) ?? ctx.StructReceiverArguments(ConstructionRules.Receiver(call), candidate.Owner)) is { } typeArguments)
                            available.Add(new(new(candidate, typeArguments, []), "native-entry+receiver-instance"));
                        else
                            available.Add(new(MethodRef.Open(candidate), "native-entry", "call.type-arguments-missing"));
                    }

                    var accepted = available.Where(c => c.Rejection is null).Select(c => c.Method).Distinct().ToArray();
                    var selected = accepted.Length == 1 ? accepted[0] : null;
                    ctx.State.Calls.callBindings.Candidates(call, target.Value, available, selected, accepted.Length == 0 ? "blocked" : accepted.Length == 1 ? "bound" : "conflict");
                    return selected;
                }

            case { Kind: OpKind.CallVirtual, Operand: int slot }:
                // 接收者静态类型的 vtable 槽位：callvirt 按对象的实际类型在同一槽位分派
                if (receiver is not DefinitionRef { Definition: var type } || slot >= type.VTable.Count || type.VTable[slot] is not { } entry)
                    return null;
                if (entry.Method.Owner.GenericParameters.Count == 0)
                    return entry with
                    {
                        TypeArguments = []
                    };
                return CallResolution.Instantiation(receiver, entry.Method.Owner) is { } arguments ? entry with
                {
                    TypeArguments = arguments
                }

                : null;
            case { Kind: OpKind.CallGenericVirtual, Operand: MethodRef generic } when generic.Method.IsVirtual:
                return generic;
            case { Kind: OpKind.CallInterface, Operand: ValueTuple<object?, int> pair } when pair.Item1 is DefinitionRef itf:
                return itf.Definition.Methods.FirstOrDefault(m => m.Slot == pair.Item2) is { } interfaceMethod ? new MethodRef(interfaceMethod, itf.Arguments, []) : null;
            case { Kind: OpKind.CallDelegate } when receiver is DefinitionRef d:
                return d.Definition.Methods.FirstOrDefault(m => m.Name == "Invoke" && !m.IsStatic) is { } invoke ? new MethodRef(invoke, d.Arguments, []) : null;
            case { Kind: OpKind.CallDelegate, Operand: MethodRef knownInvoke } when receiver is null:
                return knownInvoke;
            default:
                return null;
        }
    }

    internal static IEnumerable<TypeRef> ReceiverTypes(this RecoveryScope ctx, Call call, TypeRef? receiver)
    {
        if (receiver is ByRefRef { Element: var element })
            yield return element;
        else if (receiver is not null)
            yield return receiver;
        if (ConstructionRules.Receiver(call) is not { } address)
            yield break;
        var (root, offset, rest) = ctx.Split(address);
        if (root is null || rest.Count != 0 || ctx.TypeOfAddressBase(root) is not { } rootType)
            yield break;
        if (offset == 0 && rootType is ByRefRef { Element: var self })
            yield return self;
        foreach (var path in ctx.StructPaths(rootType).Where(p => p.Offset == offset && ctx.types.Kind(p.Type) == TypeKind.Struct))
            yield return path.Type;
    }

    /// <summary>type 或其基类中 definition 的实例实参。</summary>
    internal static IReadOnlyList<TypeRef>? Instantiation(TypeRef? type, TypeDef definition)
    {
        if (type is ByRefRef byRef)
            type = byRef.Element;
        if (type is GenericParameterRef { ReferenceBase: { } constraint })
            type = constraint;
        for (var current = type; current is DefinitionRef d; current = d.Definition.BaseType?.Substitute(d.Arguments, []))
            if (d.Definition == definition)
                return d.Arguments;
        return null;
    }

    internal static TypeRef Concrete(MethodRef m, TypeRef type) => type.Substitute(m.TypeArguments, m.MethodArguments);
}
