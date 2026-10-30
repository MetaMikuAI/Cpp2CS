
namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    internal static MethodRef? ConstrainedImplementation(TypeRef receiver, MethodRef contract, IReadOnlyCollection<MethodDef> candidates)
    {
        if (receiver is not DefinitionRef { Definition.IsValueType: true } type || !contract.Method.Owner.IsInterface
            || contract.Method.IsStatic || contract.Method.Slot < 0) return null;
        var offsets = type.Definition.InterfaceOffsets.Where(p => p.Interface.Substitute(type.Arguments, []).Equals(contract.DeclaringType))
            .Select(p => p.Offset).Distinct().ToArray();
        if (offsets is not [var offset]) return null;
        var slot = offset + contract.Method.Slot;
        if (slot < 0 || slot >= type.Definition.VTable.Count || type.Definition.VTable[slot] is not { } implementation
            || implementation.Method.Owner != type.Definition || !candidates.Contains(implementation.Method)) return null;
        return new(implementation.Method, type.Arguments, contract.MethodArguments);
    }
}
