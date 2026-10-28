using Cpp2CS.Calls;
using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

public sealed partial class SourceLibraryCalls
{
    private readonly Dictionary<DefinitionRef, SourceGuardedUpdate[]> guardedUpdates = [];

    private ManagedBody RewriteGuardedUpdates(ManagedBody body)
    {
        var owners = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedStore>().Select(s => s.Target).OfType<FieldValue>()
            .Where(f => !ManagedAccess.Field(types, body.Method.Method.Owner, f.Field, f.Receiver.Type))
            .Select(f => f.Field.DeclaringType).OfType<DefinitionRef>().Where(t => t.Arguments.Count == 0 && !t.Definition.IsValueType).Distinct();
        foreach (var owner in owners)
        {
            if (!guardedUpdates.TryGetValue(owner, out var candidates))
            {
                var methods = owner.Definition.Methods.Where(m => !m.IsStatic && !m.IsVirtual && m.Parameters.Count == 0
                    && m.GenericParameters.Count == 0 && types.Kind(m.ReturnType) == TypeKind.Bool
                    && (m.Attributes & MethodAttributes.MemberAccessMask) == MethodAttributes.Public
                    && facts.Code.At(m.Address) is { Region: CodeRegion.Managed, Size: <= 128 });
                candidates = methods.Select(m => SummaryBody(new(new(m, [], []), m.Address), allowRegions: true))
                    .Where(b => b is not null).Select(b => SourceGuardedUpdate.Create(b!, types))
                    .OfType<SourceGuardedUpdate>().ToArray();
                guardedUpdates[owner] = candidates;
            }
            foreach (var candidate in candidates)
                while (candidate.Rewrite(body, types, () => new LocalValue(new(Storage.Temp(next--), 1), types.Boolean, 1),
                    (site, method) => Evidence.Add($"0x{body.Method.Method.Address:x}\t0x{site:x}\t{body.Method}\t{method}"),
                    method => method.DeclaringType is DefinitionRef declaring
                        ? FieldCalls(declaring).FirstOrDefault(c => !c.Write && c.Method.Equals(method))?.Field : null) is { } changed) body = changed;
        }
        return body;
    }
}
