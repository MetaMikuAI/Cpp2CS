using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Native;
using Cpp2CS.Recovery.Checks;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Structure;

public sealed partial class UnobservableEffects
{
    private bool FoldCheckedUnbox(QueryContext c, SnapshotRewrite edit, List<StructureRecord> records)
    {
        if (locations is null) return false;
        var runtimeCalls = c.Snapshot.Blocks.SelectMany(block => block.Statements.OfType<Call>()).Select(call => c.Get(calls, call.Identity)).ToArray();
        if (!runtimeCalls.Any(named => named is { IsSuccess: true, Value.Operation.Il.Name: "CastClass" }
            or { IsSuccess: true, Value.Operation.Name: "ThrowInvalidCast" })) return false;
        var candidates = c.Snapshot.Blocks.SelectMany(block => block.Statements.OfType<Call>().Select(call => (Block: block, Call: call)))
            .Where(candidate => c.Get(calls, candidate.Call.Identity) is { IsSuccess: true, Value.Operation.Il.Name: "UnboxUnchecked" }).ToArray();
        if (candidates.Length == 0) return false;
        var query = new CheckedUnboxFusionQuery(state, calls, names, locations);
        var runtime = RuntimeFunctionCatalog.Select(names.Spec.Layout.UnityVersion, names.Spec.Layout.Triple, names.Spec.Layout.DataModel)
            .Functions.FirstOrDefault(fn => fn.Operation.Il.Name == "Unbox" && fn.Arguments.SequenceEqual(new[] { "object", "class" }) && fn.Signature is not null);
        var signature = runtime?.Signature is { } prototype ? names.Binder.Classify(prototype).Value : null;
        if (signature is null || signature.Slots.Parameters.Any(p => p.Pieces.Length != 1 || p.CopyAddress is not null)
            || signature.Slots.Return.Pieces.Length != 1 || signature.Slots.Return.BufferAddress is not null) return false;
        foreach (var (block, unbox) in candidates)
        {
            var candidate = c.Get(query, unbox.Identity);
            if (!candidate.IsSuccess || candidate.Value is not { } proof) continue;
            edit.RemovedStatements.Add(proof.Check);
            edit.Replacements[proof.Result] = proof.Object;
            var parameters = new[] { proof.Object, proof.Class };
            var replacement = unbox with { Target = new NamedFunction(runtime!.MangledName), Arguments = parameters.Select((v, i) =>
                new SlotValue(signature.Slots.Parameters[i].Pieces[0].Slot, v)).ToImmutableArray() };
            edit.Blocks[block.Identity] = block with { Statements = block.Statements.Replace(unbox, replacement) };
            if (proof.Test is { } test) edit.Blocks[test] = edit.Blocks[test] with { End = new Jump(proof.Pass!) };
            bool undefined = false;
            RefineGuardResults(c, edit, [proof.Check], ref undefined);
            if (undefined) records.Add(new("unbox-fusion-undefined", unbox.Trace?.NativeAddress, UndefinedAssumption, true));
            records.Add(new("checked-unbox", unbox.Trace?.NativeAddress, "非空对象的类型判断失败只抛同一转换异常，结果只供随后拆箱使用", true));
            return true;
        }
        return false;
    }
}
