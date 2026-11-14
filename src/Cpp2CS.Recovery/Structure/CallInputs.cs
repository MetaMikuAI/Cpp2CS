using System.Collections.Immutable;
using Cpp2CS.Native;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Dispatch;

namespace Cpp2CS.Recovery.Structure;

public sealed partial class UnobservableEffects
{
    private NativeFunction RemoveUnusedCallInputs(NativeFunction function, List<StructureRecord> records) =>
        RemoveUnusedCallInputs(function, records, out _);
    private NativeFunction RemoveUnusedCallInputs(NativeFunction function, List<StructureRecord> records, out bool unresolved)
    {
        unresolved = false;
        var context = locations?.CreateContext(function) ?? names.CreateContext(function);
        var dispatch = locations is null ? null : new DispatchQuery(state, calls, names, locations, names.Binder, names.Spec);
        var edit = new SnapshotRewrite(function); bool changed = false;
        foreach (var block in function.Blocks)
        {
            var statements = block.Statements.ToBuilder();
            for (int i = 0; i < statements.Count; i++)
            {
                if (statements[i] is not Call call) continue;
                var named = context.Get(calls, call.Identity);
                if (!named.IsSuccess) continue;
                // 托管方法取全部候选的签名；运行时函数与系统函数取目录登记的 C 层签名。
                SignatureBinding[]? signatures = named.Value switch
                {
                    { Kind: CallKind.Managed, Candidates: { Failure: null, Candidates.Length: > 0 } candidates }
                        when candidates.Candidates.All(c => c.Binding.Success)
                        => named.Value.NativeSignature is { } native ? [native] : candidates.Candidates.Select(c => c.Binding.Value!.Signature).ToArray(),
                    { Kind: CallKind.Runtime or CallKind.System, Binding: { } binding } => [binding.Signature],
                    _ => null,
                };
                if (signatures is null && named.Value.Kind == CallKind.Indirect && dispatch is not null)
                {
                    var resolved = context.Get(dispatch, call.Identity);
                    if (resolved.IsSuccess && resolved.Value.Kind != DispatchKind.Unresolved && resolved.Value.Binding is { } binding)
                        signatures = [binding.Signature];
                }
                unresolved |= signatures is null && named.Value.Kind == CallKind.Indirect;
                if (signatures is null || signatures.Any(s => s.Signature.IsVariadic)) continue;
                // 参数、聚合副本地址和间接返回地址都属于输入；多候选取并集。
                var required = new HashSet<AbstractSlot>();
                foreach (var signature in signatures)
                {
                    var slots = signature.Slots;
                    foreach (var parameter in slots.Parameters)
                    {
                        foreach (var piece in parameter.Pieces) required.Add(piece.Slot);
                        if (parameter.CopyAddress is { } copy) required.Add(copy.Slot);
                    }
                    if (slots.Return.BufferAddress is { } buffer) required.Add(buffer.Slot);
                }
                var arguments = call.Arguments.Where(a => required.Contains(a.Slot)).ToImmutableArray();
                if (arguments.Length == call.Arguments.Length) continue;
                statements[i] = call with { Arguments = arguments }; changed = true;
                records.Add(new("unused-call-input", call.Trace?.NativeAddress, "全部候选的完整 ABI 签名均不读取这些输入槽", true));
            }
            edit.Blocks[block.Identity] = block with { Statements = statements.ToImmutable() };
        }
        return changed ? edit.Apply() : function;
    }
}
