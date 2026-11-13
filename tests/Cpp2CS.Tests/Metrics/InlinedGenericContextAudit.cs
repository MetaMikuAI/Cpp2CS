using System.Collections.Concurrent;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Structure;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Tests.Metrics;

/// <summary>初始化锚点只作普查，不参与恢复或调用等价判定。</summary>
internal sealed class InlinedGenericContextAudit(IMethodStage<NativeFunction, ManagedBody> recovery) : IMethodStage<NativeFunction, ManagedBody>
{
    private sealed record Entry(int Index, string Kind, string? Entity, string? Code, ulong? Address, string[] Uses);
    private sealed record Anchor(MethodDef Caller, MethodRef Method, ulong? Address, Entry[] Entries, Entry[] Table);
    private readonly ConcurrentBag<Anchor> anchors = [];
    private readonly ConcurrentDictionary<MethodDef, StageResult<ManagedBody>> bodies = [];
    public string Name => recovery.Name;

    public StageResult<ManagedBody> Run(NativeFunction input, MethodContext context)
    {
        var facts = context.Facts;
        var candidates = input.Blocks.SelectMany(b => b.Statements).OfType<Call>()
            .Where(call => facts.RuntimeFunctions.Find(call.Target)?.Function.Operation.Name == "InitializeMethodRgctx").ToArray();
        if (candidates.Length != 0 && (!GenericWitness.IsGeneric(context.Method)
            || context.Entry.Method is { } canonical && GenericWitness.IsCanonical(canonical))) Observe(input, context, candidates);
        var result = recovery.Run(input, context);
        // 直线性取会话选中的规范见证，不让值见证覆盖它。
        if (!GenericWitness.IsGeneric(context.Method) || context.Entry.Method is { } instance && GenericWitness.IsCanonical(instance))
            bodies.TryAdd(context.Method, result);
        return result;
    }

    private void Observe(NativeFunction function, MethodContext context, Call[] initializers)
    {
        var facts = context.Facts;
        var layouts = new FieldLayouts(facts.Spec, facts.Image.PointerWidth, facts.Image.PointerWidth);
        var binder = new MethodBinder(new(layouts, function.AddressWidth), new Aapcs64());
        var spec = facts.Spec.Layout;
        var calls = new CallNamingQuery(binder, new NamingCodeMap(facts.CodeMap), new RuntimeFunctionMap(facts.RuntimeFunctions),
            RuntimeFunctionCatalog.Select(spec.UnityVersion, spec.Triple, spec.DataModel));
        var survey = new NamingSurvey(calls, new MetadataSlotDecoder(facts), facts.Image);
        survey.Observe(function);
        var state = new StateQueries(image: facts.Image);
        var decoder = new MetadataRgctxDecoder(facts);
        var definition = MethodRef.Open(context.Method);
        var witness = GenericWitness.IsGeneric(context.Method) ? new GenericWitness(definition, context.Entry.Method!, layouts) : null;
        var signature = binder.Definition(definition, witness is null ? BindingEntryKind.Ordinary : BindingEntryKind.SharedGeneric, context.Entry.Method).Value;
        var names = new ValueNamingQuery(state, calls, survey.Finish(), facts.Spec, binder, signature, decoder, witness);
        var c = names.CreateContext(function);
        var reads = function.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>().ToArray();
        var classes = new Dictionary<Term, MethodRef>();
        var tables = new Dictionary<Term, (MethodRef Method, bool MethodContext)>();
        Term Resolve(Term value) => c.Get(state.Resolve, value) is { IsSuccess: true } resolved ? resolved.Value : value;
        ValueName? Named(Term value) => c.Get(names, value) is { IsSuccess: true } named ? named.Value.Name : null;
        Location? Location(MemoryRead read) => c.Get(state.Locations, new(Resolve(read.Address), read.Width)) is { IsSuccess: true } found ? found.Value : null;
        foreach (var read in reads)
        {
            if (Location(read) is not { Offset: { } offset } location || read.Width != function.AddressWidth) continue;
            if (Named(location.Root) is not EntityName { Entity: MethodEntity owner }) continue;
            if (offset == spec.Field("MethodInfo", "klass").ByteOffset) classes[Resolve(read.Result)] = owner.Method;
            if (offset == spec.Field("MethodInfo", "rgctx_data").ByteOffset) tables[Resolve(read.Result)] = (owner.Method, true);
        }
        foreach (var read in reads)
            if (Location(read) is { Offset: { } offset } location && read.Width == function.AddressWidth
                && offset == spec.Field("Il2CppClass", "rgctx_data").ByteOffset && classes.TryGetValue(location.Root, out var method))
                tables[Resolve(read.Result)] = (method, false);
        Entry[] Entries(MethodRef owner) => reads.Select(read =>
        {
            if (Location(read) is not { Offset: { } offset } location || !tables.TryGetValue(location.Root, out var table)
                || table.Method != owner || offset < 0 || offset % spec.Record("Il2CppRGCTXData").Size != 0
                || offset / spec.Record("Il2CppRGCTXData").Size > int.MaxValue) return null;
            int index = (int)(offset / spec.Record("Il2CppRGCTXData").Size);
            var decoded = decoder.Decode(owner, table.MethodContext, index);
            var values = new HashSet<Term> { read.Result };
            bool Depends(Term term) => SnapshotRewrite.Dependencies([term]).Overlaps(values);
            bool changed;
            do
            {
                changed = false;
                foreach (var other in reads.Where(r => Depends(r.Address))) changed |= values.Add(other.Result);
                foreach (var merge in function.Blocks.SelectMany(b => b.Merges).Where(m => m.Inputs.Any(i => Depends(i.Value)))) changed |= values.Add(merge.Result);
            } while (changed);
            var uses = new List<string>();
            foreach (var block in function.Blocks)
            {
                foreach (var statement in block.Statements.Where(s => SnapshotRewrite.Uses(s).Any(Depends)))
                    switch (statement)
                    {
                        case Call call:
                            var named = c.Get(calls, call.Identity);
                            uses.Add(named.Value.Operation?.Name ?? string.Join(" / ", named.Value.Candidates?.Candidates.Select(x => x.Entry.Method?.ToString() ?? "未绑定方法") ?? []));
                            break;
                        case MemoryRead other when other != read:
                            uses.Add("read: " + Named(other.Result));
                            break;
                        case MemoryWrite: uses.Add("write"); break;
                    }
                if (SnapshotRewrite.Uses(block.End).Any(Depends)) uses.Add(block.End.GetType().Name);
            }
            return new Entry(index, decoded.IsSuccess ? decoded.Value.GetType().Name : "Unknown", decoded.IsSuccess ? decoded.Value.ToString() : null,
                decoded.Why?.Code, read.Trace?.NativeAddress, uses.Distinct().ToArray());
        }).OfType<Entry>().ToArray();
        foreach (var call in initializers)
        {
            var classified = c.Get(calls, call.Identity);
            if (!classified.IsSuccess || classified.Value.Inputs?.GetValueOrDefault("method")?.Source is not TermSource source
                || Named(source.Term) is not EntityName { Entity: MethodEntity target }) continue;
            var table = facts.CodeMap.Rgctx.GetValueOrDefault((target.Method.Method.Owner.Assembly, target.Method.Method.Token));
            var decodedTable = table.IsDefault ? [] : table.Select((entry, index) =>
            {
                var decoded = decoder.Decode(target.Method, true, index);
                return new Entry(index, entry.Kind.ToString(), decoded.IsSuccess ? decoded.Value.ToString() : null, decoded.Why?.Code, null, []);
            }).ToArray();
            anchors.Add(new(context.Method, target.Method, call.Trace?.NativeAddress, Entries(target.Method), decodedTable));
        }
    }

    // 普查中的直线体允许块间无条件连接，拒绝分支、循环和异常区域。
    private static bool Straight(ManagedBody body)
    {
        if (body.Regions.Count != 0 || body.Blocks.Count == 0 || body.Blocks.SelectMany(b => b.Statements).Any(s => s is ManagedBranch or ManagedSwitch or ManagedCheck)) return false;
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var seen = new HashSet<ulong>();
        var current = body.Blocks[0];
        while (seen.Add(current.Address))
        {
            var edges = current.Statements.SelectMany(ManagedValues.Edges).ToArray();
            if (edges.Length == 0) return seen.Count == blocks.Count;
            if (edges.Length != 1 || !blocks.TryGetValue(edges[0].Target, out current!)) return false;
        }
        return false;
    }

    public void Write(string output, RecoveryReport report)
    {
        var byId = report.Methods.ToDictionary(m => m.Identity);
        File.WriteAllText(Path.Combine(output, "inlined-generic-context.local.json"), RecoveryReport.Json(anchors
            .GroupBy(a => a.Method.Method).OrderBy(g => RecoverySession.Identity(g.Key), StringComparer.Ordinal).Select(group =>
            {
                var definition = byId.GetValueOrDefault(RecoverySession.Identity(group.Key));
                var body = definition?.Hole is { } hole ? new Missing<ManagedBody>(hole) : bodies.GetValueOrDefault(group.Key);
                var statements = (body as Completed<ManagedBody>)?.Value.Blocks.SelectMany(b => b.Statements).ToArray();
                return new
                {
                    Definition = RecoverySession.Identity(group.Key), Name = group.Key.ToString(), Occurrences = group.Count(),
                    Complete = group.Count(a => byId[RecoverySession.Identity(a.Caller)].Status == MethodStatus.Complete),
                    FirstReasons = group.Where(a => byId[RecoverySession.Identity(a.Caller)].Hole is not null)
                        .GroupBy(a => byId[RecoverySession.Identity(a.Caller)].Hole!.Reason.Code).ToDictionary(g => g.Key, g => g.Count()),
                    Straight = body is Completed<ManagedBody> complete ? Straight(complete.Value) : (bool?)null,
                    Statements = statements?.Length,
                    DefinitionFailure = (body as Missing<ManagedBody>)?.Hole.Reason ?? byId.GetValueOrDefault(RecoverySession.Identity(group.Key))?.Hole?.Reason,
                    Anchors = group.OrderBy(a => RecoverySession.Identity(a.Caller), StringComparer.Ordinal).ThenBy(a => a.Address).Select(a => new
                    {
                        Caller = RecoverySession.Identity(a.Caller), CallerName = a.Caller.ToString(), Instance = a.Method.ToString(), a.Address, a.Entries, a.Table,
                        Status = byId[RecoverySession.Identity(a.Caller)].Status.ToString(), Reason = byId[RecoverySession.Identity(a.Caller)].Hole?.Reason,
                    }),
                };
            })));
    }
}
