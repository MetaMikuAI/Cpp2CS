using Cpp2CS.Kernel.State;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Native.Terms;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Structure;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Recovery.Locations;

namespace Cpp2CS.Pipeline;

public static class StructureRecovery
{
    public static StructureResult Run(NativeFunction input, MethodContext context, MethodBinder binder, BindingEntryKind kind, ITypeLayouts? layouts = null)
    {
        // 没有调用或条件分支，且写入全在帧内时，本变换没有任何删除或折叠候选。
        if (!input.Blocks.Any(b => b.End is Branch || b.Statements.Any(s => s is Call)))
        {
            var writes = input.Blocks.SelectMany(b => b.Statements).OfType<MemoryWrite>().ToArray();
            if (!SnapshotRewrite.Dependencies(writes.Select(w => w.Address)).Any(t => t.Identity is ResultAtom))
            {
                var location = new LocationQuery(); var query = new QueryContext(input);
                if (writes.All(w => query.Get(location, new(w.Address, w.Width)) is { IsSuccess: true, Value.Region: Region.Frame }))
                    return new(input, [], []);
            }
        }
        var facts = context.Facts;
        var catalog = RuntimeFunctionCatalog.Select(facts.Spec.Layout.UnityVersion, facts.Spec.Layout.Triple, facts.Spec.Layout.DataModel);
        var calls = new CallNamingQuery(binder, new NamingCodeMap(facts.CodeMap), new RuntimeFunctionMap(facts.RuntimeFunctions), catalog);
        var survey = new NamingSurvey(calls, new MetadataSlotDecoder(facts), facts.Image);
        survey.Observe(input);
        var names = survey.Finish();
        var state = new StateQueries(image: facts.Image);
        var signature = binder.Entry(MethodRef.Open(context.Method), kind).Value;
        var values = new ValueNamingQuery(state, calls, names, facts.Spec, binder, signature);
        var slots = signature?.Slots.Return.Pieces.Select(p => p.Slot).ToHashSet();
        layouts ??= new FieldLayouts(facts.Spec, facts.Image.PointerWidth, facts.Image.PointerWidth);
        var locations = new ManagedLocationQuery(state, values, layouts, facts.Spec);
        var initialization = new ClassInitializationQuery(state, calls, values, locations, facts.Spec);
        return new UnobservableEffects(state, calls, values, facts.Image, slots, locations, initialization).Run(input) with { Names = names };
    }
}
