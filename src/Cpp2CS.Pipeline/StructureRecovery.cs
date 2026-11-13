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
        if (input.Blocks.Any(b => b.Handler is not null))
        {
            input = ExceptionEntries.Run(input).Function;
            input = ExceptionSelectors.Run(input, context.Facts.Spec).Function;
        }
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
        if (input.Blocks.Any(block => block.Handler is not null)) input = ExceptionScaffolding.Project(input, calls);
        var signature = binder.Definition(MethodRef.Open(context.Method), kind, context.Entry.Method).Value;
        var surveyTimer = System.Diagnostics.Stopwatch.StartNew();
        var survey = new NamingSurvey(calls, new MetadataSlotDecoder(facts), facts.Image, binder, facts.Spec, signature);
        survey.Observe(input);
        var names = survey.Finish();
        surveyTimer.Stop();
        var state = new StateQueries(image: facts.Image);
        var values = new ValueNamingQuery(state, calls, names, facts.Spec, binder, signature, new MetadataRgctxDecoder(facts), layouts as GenericWitness);
        var slots = signature?.Slots.Return.Pieces.Select(p => p.Slot).ToHashSet();
        layouts ??= new FieldLayouts(facts.Spec, facts.Image.PointerWidth, facts.Image.PointerWidth);
        var locations = new ManagedLocationQuery(state, values, layouts, facts.Spec);
        var initialization = new ClassInitializationQuery(state, calls, values, locations, facts.Spec);
        var result = new UnobservableEffects(state, calls, values, facts.Image, slots, locations, initialization).Run(input);
        return result with { Names = names, Timings = result.Timings.SetItem("初始化凭据", surveyTimer.Elapsed.TotalSeconds) };
    }
}
