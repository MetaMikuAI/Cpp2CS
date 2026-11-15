using Cpp2CS.Kernel.State;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Native.Terms;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Exceptions;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Structure;
using Cpp2CS.Runtime;
using Cpp2CS.Recovery.RuntimeFunctions;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Recovery.Locations;

namespace Cpp2CS.Pipeline;

public static class StructureRecovery
{
    public static StructureResult Run(NativeFunction input, MethodContext context, MethodBinder binder, BindingEntryKind kind, ITypeLayouts? layouts = null,
        InternalCallFacts? internalCalls = null, MethodRef? discoverInternalCall = null)
    {
        input = NormalizeExceptions(input, context.Facts.Spec);
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
        internalCalls ??= InternalCallAssembly.Get(facts).Facts;
        var catalog = RuntimeFunctionCatalog.Select(facts.Spec.Layout.UnityVersion, facts.Spec.Layout.Triple, facts.Spec.Layout.DataModel);
        var calls = new CallNamingQuery(binder, new NamingCodeMap(facts.CodeMap, discoverInternalCall is null ? facts.MethodCopies.Facts : null), new RuntimeFunctionMap(facts.RuntimeFunctions), catalog, internalCalls);
        MethodProgress.Mark("结构：异常区域");
        bool hasHandlers = input.Blocks.Any(block => block.Handler is not null);
        if (hasHandlers) input = ExceptionScaffolding.Project(input, calls, splitEntries: true);
        var signature = binder.Definition(MethodRef.Open(context.Method), kind, context.Entry.Method).Value;
        MethodProgress.Mark("结构：命名普查");
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
        var objectType = hasHandlers
            ? facts.Model.Types.FirstOrDefault(t => t.Assembly == "mscorlib.dll" && t.FullName == "System.Object") : null;
        var regions = objectType is null ? null : new ExceptionRegionQuery(state, calls, values, facts.Spec, new DefinitionRef(objectType, []), nested: true);
        var initialization = new ClassInitializationQuery(state, calls, values, locations, facts.Spec, regions);
        MethodProgress.Mark("结构：效果消去与区域折叠");
        var effects = new UnobservableEffects(state, calls, values, facts.Image, slots, locations, initialization, internalCalls, discoverInternalCall, context.Entry.Address);
        var result = effects.Run(input);
        while (hasHandlers && result.Function.Blocks.Any(b => b.Handler is not null))
        {
            var normalized = NormalizeExceptions(result.Function, facts.Spec);
            // 闭合只在归一确实减少了处理入口或分支时继续；只切块、不减少它们的改动不触发重跑，终止由这个量保证。
            if (ReferenceEquals(normalized, result.Function) || !Reduced(result.Function, normalized)) break;
            input = ExceptionScaffolding.Project(normalized, calls, splitEntries: true);
            MethodProgress.Mark("结构：效果消去与区域折叠");
            result = effects.Run(input).Accumulate(result);
        }
        return result with { Names = names, Timings = result.Timings.SetItem("初始化凭据", surveyTimer.Elapsed.TotalSeconds) };
    }

    private static NativeFunction NormalizeExceptions(NativeFunction input, RuntimeSpec spec)
    {
        if (!input.Blocks.Any(b => b.Handler is not null)) return input;
        MethodProgress.Mark("结构：异常入口归一");
        NativeFunction previous;
        do
        {
            WorkAbort.Check();
            previous = input;
            input = ExceptionEntries.Run(input).Function;
            input = ExceptionSelectors.Run(input, spec).Function;
        } while (!ReferenceEquals(previous, input));
        return input;
    }

    private static bool Reduced(NativeFunction before, NativeFunction after)
    {
        static int Entries(NativeFunction f) => f.Blocks.Count(b => b.Handler is not null);
        static int Branches(NativeFunction f) => f.Blocks.Count(b => b.End is Branch or JumpTable);
        int entries = Entries(after) - Entries(before), branches = Branches(after) - Branches(before);
        return entries <= 0 && branches <= 0 && (entries < 0 || branches < 0);
    }
}
