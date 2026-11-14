using System.Collections.Immutable;
using System.Diagnostics;
using System.Reflection;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.RuntimeFunctions;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Pipeline;

public sealed record InternalCallSurvey(InternalCallFacts Facts, int Total, int Forwarders, int Caches,
    ImmutableDictionary<string, int> Other, double Seconds)
{
    public ImmutableDictionary<string, double> Timings { get; init; } = ImmutableDictionary<string, double>.Empty;
    public int LiftedEntries { get; init; }
}

/// <summary>每份全局事实只提升一次内部调用包装；产品发现过程不读取符号。</summary>
public static class InternalCallAssembly
{
    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<GlobalFacts, Lazy<InternalCallSurvey>> values = [];
    public static InternalCallSurvey Get(GlobalFacts facts) => values.GetValue(facts, f => new(() => Build(f))).Value;
    public static double Seconds(GlobalFacts facts) => values.TryGetValue(facts, out var value) && value.IsValueCreated ? value.Value.Seconds : 0;
    private static InternalCallSurvey Build(GlobalFacts facts)
    {
        var watch = Stopwatch.StartNew();
        var methods = facts.Model.Methods.Where(m => (m.ImplAttributes & MethodImplAttributes.InternalCall) != 0).ToArray();
        var other = new Dictionary<string, int>(); var direct = new List<(ulong Entry, InternalCallForwarder Forwarder)>();
        var caches = new List<(ulong Cache, InternalCallForwarder Forwarder)>(); int forwarded = 0, cached = 0;
        void Reject(string code) => other[code] = other.GetValueOrDefault(code) + 1;
        var frontend = new FrontendStage([new FrontendProvider("arm64", RecoverySession.DefaultComponents)]);
        var layouts = new FieldLayouts(facts.Spec, facts.Image.PointerWidth, facts.Image.PointerWidth);
        var binder = new MethodBinder(new(layouts, facts.Image.PointerWidth * 8), new Aapcs64());
        var state = new StateQueries(image: facts.Image);
        var entries = facts.CodeMap.Entries.Where(e => e.Method is not null && e.Kind == Cpp2CS.Input.EntryKind.Method)
            .ToLookup(e => e.Method!.Method);
        // 运行时定位先完成；事实建立用时不重复包含前端组件和目录定位的耗时。
        _ = facts.RuntimeFunctions;
        watch.Restart();
        long liftTicks = 0, structureTicks = 0, proofTicks = 0;
        var bodies = new Dictionary<ulong, StageResult<NativeFunction>>();
        foreach (var method in methods)
        {
            var candidates = entries[method].ToArray();
            if (candidates.Length != 1 || GenericWitness.IsGeneric(method)) { Reject("icall.wrapper.entry"); continue; }
            var entry = candidates[0]; var context = new MethodContext(method, entry, facts);
            var start = Stopwatch.GetTimestamp();
            if (!bodies.TryGetValue(entry.Address, out var lifted)) bodies.Add(entry.Address, lifted = frontend.Run(entry, context));
            liftTicks += Stopwatch.GetTimestamp() - start;
            if (lifted is not Completed<NativeFunction> body) { Reject("icall.wrapper.frontend"); continue; }
            start = Stopwatch.GetTimestamp();
            var raw = InternalCallWrappers.Forwarder(MethodRef.Open(method), body.Value, binder, state);
            proofTicks += Stopwatch.GetTimestamp() - start;
            if (raw.IsSuccess && body.Value.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single().Target is ImageFunction plain
                && !facts.CodeMap.ByAddress.ContainsKey(plain.EntryOffset)
                && facts.RuntimeFunctions.Find(plain)?.Function.Operation.Observation is not (Cpp2CS.Runtime.RuntimeObservation.Unobservable or Cpp2CS.Runtime.RuntimeObservation.IdempotentEvent))
            { direct.Add((plain.EntryOffset, raw.Value with { WrapperEntry = entry.Address })); forwarded++; continue; }
            start = Stopwatch.GetTimestamp();
            var transformed = StructureRecovery.Run(body.Value, context, binder, BindingEntryKind.Ordinary, layouts,
                InternalCallFacts.Empty, MethodRef.Open(method));
            structureTicks += Stopwatch.GetTimestamp() - start;
            if (!transformed.InternalCallCaches.IsEmpty)
            {
                caches.AddRange(transformed.InternalCallCaches); cached++; continue;
            }
            start = Stopwatch.GetTimestamp();
            var proof = InternalCallWrappers.Forwarder(MethodRef.Open(method), transformed.Function, binder, state);
            proofTicks += Stopwatch.GetTimestamp() - start;
            if (proof.IsSuccess && transformed.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single().Target is ImageFunction target && !facts.CodeMap.ByAddress.ContainsKey(target.EntryOffset))
            { direct.Add((target.EntryOffset, proof.Value with { WrapperEntry = entry.Address })); forwarded++; }
            else Reject(proof.Why?.Code ?? "icall.wrapper.target");
        }
        return new(new(direct, caches), methods.Length, forwarded, cached, other.ToImmutableDictionary(), watch.Elapsed.TotalSeconds)
        {
            LiftedEntries = bodies.Count,
            Timings = new Dictionary<string, double>
            {
                ["提升"] = (double)liftTicks / Stopwatch.Frequency, ["结构"] = (double)structureTicks / Stopwatch.Frequency,
                ["转发证明"] = (double)proofTicks / Stopwatch.Frequency,
            }.ToImmutableDictionary(),
        };
    }

    internal static void Write(GlobalFacts facts, string path)
    {
        if (!values.TryGetValue(facts, out var value) || !value.IsValueCreated) return;
        var result = value.Value;
        File.WriteAllText(path, System.Text.Json.JsonSerializer.Serialize(new
        {
            result.Total, result.Forwarders, result.Caches, result.Other, result.Seconds, result.Timings, result.LiftedEntries, result.Facts.Ambiguous,
            direct = result.Facts.Direct.OrderBy(p => p.Key).Select(p => new { entry = p.Key, method = RecoverySession.Identity(p.Value.Method.Method), name = p.Value.Method.ToString(), inputs = p.Value.Inputs }),
            caches = result.Facts.Caches.OrderBy(p => p.Key).Select(p => new { cache = p.Key, method = RecoverySession.Identity(p.Value.Method.Method), name = p.Value.Method.ToString(), inputs = p.Value.Inputs }),
        }, new System.Text.Json.JsonSerializerOptions { WriteIndented = true }));
    }
}
