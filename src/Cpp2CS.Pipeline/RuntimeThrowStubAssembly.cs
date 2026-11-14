using System.Collections.Concurrent;
using System.Diagnostics;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Native;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.RuntimeFunctions;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Pipeline;

/// <summary>替换桩按被调入口核对，成功与失败均缓存；调用点不重复提升。</summary>
public sealed class RuntimeThrowStubAssembly
{
    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<GlobalFacts, RuntimeThrowStubAssembly> values = [];
    private readonly ConcurrentDictionary<ulong, Lazy<Outcome<bool>>> entries = [];
    private readonly GlobalFacts facts;
    private readonly IMethodStage<Cpp2CS.Input.CodeEntry, NativeFunction> frontend;
    private readonly MethodBinder binder;
    private readonly FieldLayouts layouts;
    private readonly CallNamingQuery calls;
    private long requests, lifted, liftTicks, structureTicks;
    private RuntimeThrowStubAssembly(GlobalFacts facts, IMethodStage<Cpp2CS.Input.CodeEntry, NativeFunction> frontend)
    {
        this.facts = facts; this.frontend = frontend;
        layouts = new(facts.Spec, facts.Image.PointerWidth, facts.Image.PointerWidth);
        binder = new(new(layouts, facts.Image.PointerWidth * 8), new Aapcs64());
        var spec = facts.Spec.Layout;
        calls = new(binder, new NamingCodeMap(facts.CodeMap), new RuntimeFunctionMap(facts.RuntimeFunctions),
            RuntimeFunctionCatalog.Select(spec.UnityVersion, spec.Triple, spec.DataModel));
    }
    public static RuntimeThrowStubAssembly Get(GlobalFacts facts, IMethodStage<Cpp2CS.Input.CodeEntry, NativeFunction> frontend) =>
        values.GetValue(facts, f => new(f, frontend));
    public Outcome<bool> Check(ulong entry)
    {
        Interlocked.Increment(ref requests);
        return entries.GetOrAdd(entry, address => new(() => Build(address))).Value;
    }
    private Outcome<bool> Build(ulong address)
    {
        var entry = facts.CodeMap.ByAddress.TryGetValue(address, out var candidates) ? candidates.FirstOrDefault(e => e.Method is not null) : null;
        if (entry?.Method is null) return Outcome<bool>.Failure(new("call-body.entry", "被调方没有托管入口。"));
        var context = new MethodContext(entry.Method.Method, entry, facts);
        var start = Stopwatch.GetTimestamp();
        var result = frontend.Run(entry, context);
        Interlocked.Add(ref liftTicks, Stopwatch.GetTimestamp() - start);
        Interlocked.Increment(ref lifted);
        if (result is Missing<NativeFunction> missing) return Outcome<bool>.Failure(missing.Hole.Reason);
        var function = ((Completed<NativeFunction>)result).Value;
        // 普通方法不需要结构恢复；只有确实调用登记桩抛出的入口才检查整个桩体。
        if (!function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Any(c => calls.RuntimeIdentity(c.Target)?.Operation.Il.Name == "ThrowProfile"))
            return Outcome<bool>.Success(false);
        start = Stopwatch.GetTimestamp();
        var transformed = StructureRecovery.Run(function, context, binder, BindingEntryKind.Ordinary, layouts);
        bool stub = RuntimeThrowStubs.IsStub(transformed.Function, calls);
        Interlocked.Add(ref structureTicks, Stopwatch.GetTimestamp() - start);
        return Outcome<bool>.Success(stub);
    }
    public static double Seconds(GlobalFacts facts) => values.TryGetValue(facts, out var value)
        ? (double)(value.liftTicks + value.structureTicks) / Stopwatch.Frequency : 0;
    internal static void Write(GlobalFacts facts, string path)
    {
        if (!values.TryGetValue(facts, out var value)) return;
        File.WriteAllText(path, System.Text.Json.JsonSerializer.Serialize(new
        {
            requests = value.requests, entries = value.entries.Count, lifted = value.lifted,
            liftSeconds = (double)value.liftTicks / Stopwatch.Frequency,
            structureSeconds = (double)value.structureTicks / Stopwatch.Frequency,
            bodies = value.entries.OrderBy(p => p.Key).Select(p => new { entry = p.Key,
                stub = p.Value.Value.IsSuccess ? p.Value.Value.Value : (bool?)null, reason = p.Value.Value.Why }),
        }, new System.Text.Json.JsonSerializerOptions { WriteIndented = true }));
    }
}
