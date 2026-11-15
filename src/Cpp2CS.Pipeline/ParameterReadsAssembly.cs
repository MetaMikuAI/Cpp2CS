using System.Diagnostics;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Pipeline;

/// <summary>同一次运行按原生入口与托管声明缓存形参使用事实，不保存已确定摘要的方法体。</summary>
public sealed class ParameterReadsAssembly : IParameterReadsSource
{
    private sealed record Key(ulong Entry, MethodRef Method);
    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<GlobalFacts, ParameterReadsAssembly> values = [];
    private readonly GlobalFacts facts;
    private readonly IMethodStage<Cpp2CS.Input.CodeEntry, NativeFunction> frontend;
    private readonly MethodBinder binder;
    private readonly CallNamingQuery calls;
    private readonly object gate = new();
    private readonly SummaryQuery summaries;
    private readonly NativeFunction scope;
    private readonly HashSet<Key> requested = [];
    private QueryContext context;
    private long ticks;

    private ParameterReadsAssembly(GlobalFacts facts, IMethodStage<Cpp2CS.Input.CodeEntry, NativeFunction> frontend)
    {
        this.facts = facts; this.frontend = frontend;
        var layouts = new FieldLayouts(facts.Spec, facts.Image.PointerWidth, facts.Image.PointerWidth);
        binder = new(new(layouts, facts.Image.PointerWidth * 8), new Aapcs64());
        var spec = facts.Spec.Layout;
        calls = new(binder, new NamingCodeMap(facts.CodeMap), new RuntimeFunctionMap(facts.RuntimeFunctions),
            RuntimeFunctionCatalog.Select(spec.UnityVersion, spec.Triple, spec.DataModel), InternalCallAssembly.Get(facts).Facts);
        var terms = new TermTable(); var entry = new BlockIdentity();
        var builder = new FunctionBuilder(terms, entry, facts.Image.PointerWidth * 8,
            new(terms.Atom(new RootAtom(AddressRoot.Frame), facts.Image.PointerWidth * 8)));
        builder.Blocks.Add(new(entry, [], [], new Unreachable()));
        scope = builder.Freeze(); summaries = new(this); context = NewContext();
    }
    private QueryContext NewContext() => new(scope, facts);
    public static ParameterReadsAssembly Get(GlobalFacts facts, IMethodStage<Cpp2CS.Input.CodeEntry, NativeFunction> frontend) =>
        values.GetValue(facts, f => new(f, frontend));
    public Outcome<ParameterReads> Get(ulong entry, MethodRef method)
    {
        lock (gate)
        {
            var start = Stopwatch.GetTimestamp(); bool completed = false;
            try
            {
                var key = new Key(entry, method); requested.Add(key);
                var result = context.Get(summaries, key); completed = true; return result;
            }
            finally
            {
                // 中止时丢弃未完成查询；摘要查询的局部方法体也随调用退出而释放。
                if (!completed) context = NewContext();
                Interlocked.Add(ref ticks, Stopwatch.GetTimestamp() - start);
            }
        }
    }
    private sealed class SummaryQuery(ParameterReadsAssembly owner) : Query<Key, ParameterReads>
    {
        public override Outcome<ParameterReads> Compute(QueryContext c, Key key)
        {
            Outcome<ParameterReads> No(string code, string message) =>
                Outcome<ParameterReads>.Failure(new("binding.parameter-reads." + code, message));
            if (!key.Method.Method.DeclaresCilBody || (key.Method.Method.ImplAttributes & System.Reflection.MethodImplAttributes.InternalCall) != 0)
                return No("body", "被调方没有托管方法体的原生见证。");
            var entry = owner.facts.CodeMap.At(key.Entry).FirstOrDefault(e => e.Method?.Method == key.Method.Method
                && e.Kind is Cpp2CS.Input.EntryKind.Method or Cpp2CS.Input.EntryKind.GenericMethod);
            if (entry is null) return No("entry", "被调方没有匹配的托管入口。");
            var kind = entry.Kind == Cpp2CS.Input.EntryKind.Method ? BindingEntryKind.Ordinary : BindingEntryKind.SharedGeneric;
            var signature = owner.binder.Entry(key.Method, kind);
            if (signature.Value is null) return No("signature", "被调方形参绑定失败：" + signature.Failure!.Detail);
            var lifted = owner.frontend.Run(entry, new(key.Method.Method, entry, owner.facts));
            return lifted is Completed<NativeFunction> body
                ? ParameterReads.Prove(body.Value, signature.Value, owner.binder, owner.calls,
                    new StateQueries(new ManagedCallEffects(owner.calls), image: owner.facts.Image))
                : Outcome<ParameterReads>.Failure(new("binding.parameter-reads.lift", "被调方原生提升失败。", ((Missing<NativeFunction>)lifted).Hole.Reason));
        }
    }
    public static double Seconds(GlobalFacts facts) => values.TryGetValue(facts, out var value)
        ? (double)value.ticks / Stopwatch.Frequency : 0;
    internal static void Write(GlobalFacts facts, string path)
    {
        if (!values.TryGetValue(facts, out var value)) return;
        lock (value.gate)
        {
            var entries = value.requested.OrderBy(k => k.Entry).ThenBy(k => k.Method.ToString(), StringComparer.Ordinal).Select(key =>
            {
                var result = value.context.Get(value.summaries, key);
                return new { entry = key.Entry, method = key.Method.ToString(), fact = result.IsSuccess ? result.Value : null, reason = result.Why };
            }).ToArray();
            File.WriteAllText(path, System.Text.Json.JsonSerializer.Serialize(new { seconds = Seconds(facts), entries },
                new System.Text.Json.JsonSerializerOptions { WriteIndented = true }));
        }
    }
}
