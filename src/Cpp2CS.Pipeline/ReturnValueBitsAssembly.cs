using System.Diagnostics;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Pipeline;

/// <summary>按入口和托管声明缓存返回摘要；跨方法依赖只读取已证明的扩展事实。</summary>
public sealed class ReturnValueBitsAssembly : IReturnValueBitsSource
{
    private sealed record Key(ulong Entry, MethodRef Method);
    private sealed record Body(NativeFunction Function, SignatureBinding Signature);
    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<GlobalFacts, ReturnValueBitsAssembly> values = [];
    // 提升出的方法体只在摘要未定时保留；摘要一旦确定就释放，键留作报告。
    private readonly Dictionary<Key, Outcome<Body>> bodies = [];
    private readonly HashSet<Key> requested = [];
    private readonly GlobalFacts facts;
    private readonly IMethodStage<Cpp2CS.Input.CodeEntry, NativeFunction> frontend;
    private readonly MethodBinder binder;
    private readonly object gate = new();
    private readonly SummaryQuery summaries;
    private readonly NativeFunction scope;
    private QueryContext context;
    private long ticks;
    private static readonly Reason Pending = new("binding.return-bits.pending", "循环或依赖尚未建立返回高位事实。");

    private ReturnValueBitsAssembly(GlobalFacts facts, IMethodStage<Cpp2CS.Input.CodeEntry, NativeFunction> frontend)
    {
        this.facts = facts; this.frontend = frontend;
        var layouts = new FieldLayouts(facts.Spec, facts.Image.PointerWidth, facts.Image.PointerWidth);
        binder = new(new(layouts, facts.Image.PointerWidth * 8), new Aapcs64());
        // 运行级查询的键指向各自的原生快照；逐方法状态查询另有上下文。
        var terms = new TermTable(); var entry = new BlockIdentity();
        var builder = new FunctionBuilder(terms, entry, facts.Image.PointerWidth * 8,
            new(terms.Atom(new RootAtom(AddressRoot.Frame), facts.Image.PointerWidth * 8)));
        builder.Blocks.Add(new(entry, [], [], new Unreachable()));
        scope = builder.Freeze();
        summaries = new(this);
        context = NewContext();
    }
    private QueryContext NewContext() => new(scope, facts, new FixedPointGroup(1_000_000,
        FixedPointMember.Create(summaries, _ => new BitsLattice())));
    public static ReturnValueBitsAssembly Get(GlobalFacts facts, IMethodStage<Cpp2CS.Input.CodeEntry, NativeFunction> frontend) =>
        values.GetValue(facts, f => new(f, frontend));
    public Outcome<ReturnValueBits> Get(ulong entry, MethodRef method)
    {
        lock (gate)
        {
            var start = Stopwatch.GetTimestamp();
            bool completed = false;
            try
            {
                var result = context.Get(summaries, new(entry, method));
                completed = true;
                return !result.IsSuccess ? result.Propagate<ReturnValueBits>() : result.Value is { } bits
                    ? Outcome<ReturnValueBits>.Success(bits) : Outcome<ReturnValueBits>.Failure(Pending);
            }
            finally
            {
                // 调用方的方法时限可以在查询中途中止计算；中止留下未完成的条目，这个上下文不能再用，换一个新的。
                if (!completed) { context = NewContext(); bodies.Clear(); }
                Interlocked.Add(ref ticks, Stopwatch.GetTimestamp() - start);
            }
        }
    }
    private Outcome<Body> GetBody(Key key)
    {
        if (bodies.TryGetValue(key, out var known)) return known;
        var result = Build(key);
        bodies.Add(key, result); requested.Add(key);
        return result;
    }
    private Outcome<Body> Build(Key key)
    {
        if (!key.Method.Method.DeclaresCilBody || (key.Method.Method.ImplAttributes & System.Reflection.MethodImplAttributes.InternalCall) != 0)
            return Outcome<Body>.Failure(new("binding.return-bits.body", "被调方没有托管方法体的原生见证。"));
        var entry = facts.CodeMap.At(key.Entry).FirstOrDefault(e => e.Method?.Method == key.Method.Method
            && e.Kind is Cpp2CS.Input.EntryKind.Method or Cpp2CS.Input.EntryKind.GenericMethod);
        if (entry is null) return Outcome<Body>.Failure(new("binding.return-bits.entry", "被调方没有匹配的托管入口。"));
        var kind = entry.Kind == Cpp2CS.Input.EntryKind.Method ? BindingEntryKind.Ordinary : BindingEntryKind.SharedGeneric;
        var signature = binder.Entry(key.Method, kind);
        if (signature.Value is null) return Outcome<Body>.Failure(new("binding.return-bits.signature", signature.Failure!.Detail));
        var result = frontend.Run(entry, new(key.Method.Method, entry, facts));
        return result is Completed<NativeFunction> lifted ? Outcome<Body>.Success(new(lifted.Value, signature.Value))
            : Outcome<Body>.Failure(((Missing<NativeFunction>)result).Hole.Reason);
    }
    private sealed class BitsLattice : ILattice<ReturnValueBits?>
    {
        public ReturnValueBits? Bottom => null;
        public ReturnValueBits? Join(ReturnValueBits? a, ReturnValueBits? b) => a ?? b;
        public bool LessOrEqual(ReturnValueBits? a, ReturnValueBits? b) => a is null || a == b;
    }
    private sealed class SummaryQuery(ReturnValueBitsAssembly owner) : Query<Key, ReturnValueBits?>
    {
        public override Outcome<ReturnValueBits?> Compute(QueryContext c, Key key)
        {
            var body = owner.GetBody(key);
            if (!body.IsSuccess) return body.Propagate<ReturnValueBits?>();
            bool pending = false;
            var calls = body.Value.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().ToDictionary(call => call.Identity);
            Outcome<ReturnValueBits>? Dependency(Term value)
            {
                if (value.Identity is not ResultAtom { Definition: CallIdentity id } || !calls.TryGetValue(id, out var call)
                    || call.Target is not ImageFunction target) return null;
                var entries = owner.facts.CodeMap.At(target.EntryOffset).Where(e => e.Method is not null
                    && e.Kind is Cpp2CS.Input.EntryKind.Method or Cpp2CS.Input.EntryKind.GenericMethod).DistinctBy(e => e.Method).ToArray();
                if (entries is not [{ Method: { } method } entry]) return null;
                var signature = owner.binder.Entry(method, entry.Kind == Cpp2CS.Input.EntryKind.Method ? BindingEntryKind.Ordinary : BindingEntryKind.SharedGeneric);
                if (signature.Value is not { Signature.ReturnType: Cpp2CS.Native.Abi.CInteger { Bits: 8 or 16 },
                        Slots.Return.Pieces: [{ ValueOffset: 0, SlotOffset: 0 } piece] }
                    || call.Results.SingleOrDefault(r => r.Slot == piece.Slot)?.Value != value) return null;
                var result = c.Get(this, new(target.EntryOffset, method));
                if (!result.IsSuccess) return result.Propagate<ReturnValueBits>();
                if (result.Value is { } bits) return Outcome<ReturnValueBits>.Success(bits);
                pending = true;
                return null;
            }
            var fact = ReturnValueBits.Prove(body.Value.Function, body.Value.Signature,
                key.Method.Concrete(key.Method.Method.ReturnType), Dependency);
            if (!fact.IsSuccess && pending) return Outcome<ReturnValueBits?>.Success(null);
            owner.bodies.Remove(key);
            return fact.IsSuccess ? Outcome<ReturnValueBits?>.Success(fact.Value) : fact.Propagate<ReturnValueBits?>();
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
                return new { entry = key.Entry, method = key.Method.ToString(), fact = result.IsSuccess ? result.Value : null,
                    reason = result.IsSuccess ? result.Value is null ? Pending : null : result.Why };
            }).ToArray();
            File.WriteAllText(path, System.Text.Json.JsonSerializer.Serialize(new { seconds = Seconds(facts), entries },
                new System.Text.Json.JsonSerializerOptions { WriteIndented = true }));
        }
    }
}
