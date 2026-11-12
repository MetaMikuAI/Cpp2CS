using System.Collections.Immutable;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;

namespace Cpp2CS.Tests;

internal static partial class InliningChecks
{
    private static void LocalAccessorChecks(Assertions checks)
    {
        var f = new Fixture(valueOwner: true);
        var getter = f.Method(f.Owner, "Fetch", false, false);
        var touch = f.Method(f.Caller, "Touch", true, true, [new ByRefRef(f.OwnerType)]);
        var caller = f.Method(f.Caller, "Use", false, true);
        var body = new ManagedBody(MethodRef.Open(getter), [new(0, [new ManagedReturn(0,
            new FieldValue(new ArgumentValue(-1, new ByRefRef(f.OwnerType), 64), f.Field, f.Integer, 32))])]);
        var accessors = new AccessorQuery(f.Types, new CachedAccessorTemplates(_ => body));
        var catalog = RuntimeFunctionCatalog.Select(f.Spec.Layout.UnityVersion, f.Spec.Layout.Triple, f.Spec.Layout.DataModel);
        var calls = new CallNamingQuery(f.Binder, new NamingChecks.Map([new(MethodRef.Open(touch), BindingEntryKind.Ordinary)]),
            new NamingChecks.RuntimeMap(), catalog);
        var terms = new TermTable(); var block = new BlockIdentity(); var frame = terms.Atom(new RootAtom(AddressRoot.Frame), 64);
        var builder = new FunctionBuilder(terms, block, 64, new(frame));
        Term Add(Term value, long offset) => terms.Apply(new CoreOperator(CoreOperation.Add), 64, value, terms.Constant(unchecked((ulong)offset), 64));
        var address = Add(frame, -80);
        var statements = new List<Statement>();
        var reads = new List<Term>();
        for (int i = 0; i < 2; i++)
        {
            statements.Add(new Call(new(), new ImageFunction(10), [new(new(SlotKind.Integer), address),
                new(new(SlotKind.Integer, 1), terms.Constant(0, 64))], []) { Trace = new((ulong)(10 + i * 20)) });
            var id = new ReadIdentity(); var result = terms.Atom(new ResultAtom(id), 32); reads.Add(result);
            statements.Add(new MemoryRead(id, Add(address, f.Field.Field.Offset), 32, result) { Trace = new((ulong)(20 + i * 20)) });
        }
        var sum = terms.Apply(new CoreOperator(CoreOperation.Add), 32, reads[0], reads[1]);
        builder.Blocks.Add(new(block, [], statements.ToImmutableArray(), new Return([new(new(SlotKind.Integer), terms.Concat(sum, terms.Constant(0, 32)))])));
        var lowered = new IntegerLowering(builder.Freeze(), MethodRef.Open(caller), f.Binder, f.Types, calls: calls,
            effects: new ManagedCallEffects(calls), spec: f.Spec, accessors: accessors).Run();
        checks.True(lowered.Body is not null, "局部结构体读取能在原位置逆成访问器调用：" + lowered.Failure);
        if (lowered.Body is not { } complete) return;
        var emitted = complete.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().ToArray();
        checks.True(emitted.Length == 4 && emitted.Select(c => c.Invocation.Method.Method).SequenceEqual([touch, getter, touch, getter])
            && emitted.Select(c => c.Address).SequenceEqual([10UL, 20UL, 30UL, 40UL]), "调用留在各自原读取处，不跨改写局部的调用");
        checks.True(emitted.Where(c => c.Inlined).All(c => !c.Invocation.Virtual && c.Invocation.Receiver is AddressValue { Target: LocalValue }),
            "局部结构体的访问器直接使用已有托管地址");
        using var emission = new EmissionFixture(f);
        checks.True(emission.Emitter.Emit([complete]).Count == 0, "局部结构体访问器调用通过 CIL 校验");
    }
}
