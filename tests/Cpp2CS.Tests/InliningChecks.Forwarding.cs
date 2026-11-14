using System.Collections.Immutable;
using System.Reflection;
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
    private static void ForwardingChecks(Assertions checks)
    {
        foreach (string mode in new[] { "Getter", "Arguments", "Virtual", "Void", "DifferentArgument", "DifferentIdentity", "OtherUse", "TwoCandidates", "ExtraWrite" })
        {
            var f = new Fixture();
            bool argument = mode is "Arguments" or "DifferentArgument";
            bool empty = mode == "Void";
            var child = new FieldDef { Index = 2, Owner = f.Owner, Name = "Child", Type = f.OwnerType,
                Attributes = FieldAttributes.Private, Offset = 24, Token = 0x04000003 };
            f.Owner.Fields = [.. f.Owner.Fields, child]; ((List<FieldDef>)f.Program.Fields).Add(child);
            var field = new FieldRef(child, f.OwnerType);
            var outer = f.Method(f.Owner, "Forward", empty, false, argument ? [f.Integer] : []);
            var target = f.Method(f.Owner, "Target", empty, false, argument ? [f.Integer, f.Integer] : [], virtualMethod: mode == "Virtual", slot: 4);
            var different = f.Method(f.Owner, "Different", empty, false, argument ? [f.Integer, f.Integer] : []);
            var caller = f.Method(f.Caller, "Use", empty, true, argument ? [f.OwnerType, f.Integer] : [f.OwnerType]);
            var self = new ArgumentValue(-1, f.OwnerType, 64);
            var receiver = new FieldValue(self, field, f.OwnerType, 64);
            var parameter = new ArgumentValue(0, f.Integer, 32);
            var flag = new ConstantValue(7, f.Integer, 32);
            var local = empty ? null : new LocalValue(new(0), f.Integer, 32);
            ManagedBody Body(MethodDef method) => new(MethodRef.Open(method), [new(0,
                [new ManagedCall(0, new(MethodRef.Open(target), receiver, argument ? [parameter, flag] : [], mode == "Virtual"), local), new ManagedReturn(1, local)])]);
            var bodies = new Dictionary<MethodDef, ManagedBody> { [outer] = Body(outer) };
            if (mode == "TwoCandidates")
            {
                var second = f.Method(f.Owner, "Alternative", false, false, []); bodies.Add(second, Body(second));
            }
            checks.True(AccessorTemplates.Read(bodies[outer]).Template?.Call?.Method.Method == target, "单次转调模板提取：" + mode);
            var catalog = RuntimeFunctionCatalog.Select(f.Spec.Layout.UnityVersion, f.Spec.Layout.Triple, f.Spec.Layout.DataModel);
            var calls = new CallNamingQuery(f.Binder, new NamingChecks.Map([new(MethodRef.Open(mode == "DifferentIdentity" ? different : target), BindingEntryKind.Ordinary)]), new NamingChecks.RuntimeMap(), catalog);
            var terms = new TermTable(); var entry = new BlockIdentity();
            var builder = new FunctionBuilder(terms, entry, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var input = terms.Atom(new EntryAtom(new(SlotKind.Integer)), 64);
            var arg = terms.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64);
            builder.Inputs.Add(new(new(SlotKind.Integer), input)); builder.Inputs.Add(new(new(SlotKind.Integer, 1), arg));
            var readId = new ReadIdentity(); var loaded = terms.Atom(new ResultAtom(readId), 64);
            var address = terms.Apply(new CoreOperator(CoreOperation.Add), 64, input, terms.Constant(24, 64));
            var callId = new CallIdentity(); var result = terms.Atom(new ResultAtom(callId), 64);
            var args = new List<SlotValue> { new(new(SlotKind.Integer), loaded) };
            if (argument)
            {
                args.Add(new(new(SlotKind.Integer, 1), arg));
                args.Add(new(new(SlotKind.Integer, 2), terms.Constant(mode == "DifferentArgument" ? 8 : 7, 64)));
            }
            args.Add(new(new(SlotKind.Integer, argument ? 3 : 1), terms.Constant(0, 64)));
            var statements = new List<Statement> { new MemoryRead(readId, address, 64, loaded) { Trace = new(100) } };
            if (mode == "ExtraWrite") statements.Add(new MemoryWrite(new(), address, 64, input));
            CallTarget callTarget = new ImageFunction(10);
            if (mode == "Virtual")
            {
                Term Read(Term root, long offset)
                {
                    var id = new ReadIdentity(); var value = terms.Atom(new ResultAtom(id), 64);
                    statements.Add(new MemoryRead(id, terms.Apply(new CoreOperator(CoreOperation.Add), 64, root, terms.Constant(offset, 64)), 64, value));
                    return value;
                }
                var klass = Read(loaded, f.Spec.Layout.Field("Il2CppObject", "klass").ByteOffset);
                var basis = f.Spec.Layout.VtableStart + 4 * f.Spec.Layout.VtableSlotSize;
                callTarget = new ComputedTarget(Read(klass, basis + f.Spec.Layout.Field("VirtualInvokeData", "methodPtr").ByteOffset));
                args[^1] = new(new(SlotKind.Integer, 1), Read(klass, basis + f.Spec.Layout.Field("VirtualInvokeData", "method").ByteOffset));
            }
            statements.Add(new Call(callId, callTarget, args.ToImmutableArray(), empty ? [] : [new(new(SlotKind.Integer), result)]) { Trace = new(104) });
            var returned = terms.Slice(result, 0, 32);
            if (mode == "OtherUse") returned = terms.Apply(new CoreOperator(CoreOperation.Select), 32,
                terms.Apply(new CoreOperator(CoreOperation.Equal), 1, loaded, terms.Constant(0, 64)), returned, terms.Constant(7, 32));
            builder.Blocks.Add(new(entry, [], statements.ToImmutableArray(), new Return(empty ? [] : [new(new(SlotKind.Integer), terms.Concat(returned, terms.Constant(0, 32)))])));
            var accessors = new AccessorQuery(f.Types, new CachedAccessorTemplates(bodies.GetValueOrDefault));
            var lowered = new IntegerLowering(builder.Freeze(), MethodRef.Open(caller), f.Binder, f.Types,
                calls: calls, effects: new ManagedCallEffects(calls), spec: f.Spec, accessors: accessors).Run();
            if (mode is "DifferentArgument" or "DifferentIdentity" or "OtherUse" or "ExtraWrite")
                checks.True(lowered.Body is null, "转调身份、实参、事件与其他使用反例保持洞：" + mode + " " + lowered.Failure);
            else if (mode == "TwoCandidates") checks.True(lowered.Failure?.Reason.Code == "inline.Accessor.Ambiguous", "同一转调的两个外层候选保留歧义：" + lowered.Failure);
            else
            {
                checks.True(lowered.Body is not null, "转调下降：" + mode + " " + lowered.Failure);
                if (lowered.Body is not { } body) continue;
                var recovered = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().ToArray();
                checks.True(recovered is [{ Inlined: true, Address: 104 }] && recovered[0].Invocation.Method.Method == outer, "转调在原调用位置只发出一次外层调用：" + mode);
                using var emission = new EmissionFixture(f);
                checks.True(emission.Emitter.Emit([.. bodies.Values, body]).Count == 0, "转调结果与实参通过 CIL 校验：" + mode);
            }
        }
    }
}
