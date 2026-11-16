using System.Collections.Immutable;
using System.Reflection;
using Mono.Cecil.Cil;
using Cpp2CS.Kernel.Queries;
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
    private static void NestedStructAccessorChecks(Assertions checks)
    {
        static IEnumerable<Reason> Reasons(Reason? why)
        {
            for (; why is not null; why = why.Cause) yield return why;
        }
        foreach (var mode in new[] { "Public", "Private", "Static", "Ambiguous", "NoGetter", "Write", "Receiver", "Parts", "Accessible", "SplitReads" })
        {
            var f = new Fixture(valueOwner: true, fieldOffset: 0, receiverOwner: mode == "Receiver");
            f.Owner.Size = 16;
            var holder = new DefinitionRef(f.Caller, []);
            var a = new FieldDef { Index = 2, Owner = f.Owner, Name = "a", Type = f.Integer,
                Attributes = FieldAttributes.Public, Offset = 0, Token = 0x04000003 };
            var b = new FieldDef { Index = 3, Owner = f.Owner, Name = "b", Type = f.Types.Int64,
                Attributes = FieldAttributes.Private, Offset = 8, Token = 0x04000004 };
            f.Owner.Fields = [a, b];
            var field = new FieldDef { Index = 4, Owner = f.Caller, Name = "F", Type = f.OwnerType,
                Attributes = (mode == "Accessible" ? FieldAttributes.Public : FieldAttributes.Private)
                    | (mode == "Static" ? FieldAttributes.Static : 0), Offset = mode == "Static" ? 0 : 16, Token = 0x04000005 };
            var parent = new FieldDef { Index = 5, Owner = f.ReceiverOwner ?? f.Caller, Name = "Parent", Type = holder,
                Attributes = FieldAttributes.Private, Offset = 40, Token = 0x04000006 };
            f.Caller.Fields = f.ReceiverOwner is null ? [field, parent] : [field];
            if (f.ReceiverOwner is { } receiverOwner) receiverOwner.Fields = [parent];
            ((List<FieldDef>)f.Program.Fields).AddRange([a, b, field, parent]);
            var whole = new FieldRef(field, holder); var privatePart = new FieldRef(b, f.OwnerType);
            var getter = f.Method(f.Caller, "get_F", false, mode == "Static"); getter.ReturnType = f.OwnerType;
            var innerGetter = f.Method(f.Owner, "get_B", false, false); innerGetter.ReturnType = f.Types.Int64;
            var consumer = f.Program.Types.Single(t => t.FullName == "System.Object");
            var caller = f.Method(consumer, "Use", mode == "Write", true, mode == "Static" ? [] :
                [f.ReceiverOwner is { } receiverType ? new DefinitionRef(receiverType, []) : holder]);
            if (mode == "Private") caller.ReturnType = f.Types.Int64;
            ManagedBody GetterBody(MethodDef method) => new(MethodRef.Open(method), [new(0, [new ManagedReturn(0,
                mode == "Static" ? new StaticFieldValue(whole, f.OwnerType, 0)
                    : new FieldValue(new ArgumentValue(-1, holder, 64), whole, f.OwnerType, 0))])]);
            var bodies = new Dictionary<MethodDef, ManagedBody>
            {
                [getter] = GetterBody(getter),
                [innerGetter] = new(MethodRef.Open(innerGetter), [new(0, [new ManagedReturn(0,
                    new FieldValue(new ArgumentValue(-1, new ByRefRef(f.OwnerType), 64), privatePart, f.Types.Int64, 64))])]),
            };
            if (mode == "Ambiguous")
            {
                var another = f.Method(f.Caller, "Another", false, false); another.ReturnType = f.OwnerType;
                bodies[another] = GetterBody(another);
            }
            if (mode == "NoGetter") f.Caller.Methods = [];
            var terms = new TermTable(); var entry = new BlockIdentity();
            var builder = new FunctionBuilder(terms, entry, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var root = terms.Atom(new EntryAtom(new(SlotKind.Integer)), 64);
            if (mode != "Static") builder.Inputs.Add(new(new(SlotKind.Integer), root));
            var statements = new List<Statement>(); var names = NamingFacts.Empty;
            Term Add(Term value, int offset) => terms.Apply(new CoreOperator(CoreOperation.Add), 64, value, terms.Constant(offset, 64));
            Term Read(Term address, int width)
            {
                var id = new ReadIdentity(); var result = terms.Atom(new ResultAtom(id), width);
                statements.Add(new MemoryRead(id, address, width, result) { Trace = new((ulong)(100 + statements.Count * 4)) });
                return result;
            }
            if (mode == "Static")
            {
                var image = terms.Atom(new RootAtom(AddressRoot.Image), 64); builder.ImageBase = image;
                var klass = Read(Add(image, 256), 64);
                root = Read(Add(klass, (int)f.Spec.Layout.Field("Il2CppClass", "static_fields").ByteOffset), 64);
                names = names with { Slots = names.Slots.Add(256, Outcome<MetadataEntity>.Success(new ClassEntity(holder))) };
            }
            if (mode == "Receiver") root = Read(Add(root, parent.Offset), 64);
            var address = Add(root, field.Offset + (mode == "Private" ? b.Offset : a.Offset));
            Term value;
            if (mode == "Write")
            {
                statements.Add(new MemoryWrite(new(), address, 32, terms.Constant(7, 32)) { Trace = new(100) });
                value = terms.Constant(0, 32);
            }
            else value = Read(address, mode == "Private" ? 64 : 32);
            if (mode == "Parts") value = terms.Apply(new CoreOperator(CoreOperation.Add), 32, value,
                terms.Slice(Read(Add(root, field.Offset + b.Offset), 64), 0, 32));
            if (mode == "SplitReads")
            {
                var yes = new BlockIdentity(); var no = new BlockIdentity();
                var condition = terms.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64);
                caller.Parameters = [.. caller.Parameters, new("condition", f.Integer, 0, null, false)];
                builder.Inputs.Add(new(new(SlotKind.Integer, 1), condition));
                var first = (MemoryRead)statements.Single(); var secondId = new ReadIdentity();
                var second = new MemoryRead(secondId, first.Address, 32, terms.Atom(new ResultAtom(secondId), 32)) { Trace = new(104) };
                builder.Blocks.Add(new(entry, [], [], new Branch(terms.Apply(new CoreOperator(CoreOperation.Equal), 1,
                    terms.Slice(condition, 0, 32), terms.Constant(0, 32)), yes, no)));
                builder.Blocks.Add(new(yes, [], [first], new Return([new(new(SlotKind.Integer), terms.Concat(first.Result, terms.Constant(0, 32)))])));
                builder.Blocks.Add(new(no, [], [second], new Return([new(new(SlotKind.Integer), terms.Concat(second.Result, terms.Constant(0, 32)))])));
            }
            else builder.Blocks.Add(new(entry, [], [.. statements], new Return(mode == "Write" ? [] :
                [new(new(SlotKind.Integer), value.Width == 64 ? value : terms.Concat(value, terms.Constant(0, 32)))])));
            var attempts = new List<AccessorAttempt>();
            var accessors = new AccessorQuery(f.Types, new CachedAccessorTemplates(bodies.GetValueOrDefault), attempts.Add);
            var lowered = new IntegerLowering(builder.Freeze(), MethodRef.Open(caller), f.Binder, f.Types,
                calls: f.Calls, spec: f.Spec, names: names, accessors: accessors).Run();
            if (mode is "Ambiguous" or "NoGetter" or "Write" or "Receiver" or "SplitReads")
            {
                checks.True(lowered.Body is null, "结构体内部访问反例保留洞：" + mode);
                var why = lowered.Failure?.Reason;
                checks.True(mode switch
                {
                    "Ambiguous" => why?.Code == "inline.Accessor.Ambiguous",
                    "NoGetter" or "Receiver" => attempts.Any(t => t.Answer.NoneReason == AccessorNoneReason.NoCandidates),
                    "SplitReads" => Reasons(why).Any(r => r.Code == "inline.Accessor.Placement.ReadDominance"),
                    _ => why?.Code == "inline.Accessor.None" && Reasons(why).Any(r => r.Code == "inline.Accessor.Placement.NestedAccess"
                            && r.Message.Contains("写入", StringComparison.Ordinal)),
                }, "结构体内部访问失败原因：" + mode + " " + lowered.Failure);
                continue;
            }
            checks.True(lowered.Body is not null, "结构体内部读取下降：" + mode + " " + lowered.Failure);
            if (lowered.Body is not { } complete) continue;
            var positions = complete.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>()
                .Where(a => ManagedValues.Walk(a.Value).Any(v => v is FieldValue { Accessor: { } instance } && instance.Method.Method == getter
                    || v is StaticFieldValue { Accessor: { } shared } && shared.Method.Method == getter)).Select(a => a.Address).ToArray();
            checks.True(positions.SequenceEqual(mode switch { "Parts" => new[] { 100UL, 104UL }, "Static" => [108UL],
                "Accessible" => [], _ => [100UL] }), "整字段 getter 保留每次原读取的位置：" + mode);
            using var emission = new EmissionFixture(f);
            var problems = emission.Emitter.Emit([.. bodies.Values, complete]);
            checks.True(problems.Count == 0, "结构体整体 getter 与子路径通过 CIL 校验：" + mode + " " + string.Join("；", problems.Values));
            if (problems.Count != 0) continue;
            var instructions = emission.Method(caller).Body.Instructions;
            var calls = instructions.Where(i => i.OpCode == OpCodes.Call || i.OpCode == OpCodes.Callvirt)
                .Select(i => ((Mono.Cecil.MethodReference)i.Operand).Name).ToArray();
            checks.True(calls.SequenceEqual(mode switch
            {
                "Private" => new[] { "get_F", "get_B" },
                "Parts" => new[] { "get_F", "get_F", "get_B" },
                "Accessible" => [],
                _ => new[] { "get_F" },
            }), "各部分读取在原处调用整字段 getter，私有子字段再调子 getter：" + mode);
            if (mode == "Private") checks.True(instructions.Any(i => i.OpCode == OpCodes.Stloc)
                && instructions.Any(i => i.OpCode == OpCodes.Ldloca), "结构体 getter 结果复用临时局部与 ldloca");
            else if (mode != "Parts") checks.True(instructions.Any(i => i.OpCode == OpCodes.Ldfld
                && i.Operand is Mono.Cecil.FieldReference part && part.Name == "a"), "可访问子字段保持普通 ldfld：" + mode);
        }
    }

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
