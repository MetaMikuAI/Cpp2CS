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
    private static void ExpressionAccessorChecks(Assertions checks)
    {
        foreach (string mode in new[] { "Difference", "Comparison", "NegatedComparison", "BooleanReturn", "Nested", "Slice", "MemoryMerge", "Writes", "BooleanWrites", "FieldValueWrites", "MaskedParameter", "Constants", "Partial", "Ambiguous", "CallBetween", "ReadBetween", "Largest" })
        {
            var f = new Fixture();
            var otherDef = new FieldDef { Index = 2, Owner = f.Owner, Name = "Other", Type = f.Integer,
                Attributes = FieldAttributes.Private, Offset = 20, Token = 0x04000003 };
            var childDef = new FieldDef { Index = 3, Owner = f.Owner, Name = "Child", Type = f.OwnerType,
                Attributes = FieldAttributes.Private, Offset = 24, Token = 0x04000004 };
            f.Owner.Fields = [.. f.Owner.Fields, otherDef, childDef];
            ((List<FieldDef>)f.Program.Fields).AddRange([otherDef, childDef]);
            var other = new FieldRef(otherDef, f.OwnerType); var child = new FieldRef(childDef, f.OwnerType);
            bool writing = mode is "Writes" or "BooleanWrites" or "FieldValueWrites" or "MaskedParameter" or "Constants" or "ReadBetween";
            bool constant = mode == "Constants";
            var boolType = new DefinitionRef(f.Program.Types.Single(t => t.Namespace == "System" && t.Name == "Boolean"), []);
            var parameterType = mode == "BooleanWrites" ? boolType : f.Integer;
            var method = f.Method(f.Owner, "Template", writing, false, writing && !constant ? [parameterType] : []);
            if (mode is "BooleanReturn" or "NegatedComparison") method.ReturnType = boolType;
            var caller = f.Method(f.Caller, "Use", writing, true, (writing && !constant || mode == "MemoryMerge") ? [f.OwnerType, parameterType] : [f.OwnerType]);
            var touch = f.Method(f.Caller, "Touch", true, true, mode == "MemoryMerge" ? [f.OwnerType] : []);
            var self = new ArgumentValue(-1, f.OwnerType, 64); var parameter = new ArgumentValue(0, parameterType, mode == "BooleanWrites" ? 8 : 32);
            var left = new FieldValue(self, f.Field, f.Integer, 32); var right = new FieldValue(self, other, f.Integer, 32);
            var seven = new ConstantValue(7, f.Integer, 32);
            ManagedValue expression = mode == "BooleanReturn" ? new ConversionValue(ConversionKind.ZeroExtend,
                new ComparisonValue(ComparisonKind.Equal, left, seven, boolType), boolType, 8) : mode is "Slice" or "MemoryMerge" ? left : mode is "Comparison" or "NegatedComparison" ? new ComparisonValue(ComparisonKind.Equal, left, seven, f.Integer)
                : mode == "Nested" ? new FieldValue(new FieldValue(self, child, f.OwnerType, 64), f.Field, f.Integer, 32)
                : new BinaryValue(BinaryOperator.Subtract, left, right, f.Integer, 32);
            var stores = new ManagedStatement[] { new ManagedStore(0, left, constant ? seven : mode is "MaskedParameter" or "BooleanWrites"
                ? new BinaryValue(BinaryOperator.And, mode == "BooleanWrites" ? new ConversionValue(ConversionKind.ZeroExtend, parameter, f.Integer, 32) : parameter, new ConstantValue(1, f.Integer, 32), f.Integer, 32) : parameter),
                new ManagedStore(1, right, constant ? new ConstantValue(11, f.Integer, 32) : mode is "MaskedParameter" or "BooleanWrites" ? seven : new BinaryValue(BinaryOperator.Add, mode == "FieldValueWrites" ? right : parameter, seven, f.Integer, 32)),
                new ManagedReturn(2, null) };
            var body = new ManagedBody(MethodRef.Open(method), [new(0, writing ? stores : [new ManagedReturn(0, expression)])]);
            checks.True(AccessorTemplates.Read(body).Status == AccessorTemplateStatus.Complete, "直线模板提取：" + mode);
            var bodies = new Dictionary<MethodDef, ManagedBody> { [method] = body };
            if (mode is "Ambiguous" or "Largest")
            {
                var second = f.Method(f.Owner, "Alternative", false, false, []);
                bodies.Add(second, new(MethodRef.Open(second), [new(0, [new ManagedReturn(0, mode == "Largest" ? left : expression)])]));
            }
            var catalog = RuntimeFunctionCatalog.Select(f.Spec.Layout.UnityVersion, f.Spec.Layout.Triple, f.Spec.Layout.DataModel);
            var calls = new CallNamingQuery(f.Binder, new NamingChecks.Map([new(MethodRef.Open(touch), BindingEntryKind.Ordinary)]), new NamingChecks.RuntimeMap(), catalog);
            var terms = new TermTable(); var block = new BlockIdentity(); var builder = new FunctionBuilder(terms, block, 64,
                new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var root = terms.Atom(new EntryAtom(new(SlotKind.Integer)), 64);
            var input = terms.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64);
            builder.Inputs.Add(new(new(SlotKind.Integer), root)); builder.Inputs.Add(new(new(SlotKind.Integer, 1), input));
            var statements = new List<Statement>();
            Term Address(Term receiver, long offset) => terms.Apply(new CoreOperator(CoreOperation.Add), 64, receiver, terms.Constant(offset, 64));
            Term Read(Term receiver, FieldRef field, int width = 32)
            {
                var id = new ReadIdentity(); var value = terms.Atom(new ResultAtom(id), width);
                statements.Add(new MemoryRead(id, Address(receiver, field.Field.Offset), width, value) { Trace = new((ulong)(100 + statements.Count * 4)) });
                return value;
            }
            void Write(FieldRef field, Term value) => statements.Add(new MemoryWrite(new(), Address(root, field.Field.Offset), 32, value)
                { Trace = new((ulong)(100 + statements.Count * 4)) });
            Term result;
            if (writing)
            {
                var value = constant ? terms.Constant(7, 32) : mode == "BooleanWrites" ? terms.Concat(terms.Slice(input, 0, 1), terms.Constant(0, 31)) : terms.Slice(input, 0, 32);
                var old = mode == "FieldValueWrites" ? Read(root, other) : value;
                Write(f.Field, mode == "MaskedParameter" ? terms.Apply(new CoreOperator(CoreOperation.And), 32, value, terms.Constant(1, 32)) : value);
                if (mode == "ReadBetween") Read(root, f.Field);
                Write(other, constant ? terms.Constant(11, 32) : mode is "MaskedParameter" or "BooleanWrites" ? terms.Constant(7, 32) : terms.Apply(new CoreOperator(CoreOperation.Add), 32, old, terms.Constant(7, 32)));
                result = terms.Constant(0, 32);
            }
            else if (mode == "Nested") result = Read(Read(root, child, 64), f.Field);
            else
            {
                var a = Read(root, f.Field);
                if (mode == "CallBetween") statements.Add(new Call(new(), new ImageFunction(10), [new(new(SlotKind.Integer), terms.Constant(0, 64))], []));
                result = mode is "Slice" or "MemoryMerge" ? terms.Concat(terms.Slice(a, 1, 31), terms.Constant(0, 1)) : mode is "Comparison" or "BooleanReturn" or "NegatedComparison" ? terms.Apply(new CoreOperator(mode == "NegatedComparison" ? CoreOperation.NotEqual : CoreOperation.Equal), 1, a, terms.Constant(7, 32))
                    : terms.Apply(new CoreOperator(mode == "Partial" ? CoreOperation.Add : CoreOperation.Subtract), 32, a, Read(root, other));
            }
            var returned = result.Width == 64 ? result : terms.Concat(result, terms.Constant(0, 64 - result.Width));
            if (mode == "MemoryMerge")
            {
                var yes = new BlockIdentity(); var no = new BlockIdentity(); var join = new BlockIdentity();
                builder.Blocks.Add(new(block, [], [], new Branch(terms.Apply(new CoreOperator(CoreOperation.Equal), 1,
                    terms.Slice(input, 0, 32), terms.Constant(0, 32)), yes, no)));
                builder.Blocks.Add(new(yes, [], [new Call(new(), new ImageFunction(10),
                    [new(new(SlotKind.Integer), root), new(new(SlotKind.Integer, 1), terms.Constant(0, 64))], [])], new Jump(join)));
                builder.Blocks.Add(new(no, [], [], new Jump(join)));
                builder.Blocks.Add(new(join, [], statements.ToImmutableArray(), new Return([new(new(SlotKind.Integer), returned)])));
            }
            else builder.Blocks.Add(new(block, [], statements.ToImmutableArray(), new Return(writing ? [] : [new(new(SlotKind.Integer), returned)])));
            var query = new AccessorQuery(f.Types, new CachedAccessorTemplates(m => bodies.GetValueOrDefault(m)));
            var lowered = new IntegerLowering(builder.Freeze(), MethodRef.Open(caller), f.Binder, f.Types,
                calls: calls, effects: new ManagedCallEffects(calls), spec: f.Spec, names: NamingFacts.Empty, accessors: query).Run();
            if (mode is "Partial" or "CallBetween" or "ReadBetween")
                checks.True(lowered.Body is null, "不完整或被观察的模板保持洞：" + mode + " " + lowered.Failure);
            else if (mode is "Ambiguous" or "MaskedParameter")
                checks.True(lowered.Failure?.Reason.Code == "inline.Accessor.Ambiguous", "同一最大项有两个候选时报歧义：" + lowered.Failure);
            else
            {
                checks.True(lowered.Body is not null, "直线模板下降：" + mode + " " + lowered.Failure);
                if (lowered.Body is not { } complete) continue;
                var recovered = complete.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Where(c => c.Inlined).ToArray();
                var defined = complete.Blocks.SelectMany(b => b.Statements).Select(s => s switch
                    { ManagedCall { Result: { } r } => r.Id, ManagedAssignment a => a.Target.Id, _ => (LocalId?)null }).OfType<LocalId>().ToHashSet();
                checks.True(complete.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk)
                    .OfType<LocalValue>().All(l => defined.Contains(l.Id)), "替换后的全部局部都有定义：" + mode);
                checks.True(recovered is [var selected] && selected.Invocation.Method.Method == method, "完整覆盖只发出一次目标调用：" + mode);
                checks.True(recovered.Length == 1 && recovered[0].Address == (mode == "FieldValueWrites" ? 104UL : 100UL), "调用保留在首个读或写的位置：" + mode);
                using var emission = new EmissionFixture(f);
                var problems = emission.Emitter.Emit([.. bodies.Values, complete]);
                checks.True(problems.Count == 0, "模板与调用方通过 CIL 写出检查：" + mode + " "
                    + string.Join("；", problems.Select(p => p.Key.Method + "：" + p.Value)));
            }
        }
    }
}
