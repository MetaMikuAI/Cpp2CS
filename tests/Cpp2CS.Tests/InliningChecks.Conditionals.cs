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
    private static void ConditionalAccessorChecks(Assertions checks)
    {
        foreach (string mode in new[] { "Branch", "Select", "Reversed", "ExtraEvent", "ExtraExit", "DifferentCondition", "OtherResultUse" })
        {
            var f = new Fixture();
            var otherDef = new FieldDef { Index = 2, Owner = f.Owner, Name = "Other", Type = f.Integer,
                Attributes = FieldAttributes.Private, Offset = 20, Token = 0x04000003 };
            var other = new FieldRef(otherDef, f.OwnerType);
            f.Owner.Fields = [.. f.Owner.Fields, otherDef]; ((List<FieldDef>)f.Program.Fields).Add(otherDef);
            var getter = f.Method(f.Owner, "Choose", false, false, []);
            var caller = f.Method(f.Caller, "Use", false, true, [f.OwnerType]);
            var touch = f.Method(f.Caller, "Touch", true, true, []);
            var self = new ArgumentValue(-1, f.OwnerType, 64);
            var flag = new FieldValue(self, f.Field, f.Integer, 32);
            var value = new FieldValue(self, other, f.Integer, 32);
            var condition = new ComparisonValue(ComparisonKind.NotEqual, flag, new ConstantValue(0, f.Integer, 32), f.Types.Boolean);
            var seven = new ConstantValue(7, f.Integer, 32);
            var body = new ManagedBody(MethodRef.Open(getter), [new(0, [new ManagedBranch(0, condition, new(1, []), new(2, []))]),
                new(1, [new ManagedReturn(1, value)]), new(2, [new ManagedReturn(2, seven)])]);
            checks.True(AccessorTemplates.Read(body).Template?.Conditional?.Paths.Count == 2, "纯条件模板按返回路径提取：" + mode);
            var choice = new ManagedBody(MethodRef.Open(getter), [new(0, [new ManagedReturn(0, new ChoiceValue(condition, value, seven, f.Integer, 32))])]);
            checks.True(AccessorTemplates.Read(choice).Template?.Conditional?.Paths.Count == 2, "选择项模板使用同一条件路径表示：" + mode);
            var terms = new TermTable(); var entry = new BlockIdentity(); var yes = new BlockIdentity(); var no = new BlockIdentity(); var join = new BlockIdentity();
            var builder = new FunctionBuilder(terms, entry, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var input = terms.Atom(new EntryAtom(new(SlotKind.Integer)), 64); builder.Inputs.Add(new(new(SlotKind.Integer), input));
            MemoryRead Read(FieldRef field, int address)
            {
                var id = new ReadIdentity(); return new(id, terms.Apply(new CoreOperator(CoreOperation.Add), 64, input, terms.Constant(field.Field.Offset, 64)), 32,
                    terms.Atom(new ResultAtom(id), 32)) { Trace = new((ulong)address) };
            }
            var first = Read(f.Field, 100); var second = Read(other, 104);
            var test = terms.Apply(new CoreOperator(CoreOperation.NotEqual), 1, first.Result, terms.Constant(mode == "DifferentCondition" ? 1 : 0, 32));
            Term Extend(Term term) => terms.Concat(term, terms.Constant(0, 64 - term.Width));
            var extra = mode == "ExtraEvent" ? new Statement[] { new Call(new(), new ImageFunction(10), [new(new(SlotKind.Integer), terms.Constant(0, 64))], []) } : [];
            if (mode == "Select")
            {
                var selected = terms.Apply(new CoreOperator(CoreOperation.Select), 32, test, second.Result, terms.Constant(7, 32));
                builder.Blocks.Add(new(entry, [], [first, second], new Return([new(new(SlotKind.Integer), Extend(selected))])));
            }
            else
            {
                bool reversed = mode == "Reversed";
                if (reversed) test = terms.Apply(new CoreOperator(CoreOperation.Not), 1, test);
                builder.Blocks.Add(new(entry, [], [first], new Branch(test, reversed ? no : yes, reversed ? yes : no)));
                builder.Blocks.Add(new(yes, [], [second, .. extra], mode == "ExtraExit" ? new Return([new(new(SlotKind.Integer), Extend(second.Result))]) : new Jump(join)));
                builder.Blocks.Add(new(no, [], [], new Jump(join)));
                var id = new MergeIdentity(); var result = terms.Atom(new ResultAtom(id), 32);
                var output = mode == "OtherResultUse" ? terms.Apply(new CoreOperator(CoreOperation.Add), 32, result, first.Result) : result;
                builder.Blocks.Add(new(join, [new(id, result, mode == "ExtraExit" ? [new(no, terms.Constant(7, 32))] : [new(yes, second.Result), new(no, terms.Constant(7, 32))])], [],
                    new Return([new(new(SlotKind.Integer), Extend(output))])));
            }
            var catalog = RuntimeFunctionCatalog.Select(f.Spec.Layout.UnityVersion, f.Spec.Layout.Triple, f.Spec.Layout.DataModel);
            var calls = new CallNamingQuery(f.Binder, new NamingChecks.Map([new(MethodRef.Open(touch), BindingEntryKind.Ordinary)]), new NamingChecks.RuntimeMap(), catalog);
            var accessors = new AccessorQuery(f.Types, new CachedAccessorTemplates(m => m == getter ? body : null));
            var lowered = new IntegerLowering(builder.Freeze(), MethodRef.Open(caller), f.Binder, f.Types, calls: calls,
                effects: new ManagedCallEffects(calls), spec: f.Spec, accessors: accessors).Run();
            if (mode is "ExtraEvent" or "ExtraExit" or "DifferentCondition" or "OtherResultUse")
                checks.True(lowered.Body is null, "不完整条件区域保持洞：" + mode + " " + lowered.Failure);
            else
            {
                checks.True(lowered.Body is not null, "条件模板下降：" + mode + " " + lowered.Failure);
                if (lowered.Body is not { } complete) continue;
                var recovered = complete.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().ToArray();
                checks.True(recovered is [{ Inlined: true }] && recovered[0].Invocation.Method.Method == getter, "纯区域只发出一次候选调用：" + mode);
                checks.True(complete.Blocks.SelectMany(b => b.Statements).All(s => s is not ManagedBranch), "已证明区域直接续接汇合点：" + mode);
                using var emission = new EmissionFixture(f);
                checks.True(emission.Emitter.Emit([body, complete]).Count == 0, "条件结果通过 CIL 校验：" + mode);
            }
        }
    }
}
