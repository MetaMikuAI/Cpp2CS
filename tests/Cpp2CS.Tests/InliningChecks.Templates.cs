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
using Cpp2CS.Tests.Execution;
using ManagedValues = Cpp2CS.Managed.ManagedValues;

namespace Cpp2CS.Tests;

internal static partial class InliningChecks
{
    /// <summary>结构体类型的字段：整字段读取与整形参写入是单字段模板，位宽超过 64 位也一样；字段的一部分、夹着运算的不是。</summary>
    private static void WholeFieldTemplateChecks(Assertions checks)
    {
        var f = new Fixture(valueOwner: true);
        var holderType = new DefinitionRef(f.Caller, []);
        var wideDef = new FieldDef { Index = 2, Owner = f.Caller, Name = "Wide", Type = f.OwnerType,
            Attributes = FieldAttributes.Private | FieldAttributes.Static, Offset = 0, Token = 0x04000003 };
        var partDef = new FieldDef { Index = 3, Owner = f.Caller, Name = "Part", Type = f.OwnerType,
            Attributes = FieldAttributes.Private, Offset = 16, Token = 0x04000004 };
        f.Caller.Fields = [wideDef, partDef];
        ((List<FieldDef>)f.Program.Fields).AddRange([wideDef, partDef]);
        var wide = new FieldRef(wideDef, holderType); var part = new FieldRef(partDef, holderType);
        var self = new ArgumentValue(-1, holderType, 64);
        var local = new LocalValue(new LocalId(0), f.OwnerType, 96);
        var staticGetter = f.Method(f.Caller, "get_Wide", false, true, []); staticGetter.ReturnType = f.OwnerType;
        var viaLocal = AccessorTemplates.Read(new ManagedBody(MethodRef.Open(staticGetter), [new(0,
            [new ManagedAssignment(0, local, new StaticFieldValue(wide, f.OwnerType, 96)), new ManagedReturn(4, local)])]));
        checks.True(viaLocal is { Status: AccessorTemplateStatus.Complete, Template: { SingleField: true, Kind: AccessorKind.Getter } a } && a.Field.Equals(wide),
            "静态结构体字段经局部返回是单字段读取模板：" + viaLocal.Failure?.Message);
        var getter = f.Method(f.Caller, "get_Part", false, false, []); getter.ReturnType = f.OwnerType;
        var direct = AccessorTemplates.Read(new ManagedBody(MethodRef.Open(getter), [new(0,
            [new ManagedReturn(0, new FieldValue(self, part, f.OwnerType, 96))])]));
        checks.True(direct is { Status: AccessorTemplateStatus.Complete, Template: { SingleField: true, Kind: AccessorKind.Getter } b } && b.Field.Equals(part),
            "实例结构体字段直接返回是单字段读取模板：" + direct.Failure?.Message);
        var setter = f.Method(f.Caller, "set_Part", true, false, [f.OwnerType]);
        var stored = AccessorTemplates.Read(new ManagedBody(MethodRef.Open(setter), [new(0,
            [new ManagedStore(0, new FieldValue(self, part, f.OwnerType, 96), new ArgumentValue(0, f.OwnerType, 96)), new ManagedReturn(4, null)])]));
        checks.True(stored is { Status: AccessorTemplateStatus.Complete, Template: { SingleField: true, Kind: AccessorKind.Setter } c } && c.Field.Equals(part),
            "整形参写进结构体字段是单字段写入模板：" + stored.Failure?.Message);
        // 字段的一部分不是整字段：结构体字段里的成员仍按原规则（这里宽度合规，是纯表达式但不是单字段模板）。
        var inner = AccessorTemplates.Read(new ManagedBody(MethodRef.Open(f.Method(f.Caller, "get_Inner", false, false, [])), [new(0,
            [new ManagedReturn(0, new FieldValue(new FieldValue(self, part, f.OwnerType, 96), f.Field, f.Integer, 32))])]));
        checks.True(inner.Template?.SingleField != true, "结构体字段里的成员不是这个字段的单字段模板");
        // 宽值参与运算不是纯值。
        var wideLocal = new LocalValue(new LocalId(1), f.OwnerType, 96);
        var mixed = AccessorTemplates.Read(new ManagedBody(MethodRef.Open(staticGetter), [new(0,
            [new ManagedAssignment(0, wideLocal, new ChoiceValue(new ConstantValue(1, f.Integer, 32), new StaticFieldValue(wide, f.OwnerType, 96),
                new FieldValue(self, part, f.OwnerType, 96), f.OwnerType, 96)), new ManagedReturn(4, wideLocal)])]));
        checks.True(mixed.Status != AccessorTemplateStatus.Complete || mixed.Template?.SingleField != true, "宽值经选择不是单字段模板");
    }

    private static void ExpressionAccessorChecks(Assertions checks)
    {
        ExplanationBoundaryChecks(checks);
        ExplanationTypeOrderChecks(checks);
        foreach (string mode in new[] { "Difference", "Comparison", "NegatedComparison", "BooleanReturn", "Nested", "Slice", "MemoryMerge", "Writes", "BooleanWrites", "FieldValueWrites", "MaskedParameter", "Constants", "Partial", "Ambiguous", "CallBetween", "ReadBetween", "Largest", "UnplacedLargest" })
        foreach (bool reverse in mode == "Ambiguous" ? new[] { false, true } : new[] { false })
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
                new ComparisonValue(ComparisonKind.Equal, left, seven, boolType), boolType, 8) : mode is "Slice" or "MemoryMerge" ? left : mode is "Comparison" or "NegatedComparison" or "UnplacedLargest" ? new ComparisonValue(ComparisonKind.Equal, left, seven, f.Integer)
                : mode == "Nested" ? new FieldValue(new FieldValue(self, child, f.OwnerType, 64), f.Field, f.Integer, 32)
                : new BinaryValue(BinaryOperator.Subtract, left, right, f.Integer, 32);
            var stores = new ManagedStatement[] { new ManagedStore(0, left, constant ? seven : mode is "MaskedParameter" or "BooleanWrites"
                ? new BinaryValue(BinaryOperator.And, mode == "BooleanWrites" ? new ConversionValue(ConversionKind.ZeroExtend, parameter, f.Integer, 32) : parameter, new ConstantValue(1, f.Integer, 32), f.Integer, 32) : parameter),
                new ManagedStore(1, right, constant ? new ConstantValue(11, f.Integer, 32) : mode is "MaskedParameter" or "BooleanWrites" ? seven : new BinaryValue(BinaryOperator.Add, mode == "FieldValueWrites" ? right : parameter, seven, f.Integer, 32)),
                new ManagedReturn(2, null) };
            var body = new ManagedBody(MethodRef.Open(method), [new(0, writing ? stores : [new ManagedReturn(0, expression)])]);
            checks.True(AccessorTemplates.Read(body).Status == AccessorTemplateStatus.Complete, "直线模板提取：" + mode);
            var bodies = new Dictionary<MethodDef, ManagedBody> { [method] = body };
            MethodDef? alternative = null;
            if (mode is "Ambiguous" or "Largest" or "UnplacedLargest")
            {
                alternative = f.Method(f.Owner, "Alternative", false, false, []);
                bodies.Add(alternative, new(MethodRef.Open(alternative), [new(0, [new ManagedReturn(0, mode == "Ambiguous" ? expression : left)])]));
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
                // 比较项之外读取还有一次使用：覆盖更大的比较模板放不下，单字段 getter 放得下。
                result = mode == "UnplacedLargest" ? terms.Apply(new CoreOperator(CoreOperation.Add), 32,
                        terms.Concat(terms.Apply(new CoreOperator(CoreOperation.Equal), 1, a, terms.Constant(7, 32)), terms.Constant(0, 31)), a)
                    : mode is "Slice" or "MemoryMerge" ? terms.Concat(terms.Slice(a, 1, 31), terms.Constant(0, 1)) : mode is "Comparison" or "BooleanReturn" or "NegatedComparison" ? terms.Apply(new CoreOperator(mode == "NegatedComparison" ? CoreOperation.NotEqual : CoreOperation.Equal), 1, a, terms.Constant(7, 32))
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
            if (reverse) f.Owner.Methods = f.Owner.Methods.Reverse().ToArray();
            var attempts = new List<AccessorAttempt>();
            var query = new AccessorQuery(f.Types, new CachedAccessorTemplates(m => bodies.GetValueOrDefault(m)), attempts.Add);
            var lowered = new IntegerLowering(builder.Freeze(), MethodRef.Open(caller), f.Binder, f.Types,
                calls: calls, effects: new ManagedCallEffects(calls), spec: f.Spec, names: NamingFacts.Empty, accessors: query).Run();
            if (mode is "Partial" or "CallBetween" or "ReadBetween")
                checks.True(lowered.Body is null, "不完整或被观察的模板保持洞：" + mode + " " + lowered.Failure);
            else if (mode == "MaskedParameter")
                checks.True(lowered.Failure?.Reason.Code == "inline.Accessor.Ambiguous", "形参完整值不可逆时保留歧义：" + lowered.Failure);
            else
            {
                checks.True(lowered.Body is not null, "直线模板下降：" + mode + " " + lowered.Failure);
                if (lowered.Body is not { } complete) continue;
                if (mode == "Ambiguous") checks.True(attempts.Any(a => a.Answer is { Failure: null, Matches: 2 } && a.Answer.Method?.Method == method),
                    "相同表达式模板确定选取并记录个数，不依赖声明次序");
                var recovered = complete.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Where(c => c.Inlined).ToArray();
                var defined = complete.Blocks.SelectMany(b => b.Statements).Select(s => s switch
                    { ManagedCall { Result: { } r } => r.Id, ManagedAssignment a => a.Target.Id, _ => (LocalId?)null }).OfType<LocalId>().ToHashSet();
                checks.True(complete.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk)
                    .OfType<LocalValue>().All(l => defined.Contains(l.Id)), "替换后的全部局部都有定义：" + mode);
                checks.True(recovered is [var selected] && selected.Invocation.Method.Method == (mode == "UnplacedLargest" ? alternative : method),
                    (mode == "UnplacedLargest" ? "大模板放不下时取放得下的单字段 getter：" : "完整覆盖只发出一次目标调用：") + mode);
                checks.True(recovered.Length == 1 && recovered[0].Address == (mode == "FieldValueWrites" ? 104UL : 100UL), "调用保留在首个读或写的位置：" + mode);
                using var emission = new EmissionFixture(f);
                var problems = emission.Emitter.Emit([.. bodies.Values, complete]);
                checks.True(problems.Count == 0, "模板与调用方通过 CIL 写出检查：" + mode + " "
                    + string.Join("；", problems.Select(p => p.Key.Method + "：" + p.Value)));
                if (mode == "Ambiguous" && problems.Count == 0) CompareExplanationCalls(checks, emission.Method(caller), """
                    public class Owner {
                        private int Value, Other;
                        public int Template() => Value - Other;
                        public int Alternative() => Value - Other;
                        public static int Expanded(Owner value) => value.Value - value.Other;
                    }
                    public static class Caller { public static int Output(Owner value) => 0; }
                    """);
            }
        }
    }

    private static void ExplanationBoundaryChecks(Assertions checks)
    {
        foreach (string mode in new[] { "DifferentAccesses", "DifferentResults", "ArgumentPermutations", "SingleFieldPriority", "Unplaced", "DifferentReceivers" })
        foreach (bool reverse in new[] { false, true })
        {
            bool writing = mode is "DifferentAccesses" or "SingleFieldPriority";
            var f = new Fixture();
            FieldRef Field(string name, int offset)
            {
                var field = new FieldDef { Index = f.Program.Fields.Count, Owner = f.Owner, Name = name, Type = f.Integer,
                    Attributes = mode == "DifferentAccesses" ? FieldAttributes.Public : FieldAttributes.Private, Offset = offset, Token = (uint)(0x04000001 + f.Program.Fields.Count) };
                f.Owner.Fields = [.. f.Owner.Fields, field]; ((List<FieldDef>)f.Program.Fields).Add(field);
                return new(field, f.OwnerType);
            }
            var other = Field("Other", 20); var third = Field("Third", 24);
            var method = f.Method(f.Owner, "First", writing, mode == "DifferentReceivers", mode == "ArgumentPermutations" ? [f.Integer, f.Integer]
                : mode == "Unplaced" ? [f.Integer] : mode == "DifferentReceivers" ? [f.OwnerType] : []);
            var caller = f.Method(f.Caller, "Use", writing, true,
                mode == "ArgumentPermutations" ? [f.OwnerType, f.Integer, f.Integer] : [f.OwnerType]);
            var self = new ArgumentValue(-1, f.OwnerType, 64);
            FieldValue Value(FieldRef field) => new(self, field, f.Integer, 32);
            ConstantValue Constant(ulong value) => new(value, f.Integer, 32);
            BinaryValue Add(ManagedValue a, ManagedValue b) => new(BinaryOperator.Add, a, b, f.Integer, 32);
            ManagedBody Body(MethodDef candidate, params ManagedStatement[] statements) => new(MethodRef.Open(candidate), [new(0, statements)]);
            var bodies = new Dictionary<MethodDef, ManagedBody>();
            MethodDef? alternative = mode == "ArgumentPermutations" ? null : f.Method(f.Owner, "Second", writing, false,
                mode == "SingleFieldPriority" ? [f.Integer] : []);
            if (mode == "DifferentAccesses")
            {
                bodies[method] = Body(method, new ManagedStore(0, Value(other), Constant(11)),
                    new ManagedStore(1, Value(f.Field), Constant(7)), new ManagedReturn(2, null));
                bodies[alternative!] = Body(alternative!, new ManagedStore(0, Value(f.Field), Constant(7)),
                    new ManagedStore(1, Value(third), Constant(13)), new ManagedReturn(2, null));
            }
            else if (mode == "SingleFieldPriority")
            {
                bodies[method] = Body(method, new ManagedStore(0, Value(f.Field), Constant(7)), new ManagedReturn(1, null));
                bodies[alternative!] = Body(alternative!, new ManagedStore(0, Value(f.Field), new ArgumentValue(0, f.Integer, 32)), new ManagedReturn(1, null));
            }
            else if (mode == "DifferentResults")
            {
                bodies[method] = Body(method, new ManagedReturn(0, Add(Value(f.Field), Constant(1))));
                bodies[alternative!] = Body(alternative!, new ManagedReturn(0, Add(Value(f.Field), Constant(2))));
            }
            else if (mode == "DifferentReceivers")
            {
                bodies[method] = Body(method, new ManagedReturn(0,
                    new FieldValue(new ArgumentValue(0, f.OwnerType, 64), f.Field, f.Integer, 32)));
                bodies[alternative!] = Body(alternative!, new ManagedReturn(0, Value(f.Field)));
            }
            else if (mode == "Unplaced")
            {
                bodies[method] = Body(method, new ManagedReturn(0, Add(Value(f.Field), new BinaryValue(BinaryOperator.And,
                    new ArgumentValue(0, f.Integer, 32), Constant(0), f.Integer, 32))));
                bodies[alternative!] = Body(alternative!, new ManagedReturn(0, Value(f.Field)));
            }
            else bodies[method] = Body(method, new ManagedReturn(0, Add(Value(f.Field), Add(new ArgumentValue(0, f.Integer, 32),
                new ArgumentValue(1, f.Integer, 32)))));
            var t = new TermTable(); var entry = new BlockIdentity();
            var builder = new FunctionBuilder(t, entry, 64, new(t.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var input = t.Atom(new EntryAtom(new(SlotKind.Integer)), 64); builder.Inputs.Add(new(new(SlotKind.Integer), input));
            Term Address(FieldRef field) => t.Apply(new CoreOperator(CoreOperation.Add), 64, input, t.Constant(field.Field.Offset, 64));
            var statements = new List<Statement>();
            void Store(FieldRef field, int value) => statements.Add(new MemoryWrite(new(), Address(field), 32, t.Constant(value, 32)));
            Term result = t.Constant(0, 32);
            if (writing)
            {
                if (mode == "DifferentAccesses") Store(other, 11);
                Store(f.Field, 7);
                if (mode == "DifferentAccesses") Store(third, 13);
            }
            else
            {
                var read = new ReadIdentity(); result = t.Atom(new ResultAtom(read), 32);
                statements.Add(new MemoryRead(read, Address(f.Field), 32, result));
                if (mode == "DifferentResults") result = t.Apply(new CoreOperator(CoreOperation.Multiply), 32,
                    t.Apply(new CoreOperator(CoreOperation.Add), 32, result, t.Constant(1, 32)),
                    t.Apply(new CoreOperator(CoreOperation.Add), 32, result, t.Constant(2, 32)));
                else if (mode == "ArgumentPermutations")
                {
                    var values = new List<Term>();
                    for (int i = 1; i <= 2; i++)
                    {
                        var argument = t.Atom(new EntryAtom(new(SlotKind.Integer, i)), 64); builder.Inputs.Add(new(new(SlotKind.Integer, i), argument));
                        values.Add(t.Slice(argument, 0, 32));
                    }
                    result = t.Apply(new CoreOperator(CoreOperation.Add), 32, result, t.Apply(new CoreOperator(CoreOperation.Add), 32, values[0], values[1]));
                }
            }
            builder.Blocks.Add(new(entry, [], [.. statements], new Return(writing ? [] : [new(new(SlotKind.Integer), t.Concat(result, t.Constant(0, 32)))])));
            if (reverse) f.Owner.Methods = f.Owner.Methods.Reverse().ToArray();
            var attempts = new List<AccessorAttempt>();
            var lowered = new IntegerLowering(builder.Freeze(), MethodRef.Open(caller), f.Binder, f.Types, calls: f.Calls, spec: f.Spec,
                accessors: new(f.Types, new CachedAccessorTemplates(bodies.GetValueOrDefault), attempts.Add)).Run();
            if (mode is "SingleFieldPriority" or "Unplaced")
            {
                checks.True(lowered.Body?.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Single().Invocation.Method.Method == alternative
                    && attempts.Any(a => a.Answer.Failure is null && a.Answer.Matches == (mode == "Unplaced" ? 1 : 2)),
                    "单字段模板优先，放不下的解释不参与选择：" + mode + " " + lowered.Failure);
            }
            else
            {
                checks.True(lowered.Body is null && lowered.Failure?.Reason.Code == "inline.Accessor.Ambiguous",
                    "不同访问、不同值或同一方法实参排列保留歧义：" + mode + " " + lowered.Failure);
                if (mode == "ArgumentPermutations") checks.True(lowered.Failure?.Reason.Cause?.Message == "同一个方法的不同实参代入",
                    "完整可逆的两个实参互换仍保留同一方法歧义");
            }
        }
    }


    private static void CompareExplanationCalls(Assertions checks, Mono.Cecil.MethodDefinition emitted, string source)
    {
        using var compiled = new CompiledSource(source);
        var output = compiled.Method("Caller", "Output"); output.Body = emitted.Body;
        var core = compiled.Module.TypeSystem.Object.Resolve().Module;
        Mono.Cecil.TypeReference MapType(Mono.Cecil.TypeReference type) => compiled.Module.ImportReference(
            compiled.Module.GetType(type.FullName) ?? core.GetType(type.FullName));
        foreach (var local in output.Body.Variables) local.VariableType = MapType(local.VariableType);
        foreach (var instruction in output.Body.Instructions) instruction.Operand = instruction.Operand switch
        {
            Mono.Cecil.MethodReference method => compiled.Module.GetType(method.DeclaringType.FullName).Methods.Single(m => m.FullName == method.FullName),
            Mono.Cecil.FieldReference field => compiled.Module.GetType(field.DeclaringType.FullName).Fields.Single(f => f.Name == field.Name),
            Mono.Cecil.TypeReference type => MapType(type),
            Mono.Cecil.ParameterDefinition parameter => output.Parameters[parameter.Index],
            _ => instruction.Operand,
        };
        var compared = CilComparison.Compare(compiled.Method("Owner", "Expanded"), output, cases: 64);
        checks.True(compared.Status == CilComparisonStatus.Match && compared.CompletedCases == 64,
            "确定选取后的调用与展开的原生语义逐输入对照：" + compared);
    }


    private static void ExplanationTypeOrderChecks(Assertions checks)
    {
        foreach (bool reverse in new[] { false, true })
        {
            var f = new Fixture(externalCaller: true, receiverOwner: true);
            var definition = new FieldDef { Index = 2, Owner = f.Owner, Name = "Counter", Type = f.Integer,
                Attributes = FieldAttributes.Assembly | FieldAttributes.Static, Offset = 4, Token = 0x04000003 };
            f.Owner.Fields = [.. f.Owner.Fields, definition]; ((List<FieldDef>)f.Program.Fields).Add(definition);
            var field = new FieldRef(definition, f.OwnerType);
            var first = f.Method(f.ReceiverOwner!, "First", false, true);
            var second = f.Method(f.Owner, "Second", false, true);
            var caller = f.Method(f.Caller, "Use", false, true);
            ManagedBody Body(MethodDef method) => new(MethodRef.Open(method), [new(0,
                [new ManagedReturn(0, new StaticFieldValue(field, f.Integer, 32))])]);
            var bodies = new Dictionary<MethodDef, ManagedBody> { [first] = Body(first), [second] = Body(second) };
            if (reverse) ((List<MethodDef>)f.Program.Methods).Reverse();
            var attempts = new List<AccessorAttempt>();
            var (native, names) = f.Function(field, false);
            var lowered = new IntegerLowering(native, MethodRef.Open(caller), f.Binder, f.Types, calls: f.Calls, spec: f.Spec, names: names,
                accessors: new(f.Types, new CachedAccessorTemplates(bodies.GetValueOrDefault), attempts.Add)).Run();
            checks.True(lowered.Body?.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Single().Invocation.Method.Method == second
                && attempts.Any(a => a.Answer is { Failure: null, Matches: 2 }), "单字段模板先按声明类型全名排序，再按元数据次序，不依赖发现次序");
        }
    }

}
