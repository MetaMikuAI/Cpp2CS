using System.Collections.Immutable;
using Cpp2CS.Input;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using System.Reflection;
using Mono.Cecil.Cil;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Recovery.Lowering;

namespace Cpp2CS.Tests;

internal static partial class InliningChecks
{
    private static void GenericAccessorChecks(Assertions checks)
    {
        ClosedGenericAccessorChecks(checks);
        foreach (bool parameterField in new[] { false, true })
        {
            var f = new Fixture(generic: true, genericField: parameterField);
            var getter = f.Method(f.Owner, "Fetch", false, false); getter.ReturnType = f.Field.Field.Type;
            var setter = f.Method(f.Owner, "Put", true, false);
            setter.Parameters = [new("value", f.Field.Field.Type, 0, null, false)];
            var caller = f.Method(f.Caller, "Use", false, true);
            var canonical = new MethodRef(getter, [f.Types.Object], []);
            var getterFunction = f.Function(f.Field, false, width: parameterField ? 64 : 32).Function;
            var setterFunction = f.Function(f.Field, true, width: parameterField ? 64 : 32).Function;
            var entries = new[]
            {
                new CodeEntry(16, EntryKind.GenericMethod, canonical with { TypeArguments = [f.Types.String] }, 0, null),
                new CodeEntry(24, EntryKind.GenericMethod, canonical, 1, null),
                new CodeEntry(32, EntryKind.GenericMethod, new(setter, [f.Types.Object], []), 2, null),
            };
            GlobalFacts Facts(IEnumerable<CodeEntry> selected)
            {
                var array = selected.ToArray();
                var map = new Registrations { CodeRegistration = 0, MetadataRegistration = 0, Entries = array,
                    ByAddress = array.GroupBy(e => e.Address).ToDictionary(g => g.Key, g => g.ToImmutableArray()),
                    Rgctx = new Dictionary<(string, uint), ImmutableArray<RgctxEntry>>(), MetadataUsageSlots = [],
                    TypePointers = new Dictionary<ulong, int>(), InvokerOf = new Dictionary<MethodDef, int>(), UsageEntities = new Dictionary<ulong, Usage>() };
                return new(new InputMemoryImage(), f.Program, map, f.Spec, "arm64");
            }
            var frontend = new GenericTemplateFrontend(m => m == setter ? setterFunction : getterFunction);
            var source = new AccessorTemplateSource(Facts(entries), frontend);
            checks.True(source.Get(getter).Status == AccessorTemplateStatus.Complete, "泛型定义按规范见证恢复读模板：" + source.Get(getter));
            checks.True(source.Get(setter).Status == AccessorTemplateStatus.Complete, "泛型定义按规范见证恢复写模板：" + source.Get(setter));
            checks.True(frontend.Entries.Count == 2 && frontend.Entries.All(e => e.TypeArguments.SequenceEqual([f.Types.Object])),
                "模板选择全 object 入口，不选择地址靠前的其他实例");
            var query = new AccessorQuery(f.Types, source);
            foreach (var argument in new TypeRef[] { f.Integer, f.Types.String, new GenericParameterRef("U", false, 0) })
            {
                var instance = new DefinitionRef(f.Owner, [argument]);
                var field = new FieldRef(f.Field.Field, instance);
                foreach (var kind in new[] { AccessorKind.Getter, AccessorKind.Setter })
                {
                    var result = query.Resolve(new(MethodRef.Open(caller), 0, field, instance, kind, true));
                    checks.True(result.Method?.Method == (kind == AccessorKind.Getter ? getter : setter)
                        && result.Method.DeclaringType.Equals(instance), "开放字段模板实例化到锚点类型：" + instance + " " + kind);
                }
                if (argument.ContainsGenericParameter()) continue;
                foreach (bool write in new[] { false, true })
                {
                    var valueType = parameterField ? argument : f.Integer;
                    caller.ReturnType = write ? f.Void : valueType;
                    caller.Parameters = (write ? new[] { instance, valueType } : new TypeRef[] { instance })
                        .Select(t => new ParameterDef("value", t, 0, null, false)).ToArray();
                    var width = parameterField ? f.Types.ValueWidth(argument) : 32;
                    var native = f.Function(field, write, width: width).Function;
                    var resultBody = new IntegerLowering(native, MethodRef.Open(caller), f.Binder, f.Types,
                        calls: f.Calls, spec: f.Spec, accessors: query).Run();
                    checks.True(resultBody.Body is not null, "泛型实例访问器下降：" + instance + " " + write + " " + resultBody.Failure);
                    if (resultBody.Body is { } body)
                    {
                        var call = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Single();
                        checks.True(call.Invocation.Method.DeclaringType.Equals(instance) && call.Invocation.Virtual,
                            "写出的实例访问器保留实参和空检查");
                        using var emission = new EmissionFixture(f);
                        checks.True(emission.Emitter.Emit([body]).Count == 0, "泛型实例调用通过 CIL 写出校验");
                    }
                }
            }
            var noWitnessFrontend = new GenericTemplateFrontend(_ => getterFunction);
            var noWitness = new AccessorTemplateSource(Facts(entries.Take(1)), noWitnessFrontend);
            checks.True(noWitness.Get(getter) is { Status: AccessorTemplateStatus.Incomplete, Failure.Code: "lowering.Generic.Witness" }
                && noWitnessFrontend.Entries.Count == 0, "没有规范入口就不恢复或采用模板");
            var another = f.Method(f.Owner, "Other", false, false); another.ReturnType = f.Field.Field.Type;
            var openField = new FieldValue(new ArgumentValue(-1, f.OwnerType, 64), f.Field, f.Field.Field.Type, parameterField ? 64 : 32);
            ManagedBody Body(MethodDef m) => new(MethodRef.Open(m), [new(0, [new ManagedReturn(0, openField)])]);
            var ambiguous = new AccessorQuery(f.Types, new CachedAccessorTemplates(Body));
            var closed = new DefinitionRef(f.Owner, [f.Integer]);
            foreach (bool reverse in new[] { false, true })
            {
                f.Owner.Methods = reverse ? [another, getter] : [getter, another];
                var choice = ambiguous.Resolve(new(MethodRef.Open(caller), 0, new(f.Field.Field, closed), closed, AccessorKind.Getter, true));
                checks.True(choice is { Failure: null, Matches: 2 } && choice.Method?.Method == getter && choice.Method.DeclaringType.Equals(closed),
                    "同一泛型声明实例的相同模板确定选取，不依赖声明次序");
            }
            another.GenericParameters = [new() { Name = "M", Position = 0, Attributes = 0 }];
            f.Owner.Methods = [another];
            int requested = 0;
            var excluded = new AccessorQuery(f.Types, new CachedAccessorTemplates(m => { requested++; return Body(m); }));
            checks.True(excluded.Resolve(new(MethodRef.Open(caller), 0, new(f.Field.Field, closed), closed, AccessorKind.Getter, true))
                .NoneReason == AccessorNoneReason.GenericMethod && requested == 0, "泛型方法单列原因且不取模板");
        }
    }

    private static void ClosedGenericAccessorChecks(Assertions checks)
    {
        foreach (bool parameterField in new[] { true, false })
        {
            var f = new Fixture(generic: true, genericField: true, valueOwner: true, fieldOffset: 0);
            var number = new FieldDef { Index = 2, Owner = f.Owner, Name = "Number", Type = f.Integer,
                Attributes = FieldAttributes.Private, Offset = 8, Token = 0x04000003 };
            f.Owner.Fields = [.. f.Owner.Fields, number]; ((List<FieldDef>)f.Program.Fields).Add(number);
            var target = parameterField ? f.Field.Field : number;
            var getter = f.Method(f.Owner, "Fetch", false, false); getter.ReturnType = target.Type;
            var setter = f.Method(f.Owner, "Put", true, false); setter.Parameters = [new("value", target.Type, 0, null, false)];
            var caller = f.Method(f.Caller, "Use", false, true);
            MethodRef On(MethodDef m, TypeRef t) => new(m, [t], []);
            NativeFunction Native(MethodRef method, FieldDef field, bool write, bool extraWrite = false)
            {
                var instance = (DefinitionRef)method.DeclaringType;
                var layout = f.Types.Layouts.Of(instance)!;
                var offset = layout.Fields.Single(s => s.Field == field).Offset - layout.ObjectHeaderSize;
                int width = f.Types.ValueWidth(method.Concrete(field.Type));
                var t = new TermTable(); var block = new BlockIdentity();
                var builder = new FunctionBuilder(t, block, 64, new(t.Atom(new RootAtom(AddressRoot.Frame), 64)));
                var self = t.Atom(new EntryAtom(new(SlotKind.Integer)), 64);
                var input = t.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64);
                builder.Inputs.Add(new(new(SlotKind.Integer), self)); builder.Inputs.Add(new(new(SlotKind.Integer, 1), input));
                var address = t.Apply(new CoreOperator(CoreOperation.Add), 64, self, t.Constant(offset, 64));
                var statements = new List<Statement>(); Term value;
                if (write) { value = t.Constant(0, width); statements.Add(new MemoryWrite(new(), address, width, t.Slice(input, 0, width))); }
                else { var id = new ReadIdentity(); value = t.Atom(new ResultAtom(id), width); statements.Add(new MemoryRead(id, address, width, value)); }
                if (extraWrite) statements.Add(new MemoryWrite(new(), address, width, t.Constant(3, width)));
                builder.Blocks.Add(new(block, [], [.. statements], new Return(write ? [] : [new(new(SlotKind.Integer),
                    width == 64 ? value : t.Concat(value, t.Constant(0, 64 - width)))])));
                return builder.Freeze();
            }
            var entries = new[] { getter, setter }.SelectMany((m, i) => new[]
            {
                new CodeEntry((ulong)(16 + i * 16), EntryKind.GenericMethod, On(m, f.Types.Object), i * 2, null),
                new CodeEntry((ulong)(24 + i * 16), EntryKind.GenericMethod, On(m, f.Integer), i * 2 + 1, null),
            }).ToArray();
            GlobalFacts Facts(IEnumerable<CodeEntry> selected)
            {
                var array = selected.ToArray();
                var map = new Registrations { CodeRegistration = 0, MetadataRegistration = 0, Entries = array,
                    ByAddress = array.GroupBy(e => e.Address).ToDictionary(g => g.Key, g => g.ToImmutableArray()),
                    Rgctx = new Dictionary<(string, uint), ImmutableArray<RgctxEntry>>(), MetadataUsageSlots = [],
                    TypePointers = new Dictionary<ulong, int>(), InvokerOf = new Dictionary<MethodDef, int>(), UsageEntities = new Dictionary<ulong, Usage>() };
                return new(new InputMemoryImage(), f.Program, map, f.Spec, "arm64");
            }
            var frontend = new ClosedTemplateFrontend(m => Native(m, target, m.Method == setter));
            var source = new AccessorTemplateSource(Facts(entries), frontend);
            var query = new AccessorQuery(f.Types, source);
            AccessorAnswer Ask(AccessorQuery q, TypeRef argument, bool write = false) => q.Resolve(new(MethodRef.Open(caller), 0,
                new(target, new DefinitionRef(f.Owner, [argument])), new ByRefRef(new DefinitionRef(f.Owner, [argument])),
                write ? AccessorKind.Setter : AccessorKind.Getter, true));
            foreach (var argument in new TypeRef[] { f.Types.String, f.Integer, f.Types.Int64 })
            {
                var instance = new DefinitionRef(f.Owner, [argument]);
                foreach (bool write in new[] { false, true })
                {
                    var chosen = Ask(query, argument, write);
                    checks.True(chosen.Method?.Method == (write ? setter : getter) && chosen.Method.DeclaringType.Equals(instance),
                        "封闭单字段模板保留现场类型：" + argument + " " + parameterField + " " + write + " " + chosen.Failure);
                    checks.True(chosen.Witness?.Code == (argument.Equals(f.Types.Int64) ? "inline.Accessor.Witness.Assumption" : "inline.Accessor.Witness"),
                        "见证注明直接对应或借用假设：" + argument + " " + write);
                    var fieldType = target.Type.Substitute([argument], []);
                    caller.ReturnType = write ? f.Void : fieldType;
                    caller.Parameters = (write ? new TypeRef[] { new ByRefRef(instance), fieldType }
                        : new TypeRef[] { new ByRefRef(instance) }).Select(t => new ParameterDef("value", t, 0, null, false)).ToArray();
                    var lowered = new IntegerLowering(Native(On(getter, argument), target, write), MethodRef.Open(caller), f.Binder, f.Types,
                        calls: f.Calls, spec: f.Spec, accessors: query).Run();
                    checks.True(lowered.Body is not null, "封闭模板沿既有下降路径恢复调用：" + argument + " " + write + " " + lowered.Failure);
                    if (lowered.Body is not { } body) continue;
                    var call = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Single();
                    checks.True(call.Invocation.Method.DeclaringType.Equals(instance) && !call.Invocation.Virtual,
                        "借用见证仍调用现场实例且值接收者不使用 callvirt");
                    using var emission = new EmissionFixture(f);
                    var problems = emission.Emitter.Emit([body]);
                    checks.True(problems.Count == 0, "封闭访问器调用通过输出校验：" + string.Join("；", problems.Values));
                    if (problems.Count == 0)
                        checks.True(emission.Method(caller).Body.Instructions.Any(i => i.OpCode == OpCodes.Call
                            && i.Operand is Mono.Cecil.MethodReference { DeclaringType: Mono.Cecil.GenericInstanceType declaring }
                            && declaring.GenericArguments[0].FullName == ((DefinitionRef)argument).Definition.FullName),
                            "CIL call 的声明类型参数来自现场");
                }
            }
            int recovered = frontend.Entries.Count;
            source.Get(On(getter, f.Types.String)); source.Get(On(getter, f.Types.Int64));
            checks.True(frontend.Entries.Count == recovered && frontend.Entries.All(m => m.TypeArguments[0].Equals(f.Integer) || m.TypeArguments[0].Equals(f.Types.Object)),
                "缓存按实际封闭见证共享，不恢复现场的其他实例");
            checks.True(source.Get(getter) is { Status: AccessorTemplateStatus.Incomplete, Failure.Code: "lowering.Generic.Struct" },
                "封闭模板不改变开放定义的洞");
            var exactFrontend = new ClosedTemplateFrontend(m => Native(m, target, false));
            var exact = new AccessorTemplateSource(Facts([.. entries, new(64, EntryKind.GenericMethod, On(getter, f.Types.Int64), 4, null)]), exactFrontend);
            checks.True(Ask(new(f.Types, exact), f.Types.Int64).Method is not null && exactFrontend.Entries.Single().TypeArguments[0].Equals(f.Types.Int64),
                "现场值实例入口优先于另一基元实例");
            var referenceFrontend = new ClosedTemplateFrontend(m => Native(m, target, false));
            var reference = new AccessorTemplateSource(Facts(entries.Where(e => e.Method!.Method == getter && e.Method.TypeArguments[0].Equals(f.Types.Object))), referenceFrontend);
            checks.True(Ask(new(f.Types, reference), f.Types.Int64).Witness?.Code == "inline.Accessor.Witness.Assumption"
                && referenceFrontend.Entries.Single().TypeArguments[0].Equals(f.Types.Object), "缺少值实例时借用规范引用实例");
            var otherReferenceFrontend = new ClosedTemplateFrontend(m => Native(m, target, false));
            var otherReference = new AccessorTemplateSource(Facts([new(80, EntryKind.GenericMethod, On(getter, f.Types.String), 6, null)]), otherReferenceFrontend);
            checks.True(Ask(new(f.Types, otherReference), f.Types.Int64).Witness?.Code == "inline.Accessor.Witness.Assumption"
                && otherReferenceFrontend.Entries.Single().TypeArguments[0].Equals(f.Types.String), "其他非完全共享引用实例也按自己的封闭身份恢复");
            var orderedFrontend = new ClosedTemplateFrontend(m => Native(m, target, false));
            var nestedValue = new DefinitionRef(f.Owner, [f.Integer]);
            var ordered = new AccessorTemplateSource(Facts([new(8, EntryKind.GenericMethod, On(getter, nestedValue), 7, null),
                new(16, EntryKind.GenericMethod, On(getter, f.Types.Object), 8, null)]), orderedFrontend);
            checks.True(Ask(new(f.Types, ordered), f.Types.Int64).Method is not null
                && orderedFrontend.Entries.Single().TypeArguments[0].Equals(f.Types.Object), "规范引用实例优先于非基元值实例");
            var shared = new TypeDef { Index = 100, Assembly = "Checks.dll", Namespace = "Unity.IL2CPP.Metadata", Name = "__Il2CppFullySharedGenericStructType",
                Attributes = TypeAttributes.Public, Token = 0x02000100, IsValueType = true, IsEnum = false, Size = 16, PackingSize = 0, ClassSizeIsDefault = true };
            var sharedFrontend = new ClosedTemplateFrontend(m => Native(m, target, false));
            var sharedSource = new AccessorTemplateSource(Facts([new(8, EntryKind.GenericMethod, On(getter, new DefinitionRef(shared, [])), 0, null)]), sharedFrontend);
            checks.True(Ask(new(f.Types, sharedSource), f.Integer) is { NoneReason: AccessorNoneReason.Incomplete,
                IncompleteCandidates: [{ Failure.Code: "inline.Accessor.Witness.FullyShared" }] } && sharedFrontend.Entries.Count == 0,
                "只有完全共享入口时保留洞，不尝试恢复");
            var extraSource = new AccessorTemplateSource(Facts(entries), new ClosedTemplateFrontend(m => Native(m, target, false, extraWrite: true)));
            var extraAnswer = Ask(new(f.Types, extraSource), f.Types.Int64);
            checks.True(extraAnswer.NoneReason == AccessorNoneReason.NotTemplate && Reasons(extraAnswer.Failure).Any(r => r.Code == "inline.Accessor.Witness.Assumption"),
                "见证多一次写入不是模板，失败链保留借用的实例");
            var otherField = parameterField ? number : f.Field.Field;
            var different = new AccessorTemplateSource(Facts(entries.Where(e => e.Method!.TypeArguments[0].Equals(f.Integer))),
                new ClosedTemplateFrontend(m => Native(m, otherField, false)));
            checks.True(Ask(new(f.Types, different), f.Integer).NoneReason == AccessorNoneReason.NotTemplate,
                "同宽的另一字段定义不能匹配锚点");
            var closedMethod = On(getter, f.Integer);
            var self = new ArgumentValue(-1, new ByRefRef(closedMethod.DeclaringType), 64);
            var fieldValue = new FieldValue(self, new(target, closedMethod.DeclaringType), f.Integer, 32);
            ManagedBody Body(params ManagedStatement[] statements) => new(closedMethod, [new(0, statements)]);
            var expression = Body(new ManagedReturn(0, new BinaryValue(BinaryOperator.Add, fieldValue, new ConstantValue(1, f.Integer, 32), f.Integer, 32)));
            checks.True(AccessorTemplates.Read(expression).Status == AccessorTemplateStatus.Complete
                && AccessorTemplates.ReadSingleField(expression).Status == AccessorTemplateStatus.NotTemplate,
                "即使现场与见证相同，也不扩大到纯表达式");
            checks.True(AccessorTemplates.ReadSingleField(Body(new ManagedCall(0, new(closedMethod, self, [], false), null),
                new ManagedReturn(1, fieldValue))).Status == AccessorTemplateStatus.NotTemplate, "单字段读取之外多一次调用不是模板");
            var forwardedMethod = f.Method(f.Caller, "Forward", false, true, [f.Integer]);
            var local = new LocalValue(new(0), f.Integer, 32);
            var forwarded = Body(new ManagedCall(0, new(MethodRef.Open(forwardedMethod), null, [fieldValue], false), local), new ManagedReturn(1, local));
            checks.True(AccessorTemplates.Read(forwarded).Status == AccessorTemplateStatus.Complete
                && AccessorTemplates.ReadSingleField(forwarded).Status == AccessorTemplateStatus.NotTemplate, "完整的转调模板仍不进入泛型值类型范围");
            var conditional = Body(new ManagedReturn(0, new ChoiceValue(new ComparisonValue(ComparisonKind.Equal, fieldValue,
                new ConstantValue(0, f.Integer, 32), f.Types.Boolean), new ConstantValue(1, f.Integer, 32), fieldValue, f.Integer, 32)));
            checks.True(AccessorTemplates.ReadSingleField(conditional).Status == AccessorTemplateStatus.NotTemplate, "条件返回不进入泛型值类型范围");
            var another = f.Method(f.Owner, "Another", false, false); another.ReturnType = target.Type;
            var ambiguousSource = new AccessorTemplateSource(Facts([.. entries, new(72, EntryKind.GenericMethod, On(another, f.Integer), 5, null)]),
                new ClosedTemplateFrontend(m => Native(m, target, false)));
            foreach (bool reverse in new[] { false, true })
            {
                f.Owner.Methods = reverse ? [another, getter] : [getter, another];
                var choice = Ask(new(f.Types, ambiguousSource), f.Types.Int64);
                checks.True(choice is { Failure: null, Matches: 2 } && choice.Method?.Method == getter
                    && choice.Method.DeclaringType.Equals(new DefinitionRef(f.Owner, [f.Types.Int64])),
                    "相同封闭见证模板确定选取，保留现场实例且不依赖声明次序");
            }
        }
        static IEnumerable<Reason> Reasons(Reason? reason)
        { for (; reason is not null; reason = reason.Cause) yield return reason; }
    }

    private sealed class ClosedTemplateFrontend(Func<MethodRef, NativeFunction> function) : IMethodStage<CodeEntry, NativeFunction>
    {
        public List<MethodRef> Entries { get; } = [];
        public string Name => "前端";
        public StageResult<NativeFunction> Run(CodeEntry input, MethodContext context)
        { Entries.Add(input.Method!); return new Completed<NativeFunction>(function(input.Method!)); }
    }

    private sealed class GenericTemplateFrontend(Func<MethodDef, NativeFunction> function) : IMethodStage<CodeEntry, NativeFunction>
    {
        public readonly List<MethodRef> Entries = [];
        public string Name => "前端";
        public StageResult<NativeFunction> Run(CodeEntry input, MethodContext context)
        {
            Entries.Add(input.Method!);
            return new Completed<NativeFunction>(function(context.Method));
        }
    }
}
