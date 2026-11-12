using System.Collections.Immutable;
using Cpp2CS.Input;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Recovery.Lowering;

namespace Cpp2CS.Tests;

internal static partial class InliningChecks
{
    private static void GenericAccessorChecks(Assertions checks)
    {
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
            checks.True(ambiguous.Resolve(new(MethodRef.Open(caller), 0, new(f.Field.Field, closed), closed, AccessorKind.Getter, true))
                is { Failure.Code: "inline.Accessor.Ambiguous", Matches: 2 }, "泛型声明类型的两个读模板保持歧义");
            another.GenericParameters = [new() { Name = "M", Position = 0, Attributes = 0 }];
            f.Owner.Methods = [another];
            int requested = 0;
            var excluded = new AccessorQuery(f.Types, new CachedAccessorTemplates(m => { requested++; return Body(m); }));
            checks.True(excluded.Resolve(new(MethodRef.Open(caller), 0, new(f.Field.Field, closed), closed, AccessorKind.Getter, true))
                .NoneReason == AccessorNoneReason.GenericMethod && requested == 0, "泛型方法单列原因且不取模板");
        }
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
