using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Output;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Tests.Execution;
using ManagedValues = Cpp2CS.Managed.ManagedValues;

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    private static void StructByRefConstructorChecks(Assertions checks, ProgramModel primitives)
    {
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").ToList();
        TypeRef Primitive(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        var integer = Primitive("Int32"); var none = Primitive("Void");
        var methods = new List<MethodDef>(); var fields = new List<FieldDef>();
        TypeDef Define(string name, bool value = true)
        {
            var type = new TypeDef { Index = definitions.Count, Assembly = "StructByRef.dll", Namespace = "", Name = name,
                Token = (uint)(0x02000001 + definitions.Count), Attributes = TypeAttributes.Public, IsValueType = value,
                IsEnum = false, Size = value ? 8 : 16, PackingSize = 0, ClassSizeIsDefault = true };
            definitions.Add(type); return type;
        }
        FieldDef Field(TypeDef owner, string name, TypeRef type, int offset, FieldAttributes flags)
        {
            var field = new FieldDef { Index = fields.Count, Owner = owner, Name = name, Type = type, Offset = offset, Attributes = flags };
            fields.Add(field); owner.Fields = [.. owner.Fields, field]; return field;
        }
        MethodDef Method(TypeDef owner, string name, TypeRef result, MethodAttributes flags, params TypeRef[] parameters)
        {
            var method = new MethodDef { Index = methods.Count, Owner = owner, Name = name, Token = (uint)(0x06000001 + methods.Count),
                Attributes = flags, ImplAttributes = 0, Slot = -1, ReturnType = result,
                Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray() };
            methods.Add(method); owner.Methods = [.. owner.Methods, method]; return method;
        }
        var pair = Define("RefPair"); var pairType = new DefinitionRef(pair, []);
        Field(pair, "x", integer, 0, FieldAttributes.Public | FieldAttributes.InitOnly);
        Field(pair, "y", integer, 4, FieldAttributes.Public | FieldAttributes.InitOnly);
        var box = Define("RefBox", false); var boxType = new DefinitionRef(box, []);
        Field(box, "p", pairType, 16, FieldAttributes.Public);
        var caller = Define("RefCases", false);
        var echo = Method(caller, "Echo", pairType, MethodAttributes.Public | MethodAttributes.Static, pairType);
        var bodies = new Dictionary<MethodDef, ManagedBody>();
        var cases = new Dictionary<string, (MethodDef Caller, MethodDef Constructor, DefinitionRef Type)>();
        foreach (var mode in new[] { "Parameter", "Call", "Field", "PartialField", "AfterWrite", "WriteParameter", "Escape", "Fields" })
        {
            var owner = Define("Ref" + mode); var type = new DefinitionRef(owner, []);
            var field = Field(owner, "p", pairType, 0, FieldAttributes.Private | FieldAttributes.InitOnly);
            var ctor = Method(owner, ".ctor", none, MethodAttributes.Public, new ByRefRef(pairType));
            var pointer = new ArgumentValue(0, new ByRefRef(pairType), 64);
            var self = new ArgumentValue(-1, new ByRefRef(type), 64);
            var target = new FieldValue(self, new(field, type), pairType, 0);
            var local = new LocalValue(new(0), pairType, 0);
            var statements = new List<ManagedStatement>();
            if (mode == "AfterWrite") statements.Add(new ManagedStore(0, target, new ComposedValue(pairType, [])));
            if (mode == "WriteParameter") statements.Add(new ManagedStore(0, new IndirectValue(pointer, pairType), new ComposedValue(pairType, [])));
            if (mode == "Escape") statements.Add(new ManagedCall(0, new(MethodRef.Open(ctor), self, [pointer], false), null));
            if (mode == "Fields")
            {
                var values = pair.Fields.Select((f, i) => new LocalValue(new(i), integer, 32)).ToArray();
                for (int i = 0; i < 2; i++) statements.Add(new ManagedAssignment(0, values[i], new FieldValue(pointer, new(pair.Fields[i], pairType), integer, 32)));
                for (int i = 0; i < 2; i++) statements.Add(new ManagedStore(0, new FieldValue(target, new(pair.Fields[i], pairType), integer, 32), values[i]));
            }
            else
            {
                statements.Add(new ManagedAssignment(0, local, new IndirectValue(pointer, pairType)));
                statements.Add(new ManagedStore(0, target, local));
            }
            statements.Add(new ManagedReturn(0, null));
            bodies.Add(ctor, new(MethodRef.Open(ctor), [new(0, statements)]));
            var test = Method(caller, mode, type, MethodAttributes.Public | MethodAttributes.Static, mode is "Field" or "PartialField" ? boxType : pairType);
            cases.Add(mode, (test, ctor, type));
        }
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = fields,
            RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [], Assemblies = definitions.GroupBy(t => t.Assembly)
                .Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var layouts = new Cpp2CS.Runtime.Layouts.FieldLayouts(spec, 8, 8);
        var types = new ManagedTypes(program, layouts, 8); var binder = new MethodBinder(new(layouts), new Aapcs64());
        var templates = new StructConstructorTemplates(types, new StructBodies(bodies));
        var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        const string source = """
            public readonly struct RefPair { public readonly int x,y; public RefPair(int a,int b){x=a;y=b;} }
            public readonly struct RefParameter { private readonly RefPair p; public RefParameter(in RefPair x){p=x;} }
            public readonly struct RefCall { private readonly RefPair p; public RefCall(in RefPair x){p=x;} }
            public class RefBox { public RefPair p; }
            public readonly struct RefField { private readonly RefPair p; public RefField(in RefPair x){p=x;} }
            public readonly struct RefFields { private readonly RefPair p; public RefFields(in RefPair x){p=x;} }
            public static class RefCases {
                public static RefPair Echo(RefPair p)=>p;
                public static RefParameter Parameter(RefPair p)=>new RefParameter(in p);
                public static RefCall Call(RefPair p){var x=Echo(p);return new RefCall(in x);}
                public static RefField Field(RefBox b)=>new RefField(in b.p);
                public static RefFields Fields(RefPair p)=>new RefFields(in p);
            }
            """;
        using var reference = new CompiledSource(source); using var tested = new CompiledSource(source);
        foreach (var (mode, item) in cases)
        {
            var terms = new TermTable(); var entry = new BlockIdentity(); var frame = terms.Atom(new RootAtom(AddressRoot.Frame), 64);
            var function = new FunctionBuilder(terms, entry, 64, new(frame));
            var slot = new AbstractSlot(SlotKind.Integer); var input = terms.Atom(new EntryAtom(slot), 64); function.Inputs.Add(new(slot, input));
            var statements = new List<Statement>(); Term result = input;
            if (mode == "Call")
            {
                var identity = new CallIdentity(); result = terms.Atom(new ResultAtom(identity), 64);
                statements.Add(new Call(identity, new ImageFunction(10), [new(slot, input), new(new(SlotKind.Integer, 1), terms.Constant(0, 64))], [new(slot, result)]));
            }
            if (mode is "Field" or "PartialField")
            {
                var identity = new ReadIdentity(); result = terms.Atom(new ResultAtom(identity), 64);
                var fieldAddress = terms.Apply(new CoreOperator(CoreOperation.Add), 64, input, terms.Constant(16, 64));
                statements.Add(new MemoryRead(identity, fieldAddress, 64, result));
                if (mode == "PartialField") result = terms.Concat(terms.Slice(result, 0, 32), terms.Constant(42, 32));
            }
            function.Blocks.Add(new(entry, [], [.. statements], new Return([new(slot, result)])));
            var calls = new CallNamingQuery(binder, new AddressMap(echo, echo, echo), new NamingChecks.RuntimeMap(), RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel));
            var lowered = new IntegerLowering(function.Freeze(), MethodRef.Open(item.Caller), binder, types,
                calls: calls, effects: new NoStructWrites(), spec: spec, structConstructors: templates).Run();
            if (mode is "AfterWrite" or "WriteParameter" or "Escape" or "PartialField")
            {
                var expected = mode == "AfterWrite" ? "inline.StructConstructor.ReadAfterWrite" : mode == "PartialField" ? "inline.StructConstructor.NoMatch" : "inline.StructConstructor.Events";
                checks.True(lowered.Body is null && lowered.Failure?.Reason.Code == expected, mode + " 保留洞：" + lowered.Failure);
                continue;
            }
            checks.True(lowered.Body is not null, mode + " 按引用构造下降：" + lowered.Failure);
            if (lowered.Body is not { } body) continue;
            var returned = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedReturn>().Single().Value;
            bool snapshotAddress = mode is "Call" or "Field";
            checks.True(returned is NewObjectValue { Arguments: [AddressValue address] } && (snapshotAddress ? address.Target is LocalValue : address.Target is ArgumentValue), mode + " 对整体来源取地址");
            checks.True(emitter.Emit([body]).Count == 0, mode + " 按引用构造 CIL 校验");
            var emitted = skeleton.Method(item.Caller);
            checks.True(emitted.Body.Instructions.Any(i => snapshotAddress
                ? i.OpCode.Code is Mono.Cecil.Cil.Code.Ldloca or Mono.Cecil.Cil.Code.Ldloca_S
                : i.OpCode.Code is Mono.Cecil.Cil.Code.Ldarga or Mono.Cecil.Cil.Code.Ldarga_S), mode + " 输出地址指令");
            if (mode == "Call") checks.True(returned is NewObjectValue { Arguments: [AddressValue { Target: LocalValue saved }] }
                && body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Single().Result?.Id == saved.Id,
                "调用结果只求值一次并保存在所取址的临时局部");
            var output = tested.Method("RefCases", mode); output.Body = emitted.Body; RebindStructBody(tested.Module, output);
            var comparison = CilComparison.Compare(reference.Method("RefCases", mode), output);
            checks.True(comparison.Status == CilComparisonStatus.Match, mode + " 按引用构造执行对照：" + comparison);
            if (mode == "Parameter")
            {
                var snapshot = function.Freeze(); var state = new StateQueries(); var point = new Point(entry, 0);
                var origin = new StructOrigin(pairType, new TermSource(input), point, Parameter: 0);
                var query = new StructConstructorQuery(types, templates, state, [origin, origin with { Parameter = 1 }]);
                var leaves = types.Projections(item.Type).Select(p => new StructLeaf(p, terms.Slice(input, p.Bit, p.Width))).ToImmutableArray();
                var answer = state.CreateContext(snapshot).Get(query, new(MethodRef.Open(item.Caller), item.Type, leaves, point));
                checks.True(answer.IsSuccess && answer.Value.Failure?.Code == "inline.StructConstructor.Ambiguous", "两个同值整体来源保留歧义洞");
            }
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
}
