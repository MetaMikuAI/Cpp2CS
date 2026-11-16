using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Input;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Output;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Tests.Execution;
using ManagedValues = Cpp2CS.Managed.ManagedValues;

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    private sealed class ConstructorFrontend(Func<MethodRef, NativeFunction> native) : IMethodStage<CodeEntry, NativeFunction>
    {
        public string Name => "前端";
        public List<MethodRef> Entries { get; } = [];
        public StageResult<NativeFunction> Run(CodeEntry input, MethodContext context)
        { Entries.Add(input.Method!); return new Completed<NativeFunction>(native(input.Method!)); }
    }
    private static void GenericStructConstructorChecks(Assertions checks, ProgramModel primitives)
    {
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").ToList();
        TypeRef Primitive(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        var integer = Primitive("Int32"); var wide = Primitive("Int64"); var none = Primitive("Void");
        var fields = new List<FieldDef>(); var methods = new List<MethodDef>();
        TypeDef Define(string name, bool value = true)
        {
            var type = new TypeDef { Index = definitions.Count, Assembly = "GenericStructs.dll", Namespace = "", Name = name,
                Token = (uint)(0x02000001 + definitions.Count), Attributes = TypeAttributes.Public, IsValueType = value,
                IsEnum = false, Size = value ? 0 : 16, PackingSize = 0, ClassSizeIsDefault = true };
            if (value) type.GenericParameters = [new() { Name = "T", Position = 0, Attributes = 0 }];
            definitions.Add(type); return type;
        }
        TypeRef Parameter(TypeDef type) => new GenericParameterRef("T", false, 0) { Parameter = type.GenericParameters[0] };
        void Field(TypeDef owner, string name, TypeRef type, int offset, bool visible = false)
        {
            var field = new FieldDef { Index = fields.Count, Owner = owner, Name = name, Type = type, Offset = offset,
                Attributes = (visible ? FieldAttributes.Public : FieldAttributes.Private) | FieldAttributes.InitOnly };
            fields.Add(field); owner.Fields = [.. owner.Fields, field];
        }
        MethodDef Method(TypeDef owner, string name, TypeRef result, params TypeRef[] parameters)
        {
            var method = new MethodDef { Index = methods.Count, Owner = owner, Name = name, Token = (uint)(0x06000001 + methods.Count),
                Attributes = MethodAttributes.Public | (name == ".ctor" ? 0 : MethodAttributes.Static), ImplAttributes = 0, Slot = -1,
                ReturnType = result, Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray() };
            methods.Add(method); owner.Methods = [.. owner.Methods, method]; return method;
        }
        var g = Define("CtorG`1"); Field(g, "a", Parameter(g), 0); Field(g, "b", integer, 8);
        var ctor = Method(g, ".ctor", none, Parameter(g), integer);
        var p = Define("CtorP`1"); Field(p, "a", Parameter(p), 0, true); Field(p, "b", integer, 8, true);
        var pairCtor = Method(p, ".ctor", none, Parameter(p), integer);
        var h = Define("CtorH`1"); var openPair = new DefinitionRef(p, [Parameter(h)]); Field(h, "p", openPair, 0);
        var refCtor = Method(h, ".ctor", none, new ByRefRef(openPair));
        var n = Define("CtorN`1"); Field(n, "g", new DefinitionRef(g, [Parameter(n)]), 0);
        var nestedCtor = Method(n, ".ctor", none, Parameter(n), integer);
        var caller = Define("GenericCtorCases", false);
        var pair = new DefinitionRef(p, [integer]);
        var cases = new Dictionary<string, (MethodDef Caller, MethodDef Constructor, TypeRef Argument)>();
        foreach (var (name, constructor, argument) in new (string, MethodDef, TypeRef)[] {
            ("Exact", ctor, wide), ("Borrowed", ctor, wide), ("Expand", ctor, pair), ("Collapse", ctor, wide),
            ("ByRef", refCtor, integer), ("ByRefBorrowed", refCtor, wide), ("Nested", nestedCtor, wide),
            ("Shared", ctor, wide), ("Conversion", ctor, integer), ("Default", ctor, wide), ("Permuted", ctor, wide), ("Constant", ctor, wide) })
        {
            var result = new DefinitionRef(constructor.Owner, [argument]);
            var parameters = constructor == refCtor ? new TypeRef[] { new DefinitionRef(p, [argument]) } : [argument, integer];
            cases.Add(name, (Method(caller, name, result, parameters), constructor, argument));
        }
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = fields,
            RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [], Assemblies = definitions.GroupBy(t => t.Assembly)
                .Select(v => new AssemblyDef { Name = v.Key, AssemblyName = Path.GetFileNameWithoutExtension(v.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = v.ToArray() }).ToArray() };
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var layouts = new Cpp2CS.Runtime.Layouts.FieldLayouts(spec, 8, 8); var types = new ManagedTypes(program, layouts, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        MethodRef On(MethodDef m, TypeRef t) => new(m, [t], []);
        NativeFunction Native(MethodRef method, string mode)
        {
            var terms = new TermTable(); var block = new BlockIdentity();
            var builder = new FunctionBuilder(terms, block, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
            Term Input(int index)
            { var slot = new AbstractSlot(SlotKind.Integer, index); var value = terms.Atom(new EntryAtom(slot), 64); builder.Inputs.Add(new(slot, value)); return value; }
            var self = Input(0); var x = Input(1); var statements = new List<Statement>();
            Term Address(int offset) => terms.Apply(new CoreOperator(CoreOperation.Add), 64, self, terms.Constant(offset, 64));
            var instance = (DefinitionRef)method.DeclaringType;
            if (method.Method == refCtor)
            {
                var field = types.Fields(instance).Single(); var read = new ReadIdentity(); var value = terms.Atom(new ResultAtom(read), field.Width);
                statements.Add(new MemoryRead(read, x, field.Width, value));
                statements.Add(new MemoryWrite(new(), Address(field.Bit / 8), field.Width, value));
            }
            else
            {
                var y = Input(2); var projections = types.Fields(instance).ToArray();
                if (method.Method == nestedCtor)
                {
                    var value = terms.Concat(terms.Slice(x, 0, 32), terms.Slice(y, 0, 32));
                    statements.Add(new MemoryWrite(new(), Address(projections[0].Bit / 8), 64, value));
                }
                else
                {
                    var a = projections[0]; var b = projections[1];
                    statements.Add(new MemoryWrite(new(), Address(a.Bit / 8), a.Width,
                        mode == "Default" ? terms.Constant(0, a.Width) : mode == "Permuted" && method.Method == ctor
                            ? terms.Concat(terms.Slice(x, 32, 32), terms.Slice(x, 0, 32)) : terms.Slice(x, 0, a.Width)));
                    statements.Add(new MemoryWrite(new(), Address(b.Bit / 8), b.Width, mode == "Constant" ? terms.Constant(1, b.Width) : terms.Slice(mode == "Conversion" ? x : y, 0, b.Width)));
                }
            }
            builder.Blocks.Add(new(block, [], [.. statements], new Return([]))); return builder.Freeze();
        }
        GlobalFacts Facts(IEnumerable<MethodRef> selected)
        {
            var entries = selected.Select((m, i) => new CodeEntry((ulong)(16 + i * 8), EntryKind.GenericMethod, m, i, null)).ToArray();
            var map = new Registrations { CodeRegistration = 0, MetadataRegistration = 0, Entries = entries,
                ByAddress = entries.GroupBy(e => e.Address).ToDictionary(v => v.Key, v => v.ToImmutableArray()),
                Rgctx = new Dictionary<(string, uint), ImmutableArray<RgctxEntry>>(), MetadataUsageSlots = [], TypePointers = new Dictionary<ulong, int>(),
                InvokerOf = new Dictionary<MethodDef, int>(), UsageEntities = new Dictionary<ulong, Usage>() };
            return new(new InputMemoryImage(), program, map, spec, "arm64");
        }
        var shared = new TypeDef { Index = 100, Assembly = "GenericStructs.dll", Namespace = "Unity.IL2CPP.Metadata", Name = "__Il2CppFullySharedGenericStructType",
            Attributes = TypeAttributes.Public, Token = 0x02000100, IsValueType = true, IsEnum = false, Size = 16, PackingSize = 0, ClassSizeIsDefault = true };
        var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        const string source = """
            public readonly struct CtorG<T>{private readonly T a;private readonly int b;public CtorG(T x,int y){a=x;b=y;}}
            public readonly struct CtorP<T>{public readonly T a;public readonly int b;public CtorP(T x,int y){a=x;b=y;}}
            public readonly struct CtorH<T>{private readonly CtorP<T> p;public CtorH(in CtorP<T> x){p=x;}}
            public readonly struct CtorN<T>{private readonly CtorG<T> g;public CtorN(T x,int y){g=new CtorG<T>(x,y);}}
            public static class GenericCtorCases{
                public static CtorG<long> Exact(long x,int y)=>new CtorG<long>(x,y);
                public static CtorG<long> Borrowed(long x,int y)=>new CtorG<long>(x,y);
                public static CtorG<CtorP<int>> Expand(CtorP<int> x,int y)=>new CtorG<CtorP<int>>(x,y);
                public static CtorG<long> Collapse(long x,int y)=>new CtorG<long>(x,y);
                public static CtorH<int> ByRef(CtorP<int> x)=>new CtorH<int>(in x);
                public static CtorH<long> ByRefBorrowed(CtorP<long> x)=>new CtorH<long>(in x);
                public static CtorN<long> Nested(long x,int y)=>new CtorN<long>(x,y);
            }
            """;
        using var reference = new CompiledSource(source); using var tested = new CompiledSource(source);
        foreach (var (name, item) in cases)
        {
            var witnesses = name switch {
                "Exact" => new[] { On(ctor, integer), On(ctor, wide) },
                "Shared" => [On(ctor, new DefinitionRef(shared, []))],
                "Conversion" => [On(ctor, wide)], "Collapse" => [On(ctor, pair)],
                "Nested" => [On(nestedCtor, integer), On(ctor, integer)],
                "Permuted" => [On(ctor, pair), On(pairCtor, integer)],
                _ => [On(item.Constructor, integer)],
            };
            var frontend = new ConstructorFrontend(m => Native(m, name));
            var sourceBodies = new MethodTemplateSource(Facts(witnesses), frontend, constructors: true);
            var templates = new StructConstructorTemplates(types, sourceBodies);
            var selected = On(item.Constructor, item.Argument); var template = templates.Get(selected);
            if (name is "Shared" or "Conversion" or "Default" or "Permuted" or "Constant")
            {
                checks.True(template.Template is null, name + " 不采纳模板");
                checks.True(name == "Shared" ? Chain(template.Failure).Any(r => r.Code == "inline.StructConstructor.Witness.FullyShared") && frontend.Entries.Count == 0
                    : template.Failure?.Code == "inline.StructConstructor.Representation", name + " 拒绝原因：" + template.Failure);
                continue;
            }
            checks.True(template.Template is not null, name + " 封闭构造写入表：" + template.Failure);
            if (template.Template is null) continue;
            bool borrowed = name is not ("Exact" or "ByRef");
            checks.True(template.Witness?.Code == "inline.StructConstructor.Witness" + (borrowed ? ".Assumption" : ""), name + " 见证注明实例与借用假设");
            checks.True(frontend.Entries.Any(m => m == (name == "Exact" ? selected : witnesses[0])) && (name != "Exact" || frontend.Entries.Single() == selected), name + " 按现场入口优先选择");
            int count = frontend.Entries.Count; templates.Get(On(item.Constructor, item.Argument));
            checks.True(frontend.Entries.Count == count, name + " 按封闭实例缓存");
            var terms = new TermTable(); var block = new BlockIdentity();
            var builder = new FunctionBuilder(terms, block, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var slots = new List<Term>();
            var inputType = item.Caller.Parameters[0].Type; int inputBits = types.StorageBits(inputType);
            for (int i = 0; i < (inputBits + 63) / 64; i++)
            { var slot = new AbstractSlot(SlotKind.Integer, i); var input = terms.Atom(new EntryAtom(slot), 64); builder.Inputs.Add(new(slot, input)); slots.Add(input); }
            Term packed;
            if (item.Constructor == refCtor) packed = terms.Concat(slots.ToArray());
            else
            {
                var slot = new AbstractSlot(SlotKind.Integer, slots.Count); var y = terms.Atom(new EntryAtom(slot), 64); builder.Inputs.Add(new(slot, y));
                int bits = types.StorageBits(selected.DeclaringType);
                var value = terms.Concat(terms.Slice(slots[0], 0, inputBits), terms.Slice(y, 0, 32));
                packed = value.Width < bits ? terms.Concat(value, terms.Constant(0, bits - value.Width)) : value;
            }
            builder.Blocks.Add(new(block, [], [], new Return(Enumerable.Range(0, (packed.Width + 63) / 64)
                .Select(i => new SlotValue(new(SlotKind.Integer, i), terms.Slice(packed, i * 64, Math.Min(64, packed.Width - i * 64)))).ToImmutableArray())));
            var lowered = new IntegerLowering(builder.Freeze(), MethodRef.Open(item.Caller), binder, types, structConstructors: templates).Run();
            checks.True(lowered.Body is not null, name + " 现场闭包 newobj：" + lowered.Failure);
            if (lowered.Body is not { } body) continue;
            var result = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedReturn>().Single().Value;
            checks.True(result is NewObjectValue created && created.Constructor == selected, name + " newobj 保留现场构造函数实例");
            var problems = emitter.Emit([body]); checks.True(problems.Count == 0, name + " 泛型构造 CIL 校验：" + string.Join("；", problems.Values));
            if (problems.Count != 0) continue;
            var output = tested.Method("GenericCtorCases", name); output.Body = skeleton.Method(item.Caller).Body;
            RebindGenericStructBody(tested.Module, output);
            var comparison = CilComparison.Compare(reference.Method("GenericCtorCases", name), output);
            checks.True(comparison.Status == CilComparisonStatus.Match, name + " 泛型构造执行对照：" + comparison);
            if (name == "Borrowed")
            {
                var small = templates.Get(On(ctor, integer));
                checks.True(small.Template!.Leaves[1].Projection.Bit != template.Template.Leaves[1].Projection.Bit, "泛型字段偏移随实例重投影");
                checks.True(sourceBodies.GetBody(ctor) is null && sourceBodies.GetFailure(ctor)?.Code == "lowering.Generic.Witness", "封闭模板不改变开放定义的原有洞");
            }
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
        static IEnumerable<Reason> Chain(Reason? reason) { for (; reason is not null; reason = reason.Cause) yield return reason; }
    }
    private static void RebindGenericStructBody(Mono.Cecil.ModuleDefinition module, Mono.Cecil.MethodDefinition method)
    {
        Mono.Cecil.TypeReference Map(Mono.Cecil.TypeReference type)
        {
            if (type is Mono.Cecil.ByReferenceType byref) return new Mono.Cecil.ByReferenceType(Map(byref.ElementType));
            if (type is Mono.Cecil.GenericInstanceType generic)
            {
                var mapped = new Mono.Cecil.GenericInstanceType(Map(generic.ElementType));
                foreach (var argument in generic.GenericArguments) mapped.GenericArguments.Add(Map(argument));
                return mapped;
            }
            return module.GetType(type.FullName) ?? module.ImportReference(module.TypeSystem.Object.Resolve().Module.GetType(type.FullName));
        }
        foreach (var local in method.Body.Variables) local.VariableType = Map(local.VariableType);
        foreach (var instruction in method.Body.Instructions)
        {
            if (instruction.Operand is Mono.Cecil.MethodReference called)
            {
                var owner = module.GetType(called.DeclaringType.GetElementType().FullName);
                var definition = owner.Methods.Single(m => m.Name == called.Name && m.Parameters.Count == called.Parameters.Count);
                var mapped = new Mono.Cecil.MethodReference(definition.Name, definition.ReturnType, Map(called.DeclaringType))
                { HasThis = definition.HasThis, ExplicitThis = definition.ExplicitThis, CallingConvention = definition.CallingConvention };
                foreach (var parameter in definition.Parameters) mapped.Parameters.Add(new(parameter.ParameterType));
                instruction.Operand = mapped;
            }
            else if (instruction.Operand is Mono.Cecil.TypeReference type) instruction.Operand = Map(type);
            else if (instruction.Operand is Mono.Cecil.ParameterDefinition parameter) instruction.Operand = method.Parameters[parameter.Index];
        }
    }
}
