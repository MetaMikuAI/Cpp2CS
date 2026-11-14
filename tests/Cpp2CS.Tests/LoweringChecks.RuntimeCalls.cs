using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Output;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    private static void RuntimeCallChecks(Assertions checks, ProgramModel primitives)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").ToList();
        TypeRef Type(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        TypeDef AddType(string name, string assembly = "mscorlib.dll")
        {
            var type = new TypeDef { Index = definitions.Count, Assembly = assembly, Namespace = "System", Name = name,
                Token = (uint)(0x02000001 + definitions.Count), Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
            definitions.Add(type); return type;
        }
        var reflection = AddType("Type"); var owner = AddType("RuntimeCalls", "RuntimeChecks.dll");
        var methods = new List<MethodDef>();
        MethodDef AddMethod(TypeDef type, string name, TypeRef result, params TypeRef[] parameters)
        {
            var method = new MethodDef { Index = methods.Count, Owner = type, Name = name, Token = (uint)(0x06000001 + methods.Count),
                Attributes = MethodAttributes.Public | (name == ".ctor" ? 0 : MethodAttributes.Static), ImplAttributes = 0, Slot = -1,
                ReturnType = result, Parameters = parameters.Select((p, i) => new ParameterDef("p" + i, p, 0, null, false)).ToArray() };
            methods.Add(method); type.Methods = type.Methods.Append(method).ToArray(); return method;
        }
        var profile = AddMethod(owner, "Profile", Type("Void"));
        var uncheckedBox = AddMethod(owner, "Boxed", Type("Int32"), Type("Int32"));
        var thread = AddMethod(owner, "ThreadData", Type("IntPtr"));
        var lookups = Enumerable.Range(1, 3).Select(n => AddMethod(reflection, "GetType", Type("Type"),
            Enumerable.Range(0, n).Select(i => Type(i == 0 ? "String" : "Boolean")).ToArray())).ToArray();
        var callers = lookups.Select((m, i) => AddMethod(owner, "Lookup" + i, Type("Type"), m.Parameters.Select(p => p.Type).ToArray())).ToArray();
        var math = AddType("Math");
        var sin = AddMethod(math, "Sin", Type("Double"), Type("Double"));
        var atan2 = AddMethod(math, "Atan2", Type("Double"), Type("Double"), Type("Double"));
        var abs = AddMethod(math, "Abs", Type("Single"), Type("Single"));
        var mathCallers = new[] { sin, atan2, abs }.Select(m => AddMethod(owner, "Call" + m.Name, m.ReturnType, m.Parameters.Select(p => p.Type).ToArray())).ToArray();
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = [], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key),
                Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var layouts = new FieldLayouts(spec, 8, 8); var types = new ManagedTypes(program, layouts, 8); var binder = new MethodBinder(new(layouts), new Aapcs64());
        var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(catalog.Functions[0]), catalog);
        var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        foreach (var test in new[] { "Profile", "Thread", "Unchecked", "UnknownBox", "Lookup1", "Lookup2", "Lookup3", "WrongCaller", "WrongTarget" })
        {
            var t = new TermTable(); var block = new BlockIdentity(); var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            var builder = new FunctionBuilder(t, block, 64, new(frame)) { ImageBase = image }; var statements = new List<Statement>();
            var slots = ImmutableDictionary<ulong, Outcome<MetadataEntity>>.Empty;
            Term Input(int i) { var slot = new AbstractSlot(SlotKind.Integer, i); var value = t.Atom(new EntryAtom(slot), 64); builder.Inputs.Add(new(slot, value)); return value; }
            Term Entity(ulong offset, MetadataEntity entity)
            {
                slots = slots.Add(offset, Outcome<MetadataEntity>.Success(entity)); var id = new ReadIdentity(); var value = t.Atom(new ResultAtom(id), 64);
                statements.Add(new MemoryRead(id, t.Apply(new CoreOperator(CoreOperation.Add), 64, image, t.Constant(offset, 64)), 64, value)); return value;
            }
            Term Invoke(string operation, params Term[] arguments)
            {
                var function = catalog.Functions.Single(f => f.Operation.Name == operation && (operation != "Box" || f.Name == "Box"));
                var id = new CallIdentity(); var result = t.Atom(new ResultAtom(id), 64);
                statements.Add(new Call(id, new NamedFunction(function.MangledName), arguments.Select((v, i) => new SlotValue(new(SlotKind.Integer, i), v)).ToImmutableArray(),
                    function.Operation.Result.Kind == RuntimeValueKind.Void ? [] : [new(new(SlotKind.Integer), result)]) { Trace = new(48) }); return result;
            }
            MethodDef caller; Term? returned = null;
            if (test == "Profile") { caller = profile; Invoke("ThrowProfile", Entity(128, new MethodEntity(MethodRef.Open(profile)))); }
            else if (test == "Thread") { caller = thread; returned = Invoke("GetThreadStaticData", Entity(128, new ClassEntity(Type("Int32")))); }
            else if (test is "Unchecked" or "UnknownBox")
            {
                caller = uncheckedBox; var value = Input(0); Term obj = value;
                if (test == "Unchecked")
                {
                    var klass = Entity(128, new ClassEntity(Type("Int32"))); statements.Add(new MemoryWrite(new(), frame, 32, t.Slice(value, 0, 32)));
                    obj = Invoke("Box", klass, frame);
                }
                var address = Invoke("UnboxUnchecked", obj); var read = new ReadIdentity(); returned = t.Atom(new ResultAtom(read), 32); statements.Add(new MemoryRead(read, address, 32, returned));
            }
            else
            {
                int n = test.StartsWith("Lookup", StringComparison.Ordinal) ? int.Parse(test[^1..]) : 1; caller = callers[n - 1];
                var arguments = Enumerable.Range(0, n).Select(Input).ToList();
                arguments.Add(Entity(128, new MethodEntity(MethodRef.Open(test == "WrongTarget" ? profile : lookups[n - 1]))));
                arguments.Add(Entity(256, new MethodEntity(MethodRef.Open(test == "WrongCaller" ? lookups[0] : caller))));
                returned = Invoke("GetTypeByName" + n, [.. arguments]);
            }
            builder.Blocks.Add(new(block, [], [.. statements], new Return(returned is null ? [] : [new(new(SlotKind.Integer), returned.Width == 32 ? t.Concat(returned, t.Constant(0, 32)) : returned)])));
            var result = new IntegerLowering(builder.Freeze(), MethodRef.Open(caller), binder, types, calls: calls, effects: new ManagedCallEffects(calls), spec: spec,
                names: NamingFacts.Empty with { Slots = slots }).Run();
            string? error = test switch { "Profile" => "lowering.Profile.Unavailable", "Thread" => "lowering.ThreadStatic.Location", "UnknownBox" => "lowering.UnboxUnchecked.Type",
                "WrongCaller" => "lowering.GetType.Caller", "WrongTarget" => "lowering.GetType.Method", _ => null };
            if (error is not null) { checks.True(result.Failure?.Reason.Code == error, test + " 明确拒绝：" + result.Failure); continue; }
            checks.True(result.Body is not null, test + " 下降：" + result.Failure);
            if (result.Body is not { } body) continue;
            if (test.StartsWith("Lookup", StringComparison.Ordinal)) checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Single().Invocation.Method.Method == lookups[int.Parse(test[^1..]) - 1], "GetType 方法身份与重载一致");
            checks.True(emitter.Emit([body]).Count == 0, test + " CIL 写出校验");
        }
        foreach (var (symbol, target, caller) in new[] { ("sin", sin, mathCallers[0]), ("atan2", atan2, mathCallers[1]), ("fabsf", abs, mathCallers[2]) })
        {
            var t = new TermTable(); var block = new BlockIdentity(); var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64);
            var builder = new FunctionBuilder(t, block, 64, new(frame)); var arguments = new List<SlotValue>();
            for (int i = 0; i < target.Parameters.Count; i++)
            {
                var slot = new AbstractSlot(SlotKind.Floating, i); var value = t.Atom(new EntryAtom(slot), 64);
                arguments.Add(new(slot, value)); builder.Inputs.Add(new(slot, value));
            }
            var id = new CallIdentity(); var returned = t.Atom(new ResultAtom(id), 64);
            builder.Blocks.Add(new(block, [], [new Call(id, new ImportedTarget(new(symbol)), [.. arguments], [new(new(SlotKind.Floating), returned)])],
                new Return([new(new(SlotKind.Floating), returned)])));
            var lowered = new IntegerLowering(builder.Freeze(), MethodRef.Open(caller), binder, types, calls: calls, effects: new ManagedCallEffects(calls), spec: spec).Run();
            checks.True(lowered.Body is not null, symbol + " 浮点 ABI 下降：" + lowered.Failure);
            if (lowered.Body is { } body)
            {
                var call = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Single();
                checks.True(call.Invocation.Method.Method == target && call.Invocation.Arguments.All(a => a is ArgumentValue), symbol + " 精确方法与浮点参数槽");
                checks.True(emitter.Emit([body]).Count == 0, symbol + " 浮点调用写出校验");
            }
            var saved = math.Methods; math.Methods = saved.Where(m => m != target).ToArray();
            checks.True(new IntegerLowering(builder.Freeze(), MethodRef.Open(caller), binder, types, calls: calls, effects: new ManagedCallEffects(calls), spec: spec).Run()
                .Failure?.Reason.Code == "lowering.Math.Method", "核心库被裁剪时数学导入保持洞");
            math.Methods = saved;
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
}
