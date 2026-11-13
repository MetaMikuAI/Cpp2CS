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
using Cpp2CS.Tests.Execution;

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    private static void InterlockedChecks(Assertions checks, ProgramModel primitives)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var layouts = new FieldLayouts(spec, 8, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll").Select((t, i) => new TypeDef
        { Index = i, Assembly = t.Assembly, Namespace = t.Namespace, Name = t.Name, Token = t.Token,
            Attributes = t.Attributes, IsValueType = t.IsValueType, IsEnum = t.IsEnum }).ToList();
        TypeRef Primitive(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        TypeDef Define(string name, string ns = "", string assembly = "InterlockedChecks.dll")
        {
            var type = new TypeDef { Index = definitions.Count, Assembly = assembly, Namespace = ns, Name = name,
                Token = (uint)(0x02000001 + definitions.Count), Attributes = TypeAttributes.Public, IsValueType = false,
                IsEnum = false, Size = 40, PackingSize = 0, ClassSizeIsDefault = true };
            definitions.Add(type); return type;
        }
        var owner = Define("Owner"); var ownerType = new DefinitionRef(owner, []);
        var baseDef = Define("Base"); var baseType = new DefinitionRef(baseDef, []);
        var derived = Define("Derived"); var derivedType = new DefinitionRef(derived, []); derived.BaseType = baseType;
        var unrelated = Define("Unrelated"); var unrelatedType = new DefinitionRef(unrelated, []);
        var interlocked = Define("Interlocked", "System.Threading", "mscorlib.dll");
        var parameter = new GenericParameterDef { Name = "T", Position = 0, Attributes = GenericParameterAttributes.ReferenceTypeConstraint };
        var generic = new GenericParameterRef("T", true, 0) { Parameter = parameter };
        int header = (int)spec.Layout.ObjectHeaderSize;
        int nextField = 0;
        FieldDef Field(string name, TypeRef type, int offset, bool statics = false) => new() { Index = nextField++, Owner = owner,
            Name = name, Type = type, Offset = offset, Attributes = FieldAttributes.Public | (statics ? FieldAttributes.Static : 0) };
        var field = Field("Value", baseType, header); var shared = Field("Shared", baseType, 0, true);
        var number = Field("Number", Primitive("Int32"), header + 8); owner.Fields = [field, shared, number];
        var methods = new List<MethodDef>();
        MethodDef Method(TypeDef type, string name, TypeRef result, params TypeRef[] parameters)
        {
            var method = new MethodDef { Index = methods.Count, Owner = type, Name = name, Token = (uint)(0x06000001 + methods.Count),
                Attributes = MethodAttributes.Public | MethodAttributes.Static, ImplAttributes = 0, Slot = -1, ReturnType = result,
                Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray() };
            methods.Add(method); return method;
        }
        var compare = Method(interlocked, "CompareExchange", generic, new ByRefRef(generic), generic, generic); compare.GenericParameters = [parameter];
        var exchange = Method(interlocked, "Exchange", generic, new ByRefRef(generic), generic); exchange.GenericParameters = [parameter];
        interlocked.Methods = [compare, exchange];
        string[] modes = ["Field", "Static", "Array", "ByRef", "Derived", "CastValue", "Integer", "Value", "WrongValue", "WrongComparand", "Missing", "Ambiguous"];
        var callers = modes.ToDictionary(n => n, n => Method(owner, n, baseType,
            n == "Array" ? new ArrayRef(baseType, 1) : n == "ByRef" ? new ByRefRef(baseType) : ownerType,
            n == "Derived" ? derivedType : n == "CastValue" ? Primitive("Object") : n == "WrongValue" ? unrelatedType : baseType,
            n == "WrongComparand" ? unrelatedType : baseType));
        owner.Methods = callers.Values.ToArray();
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = owner.Fields,
            RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key,
                AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var types = new ManagedTypes(program, layouts, 8);
        var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        foreach (bool isCompare in new[] { true, false })
        foreach (string mode in modes)
        {
            var runtime = catalog.Functions.Single(f => f.Operation.Name == (isCompare ? "CompareExchangeReference" : "ExchangeReference"));
            var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new InterlockedRuntimeMap(runtime, catalog.ByName("CastclassClass").Single()), catalog);
            var t = new TermTable(); var block = new BlockIdentity(); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            var builder = new FunctionBuilder(t, block, 64, new(t.Atom(new RootAtom(AddressRoot.Frame), 64))) { ImageBase = image };
            Term Input(int index) { var slot = new AbstractSlot(SlotKind.Integer, index); var value = t.Atom(new EntryAtom(slot), 64); builder.Inputs.Add(new(slot, value)); return value; }
            var root = Input(0); var value = Input(1); var comparand = Input(2); var statements = new List<Statement>();
            Term Add(Term basis, long offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, basis, t.Constant(offset, 64));
            Term Read(Term address) { var id = new ReadIdentity(); var result = t.Atom(new ResultAtom(id), 64); statements.Add(new MemoryRead(id, address, 64, result)); return result; }
            var address = mode switch { "Array" => Add(root, spec.Layout.ArrayDataStart), "ByRef" => root,
                "Integer" => Add(root, number.Offset), "Value" => value, _ => Add(root, field.Offset) };
            var facts = NamingFacts.Empty;
            if (mode == "CastValue")
            {
                var klass = Read(Add(image, 256));
                facts = facts with { Slots = ImmutableDictionary<ulong, Outcome<MetadataEntity>>.Empty.Add(256, Outcome<MetadataEntity>.Success(new ClassEntity(baseType))) };
                var cast = new CallIdentity(); var castResult = t.Atom(new ResultAtom(cast), 64);
                statements.Add(new Call(cast, new ImageFunction(30), [new(new(SlotKind.Integer), value), new(new(SlotKind.Integer, 1), klass)], [new(new(SlotKind.Integer), castResult)]));
                value = castResult;
            }
            if (mode == "Static")
            {
                var klass = Read(Add(image, 256)); address = Read(Add(klass, spec.Layout.Field("Il2CppClass", "static_fields").ByteOffset));
                facts = facts with { Slots = ImmutableDictionary<ulong, Outcome<MetadataEntity>>.Empty.Add(256, Outcome<MetadataEntity>.Success(new ClassEntity(ownerType))) };
            }
            var id = new CallIdentity(); var result = t.Atom(new ResultAtom(id), 64);
            var args = new List<SlotValue> { new(new(SlotKind.Integer), address), new(new(SlotKind.Integer, 1), value) };
            if (isCompare) args.Add(new(new(SlotKind.Integer, 2), comparand));
            statements.Add(new Call(id, new ImageFunction(20), [.. args], [new(new(SlotKind.Integer), result)]));
            builder.Blocks.Add(new(block, [], [.. statements], new Return([new(new(SlotKind.Integer), result)])));
            var saved = interlocked.Methods;
            if (mode == "Missing") interlocked.Methods = [];
            if (mode == "Ambiguous") interlocked.Methods = [compare, exchange, isCompare ? compare : exchange];
            var lowered = new IntegerLowering(builder.Freeze(), MethodRef.Open(callers[mode]), binder, types, calls: calls,
                effects: new ManagedCallEffects(calls), spec: spec, names: facts).Run();
            interlocked.Methods = saved;
            var expected = mode switch { "Integer" or "Value" => "lowering.Interlocked.Location",
                "WrongValue" => "lowering.Interlocked.Type", "WrongComparand" when isCompare => "lowering.Interlocked.Type",
                "Missing" or "Ambiguous" => "lowering.Interlocked.Method", _ => null };
            if (expected is not null) { checks.True(lowered.Failure?.Reason.Code == expected, mode + " 分类缺口：" + lowered.Failure); continue; }
            checks.True(lowered.Body is not null, runtime.Operation.Name + "/" + mode + " 下降：" + lowered.Failure);
            if (lowered.Body is not { } body) continue;
            var call = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Single();
            checks.True(call.Invocation.Method.Method == (isCompare ? compare : exchange) && call.Invocation.Method.MethodArguments.SequenceEqual([baseType]),
                mode + " 方法与 T 取位置声明类型");
            checks.True(call.Invocation.Arguments[0].Type.Equals(new ByRefRef(baseType)), mode + " 第一实参保持 ref T");
            checks.True(emitter.Emit([body]).Count == 0, mode + " 写出并校验泛型调用");
        }
        var terms = new TermTable(); var entry = new BlockIdentity(); var atomic = new FunctionBuilder(terms, entry, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
        atomic.Blocks.Add(new(entry, [], [new ExclusiveClear(new())], new Return([])));
        checks.True(new IntegerLowering(atomic.Freeze(), MethodRef.Open(callers["Field"]), binder, types).Run().Failure?.Reason.Code == "lowering.Atomic",
            "无使用的独占事件也不能下降");
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
        InterlockedExecutionChecks(checks);
    }

    private sealed class InterlockedRuntimeMap(RuntimeFunction operation, RuntimeFunction cast) : IRuntimeFunctionMap
    {
        public RuntimeFunction? Find(CallTarget target) => target is ImageFunction { EntryOffset: 30 } ? cast : operation;
    }

    private static void InterlockedExecutionChecks(Assertions checks)
    {
        using var source = new CompiledSource("""
            using System.Threading;
            public static class AtomicCases {
                public static object Equal(object a, object b) { object p = a; return Interlocked.CompareExchange<object>(ref p, b, a) == a && p == b ? a : b; }
                public static object Different(object a, object b) { object p = a; return Interlocked.CompareExchange<object>(ref p, b, b) == a && p == a ? a : b; }
                public static object Exchange(object a, object b) { object p = a; return Interlocked.Exchange<object>(ref p, b) == a && p == b ? a : b; }
            }
            """);
        var model = new CecilModel(source.Module); var types = new ManagedTypes(model.Program, new ManagedStorage(model.Prepare), 8);
        foreach (string name in new[] { "Equal", "Different", "Exchange" })
        {
            var method = source.Method("AtomicCases", name); var reference = model.Method(method);
            checks.True(method.Body.Instructions.Select(i => i.Operand).OfType<Mono.Cecil.GenericInstanceMethod>()
                .Any(m => m.DeclaringType.FullName == "System.Threading.Interlocked" && m.GenericArguments.Count == 1), name + " 参考 IL 明确调用泛型重载");
            var index = new WorldIndex(model.Program, types); var world = new World(index, 0, new Hints([], []), reference.DeclaringType);
            var interpreter = new CilInterpreter(model, index) { BodyModule = source.Module };
            var execution = interpreter.Run(world, method, reference, [StackValue.O(0), StackValue.O(0x1234)]);
            checks.True(execution.Result == "return 0x0", name + " 比较引用、写入条件与旧值结果：" + execution.Result);
        }
    }
}
