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
using Cpp2CS.Recovery.Structure;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Kernel.State;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Tests.Execution;

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    private static void RuntimeEventExecutionChecks(Assertions checks, ProgramModel primitives)
    {
        using var source = new CompiledSource("""
            public class EventValue { public int Value; public int Read() => Value; public virtual U Apply<U>(U value) => value; }
            public static class EventCases {
                public static int NullRead(EventValue value) => value.Value;
                public static int NullReadOut(EventValue value) => 0;
                public static int NullExplicit(EventValue value) { if(value == null) throw new System.NullReferenceException(); return 7; }
                public static int NullExplicitOut(EventValue value) => 0;
                public static int NullCall(EventValue value) => value.Read();
                public static int NullCallOut(EventValue value) => 0;
                public static int NullOther(EventValue value, EventValue other) { if(value == null) throw new System.NullReferenceException(); return other.Value; }
                public static int NullOtherOut(EventValue value, EventValue other) => 0;
                public static int IsBoxResult(object value) => value is int ? (int)value : 9;
                public static int IsBoxResultOut(object value) => 0;
                public static int IsBoxOriginal(object value) => value is int ? (int)value : 9;
                public static int IsBoxOriginalOut(object value) => 0;
                public static int UnknownBox(object value) => 0;
                public static int UnusedTypeCheck(object value) => 0;
                public static int UnboxThrow(object value) => (int)value;
                public static int UnboxThrowOut(object value) => 0;
                public static int NoNullFusion(object value) { if(value is int) return (int)value; throw new System.InvalidCastException(); }
                public static int NoNullFusionOut(object value) => 0;
                public static int GenericVirtual(EventValue value, int argument) => value.Apply<int>(argument);
                public static int GenericVirtualOut(EventValue value, int argument) => 0;
            }
            """);
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").ToList();
        var objectIndex = definitions.FindIndex(t => t.Name == "Object"); var originalObject = definitions[objectIndex];
        definitions[objectIndex] = new TypeDef { Index = originalObject.Index, Assembly = originalObject.Assembly, Namespace = originalObject.Namespace,
            Name = originalObject.Name, Token = originalObject.Token, Attributes = originalObject.Attributes, IsValueType = false, IsEnum = false,
            Size = 16, PackingSize = 0, ClassSizeIsDefault = true };
        TypeRef Type(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        TypeDef Define(string name, string assembly = "EventChecks.dll", string ns = "", TypeRef? parent = null)
        {
            var d = new TypeDef { Index = definitions.Count, Assembly = assembly, Namespace = ns, Name = name, Token = (uint)(0x02000001 + definitions.Count),
                Attributes = TypeAttributes.Public | (name is "Exception" or "EventValue" ? 0 : TypeAttributes.Sealed), IsValueType = false, IsEnum = false, BaseType = parent ?? Type("Object"), Size = 24,
                PackingSize = 0, ClassSizeIsDefault = true }; definitions.Add(d); return d;
        }
        var owner = Define("EventCases"); var holder = Define("EventValue"); var baseException = Define("Exception", "mscorlib.dll", "System");
        var exception = Define("NullReferenceException", "mscorlib.dll", "System", new DefinitionRef(baseException, []));
        var invalidCast = Define("InvalidCastException", "mscorlib.dll", "System", new DefinitionRef(baseException, []));
        var field = new FieldDef { Index = 0, Owner = holder, Name = "Value", Attributes = FieldAttributes.Public, Type = Type("Int32"), Offset = 16 }; holder.Fields = [field];
        var methods = new List<MethodDef>();
        MethodDef Method(TypeDef type, string name, bool statics, TypeRef result, params TypeRef[] parameters)
        {
            var m = new MethodDef { Index = methods.Count, Owner = type, Name = name, Token = (uint)(0x06000001 + methods.Count),
                Attributes = MethodAttributes.Public | (statics ? MethodAttributes.Static : 0) | (name == ".ctor" ? MethodAttributes.SpecialName | MethodAttributes.RTSpecialName : 0),
                ImplAttributes = 0, Slot = -1, ReturnType = result, Parameters = parameters.Select((p, i) => new ParameterDef("p" + i, p, 0, null, false)).ToArray() };
            methods.Add(m); type.Methods = type.Methods.Append(m).ToArray(); return m;
        }
        Method(exception, ".ctor", false, Type("Void"));
        Method(invalidCast, ".ctor", false, Type("Void"));
        var readMethod = Method(holder, "Read", false, Type("Int32"));
        var genericParameter = new GenericParameterDef { Name = "U", Position = 0, Attributes = 0 };
        var genericValue = new GenericParameterRef("U", true, 0) { Parameter = genericParameter };
        var genericMethod = new MethodDef { Index = methods.Count, Owner = holder, Name = "Apply", Token = (uint)(0x06000001 + methods.Count),
            Attributes = MethodAttributes.Public | MethodAttributes.Virtual, ImplAttributes = 0, Slot = 3, ReturnType = genericValue,
            Parameters = [new("value", genericValue, 0, null, false)], GenericParameters = [genericParameter] };
        methods.Add(genericMethod); holder.Methods = holder.Methods.Append(genericMethod).ToArray();
        var genericInstance = new MethodRef(genericMethod, [], [Type("Int32")]);
        var cases = new[] { "NullRead", "NullExplicit", "NullCall", "NullOther", "IsBoxResult", "IsBoxOriginal", "UnknownBox", "UnusedTypeCheck", "UnboxThrow", "NoNullFusion", "GenericVirtual" }
            .Select(name => Method(owner, name, true, Type("Int32"), name == "NullOther"
                ? [new DefinitionRef(holder, []), new DefinitionRef(holder, [])] : name == "GenericVirtual" ? [new DefinitionRef(holder, []), Type("Int32")]
                : [name.StartsWith("Null", StringComparison.Ordinal) ? new DefinitionRef(holder, []) : Type("Object")])).ToArray();
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = [field], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(d => d.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var spec = InputCorpusChecks.Spec("arm64-v8a"); var layouts = new FieldLayouts(spec, 8, 8); var types = new ManagedTypes(program, layouts, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64()); var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var calls = new CallNamingQuery(binder, new NamingChecks.Map([new(MethodRef.Open(readMethod), BindingEntryKind.Ordinary)]), new NamingChecks.RuntimeMap(), catalog);
        var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        foreach (var method in cases)
        {
            var t = new TermTable(); var entry = new BlockIdentity(); var pass = new BlockIdentity(); var fail = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            var f = new FunctionBuilder(t, entry, 64, new(frame)) { ImageBase = image };
            Term Input(int n) { var slot = new AbstractSlot(SlotKind.Integer, n); var value = t.Atom(new EntryAtom(slot), 64); f.Inputs.Add(new(slot, value)); return value; }
            var obj = Input(0); var statements = new List<Statement>();
            Term Invoke(string operation, params Term[] inputs)
            {
                var fn = catalog.Functions.First(fn => fn.Operation.Name == operation && fn.Signature is not null);
                var id = new CallIdentity(); var result = t.Atom(new ResultAtom(id), 64);
                statements.Add(new Call(id, new NamedFunction(fn.MangledName), inputs.Select((v, i) => new SlotValue(new(SlotKind.Integer, i), v)).ToImmutableArray(),
                    fn.Operation.Result.Kind == RuntimeValueKind.Void ? [] : [new(new(SlotKind.Integer), result)], fn.Operation.DoesNotReturn)); return result;
            }
            Term Read(Term address, int width)
            { var id = new ReadIdentity(); var value = t.Atom(new ResultAtom(id), width); statements.Add(new MemoryRead(id, address, width, value)); return value; }
            var facts = NamingFacts.Empty; Term result;
            if (method.Name == "GenericVirtual")
            {
                var argument = Input(1); Invoke("CheckNull", obj);
                var info = Read(t.Apply(new CoreOperator(CoreOperation.Add), 64, image, t.Constant(256, 64)), 64);
                facts = facts with { Slots = facts.Slots.Add(256, Outcome<MetadataEntity>.Success(new MethodEntity(genericInstance))) };
                var objectClass = Read(obj, 64); var slot = Read(t.Apply(new CoreOperator(CoreOperation.Add), 64, info, t.Constant(spec.Layout.Field("MethodInfo", "slot").ByteOffset, 64)), 16);
                var offset = t.Apply(new CoreOperator(CoreOperation.Multiply), 64, t.Apply(new CoreOperator(CoreOperation.ZeroExtend), 64, slot), t.Constant(spec.Layout.VtableSlotSize, 64));
                var definition = Read(t.Apply(new CoreOperator(CoreOperation.Add), 64, t.Apply(new CoreOperator(CoreOperation.Add), 64, objectClass, offset),
                    t.Constant(spec.Layout.VtableStart + spec.Layout.Field("VirtualInvokeData", "method").ByteOffset, 64)), 64);
                var resolved = Invoke("ResolveGenericVirtual", definition, info);
                var pointer = Read(t.Apply(new CoreOperator(CoreOperation.Add), 64, resolved, t.Constant(spec.Layout.Field("MethodInfo", "virtualMethodPointer").ByteOffset, 64)), 64);
                var id = new CallIdentity(); result = t.Atom(new ResultAtom(id), 64);
                statements.Add(new Call(id, new ComputedTarget(pointer), [new(new(SlotKind.Integer), obj), new(new(SlotKind.Integer, 1), argument), new(new(SlotKind.Integer, 2), resolved)], [new(new(SlotKind.Integer), result)]));
                f.Blocks.Add(new(entry, [], [.. statements], new Return([new(new(SlotKind.Integer), result)])));
            }
            else if (method.Name.StartsWith("Null", StringComparison.Ordinal))
            {
                Invoke("CheckNull", obj);
                if (method.Name == "NullExplicit") result = t.Constant(7, 64);
                else if (method.Name == "NullCall")
                {
                    var id = new CallIdentity(); result = t.Atom(new ResultAtom(id), 64);
                    statements.Add(new Call(id, new ImageFunction(10), [new(new(SlotKind.Integer), obj), new(new(SlotKind.Integer, 1), t.Constant(0, 64))], [new(new(SlotKind.Integer), result)]));
                }
                else result = Read(t.Apply(new CoreOperator(CoreOperation.Add), 64, method.Name == "NullOther" ? Input(1) : obj, t.Constant(16, 64)), 32);
                f.Blocks.Add(new(entry, [], [.. statements], new Return([new(new(SlotKind.Integer), result.Width == 32 ? t.Concat(result, t.Constant(0, 32)) : result)])));
            }
            else
            {
                var klass = Read(t.Apply(new CoreOperator(CoreOperation.Add), 64, image, t.Constant(128, 64)), 64);
                facts = facts with { Slots = facts.Slots.Add(128, Outcome<MetadataEntity>.Success(new ClassEntity(Type("Int32")))) };
                if (method.Name == "UnboxThrow") Invoke("CheckNull", obj);
                var tested = method.Name == "UnknownBox" ? obj : Invoke("IsInstance", obj, klass);
                if (method.Name is "UnknownBox" or "UnusedTypeCheck")
                {
                    var address = Invoke("UnboxUnchecked", obj); result = Read(address, 32);
                    f.Blocks.Add(new(entry, [], [.. statements], new Return([new(new(SlotKind.Integer), t.Concat(result, t.Constant(0, 32)))])));
                }
                else
                {
                    f.Blocks.Add(new(entry, [], [.. statements], new Branch(t.Apply(new CoreOperator(CoreOperation.NotEqual), 1, tested, t.Constant(0, 64)), pass, fail)));
                    statements.Clear(); var address = Invoke("UnboxUnchecked", method.Name == "IsBoxResult" ? tested : obj); result = Read(address, 32);
                    f.Blocks.Add(new(pass, [], [.. statements], new Return([new(new(SlotKind.Integer), t.Concat(result, t.Constant(0, 32)))])));
                    if (method.Name is "UnboxThrow" or "NoNullFusion")
                    { statements.Clear(); Invoke("ThrowInvalidCast", obj, klass); f.Blocks.Add(new(fail, [], [.. statements], new Unreachable())); }
                    else f.Blocks.Add(new(fail, [], [], new Return([new(new(SlotKind.Integer), t.Constant(9, 64))])));
                }
            }
            var function = f.Freeze();
            if (method.Name is "UnboxThrow" or "NoNullFusion")
            {
                var state = new StateQueries(); var names = new ValueNamingQuery(state, calls, facts, spec, binder, binder.Entry(MethodRef.Open(method), BindingEntryKind.Ordinary).Value);
                var locations = new ManagedLocationQuery(state, names, layouts, spec);
                var transformed = new UnobservableEffects(state, calls, names, new InputMemoryImage(), new HashSet<AbstractSlot> { new(SlotKind.Integer) }, locations).Run(function);
                checks.True(transformed.Records.Any(r => r.Kind == "checked-unbox") == (method.Name == "UnboxThrow"), method.Name + " 只在输入先非空时合并类型判断与拆箱");
                function = transformed.Function;
            }
            var lowered = new IntegerLowering(function, MethodRef.Open(method), binder, types, calls: calls, effects: new ManagedCallEffects(calls), spec: spec, names: facts).Run();
            if (method.Name is "UnknownBox" or "UnusedTypeCheck")
            {
                checks.True(lowered.Failure?.Reason.Code == (method.Name == "UnknownBox" ? "lowering.UnboxUnchecked.Type" : "lowering.UnboxUnchecked.Success"), method.Name + " 缺少凭据保持具体洞：" + lowered.Failure);
                continue;
            }
            checks.True(lowered.Body is not null, method.Name + " 下降：" + lowered.Failure);
            if (lowered.Body is not { } body) continue;
            checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCheck>().Count() == (method.Name is "NullExplicit" or "NullOther" or "GenericVirtual" ? 1 : 0), method.Name + " 吸收与显式抛出分开");
            if (method.Name == "NullCall") checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Single().Invocation.Virtual, "非虚实例接收者判空由 callvirt 承担");
            if (method.Name == "GenericVirtual") checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Single().Invocation is { Virtual: true, Method: var invoked } && invoked == genericInstance,
                "泛型解析与目标读取只输出对应泛型 callvirt");
            checks.True(emitter.Emit([body]).Count == 0, method.Name + " CIL 契约");
            var testedMethod = source.Method("EventCases", method.Name + "Out"); testedMethod.Body = skeleton.Method(method).Body;
            Mono.Cecil.TypeReference MapType(Mono.Cecil.TypeReference type) => type.FullName switch
            {
                "EventValue" => source.Module.GetType("EventValue"), "System.Int32" => source.Module.TypeSystem.Int32, "System.Object" => source.Module.TypeSystem.Object,
                _ => type,
            };
            foreach (var local in testedMethod.Body.Variables) local.VariableType = MapType(local.VariableType);
            Mono.Cecil.MethodReference MapMethod(Mono.Cecil.GenericInstanceMethod called)
            {
                var mapped = new Mono.Cecil.GenericInstanceMethod(source.Method("EventValue", called.Name));
                foreach (var argument in called.GenericArguments) mapped.GenericArguments.Add(MapType(argument));
                return mapped;
            }
            foreach (var instruction in testedMethod.Body.Instructions)
                instruction.Operand = instruction.Operand switch
                {
                    Mono.Cecil.MethodReference called when called.DeclaringType.FullName is "System.NullReferenceException" or "System.InvalidCastException" => source.Module.ImportReference(
                        (called.DeclaringType.FullName == "System.NullReferenceException" ? typeof(NullReferenceException) : typeof(InvalidCastException)).GetConstructor(System.Type.EmptyTypes)!),
                    Mono.Cecil.GenericInstanceMethod called => MapMethod(called),
                    Mono.Cecil.MethodReference called when called.DeclaringType.FullName == "EventValue" => source.Method("EventValue", called.Name),
                    Mono.Cecil.FieldReference access => source.Module.GetType("EventValue").Fields.Single(f => f.Name == access.Name),
                    Mono.Cecil.TypeReference type => MapType(type), Mono.Cecil.ParameterDefinition parameter => testedMethod.Parameters[parameter.Index], _ => instruction.Operand,
                };
            var comparison = CilComparison.Compare(source.Method("EventCases", method.Name), testedMethod);
            checks.True(comparison.Status == CilComparisonStatus.Match && comparison.CompletedCases == 32, method.Name + " 32 个输入执行对照：" + comparison);
            if (method.Name.StartsWith("Null", StringComparison.Ordinal))
            {
                var model = new CecilModel(source.Module); var index = new WorldIndex(model.Program, new ManagedTypes(model.Program, new ManagedStorage(model.Prepare), 8));
                var interpreter = new CilInterpreter(model, index) { BodyModule = source.Module };
                foreach (bool isNull in new[] { true, false })
                {
                    var target = model.Method(testedMethod); var world = new World(index, 0, new Hints([], []), target.DeclaringType);
                    var value = isNull ? 0 : world.Instance(new DefinitionRef(model.Program.Types.Single(d => d.Name == "EventValue"), []), "value", 0);
                    var arguments = method.Name == "NullOther" ? new[] { StackValue.O(value), StackValue.O(value) } : new[] { StackValue.O(value) };
                    var left = interpreter.Run(world, source.Method("EventCases", method.Name), model.Method(source.Method("EventCases", method.Name)), arguments);
                    var right = interpreter.Run(world, testedMethod, target, arguments);
                    checks.True(Execution.Trace.Difference(world, left, right) is null, method.Name + (isNull ? " 空值抛出路径" : " 非空正常路径"));
                    checks.True(isNull ? right.Events.Any(e => e.Text.StartsWith("throw System.NullReferenceException ", StringComparison.Ordinal)) : right.Result?.StartsWith("return ", StringComparison.Ordinal) == true,
                        method.Name + " 路径确实执行：" + right.Result);
                }
            }
            if (method.Name is "IsBoxResult" or "IsBoxOriginal" or "UnboxThrow" or "NoNullFusion")
            foreach (var input in new[] { "box", "null", "wrong" })
            {
                Mono.Cecil.MethodDefinition Wrapper(string name, Mono.Cecil.MethodDefinition called)
                {
                    var wrapper = new Mono.Cecil.MethodDefinition(name, Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static, source.Module.TypeSystem.Int32);
                    source.Module.GetType("EventCases").Methods.Add(wrapper);
                    var il = wrapper.Body.GetILProcessor();
                    if (input == "box")
                    {
                        il.Emit(Mono.Cecil.Cil.OpCodes.Ldc_I4, 37);
                        il.Emit(Mono.Cecil.Cil.OpCodes.Box, source.Module.TypeSystem.Int32);
                    }
                    else if (input == "null") il.Emit(Mono.Cecil.Cil.OpCodes.Ldnull);
                    else il.Emit(Mono.Cecil.Cil.OpCodes.Ldstr, "wrong");
                    il.Emit(Mono.Cecil.Cil.OpCodes.Call, called); il.Emit(Mono.Cecil.Cil.OpCodes.Ret);
                    return wrapper;
                }
                var reference = Wrapper(method.Name + input, source.Method("EventCases", method.Name));
                var tested = Wrapper(method.Name + input + "Out", testedMethod);
                var model = new CecilModel(source.Module); var index = new WorldIndex(model.Program, new ManagedTypes(model.Program, new ManagedStorage(model.Prepare), 8));
                var interpreter = new CilInterpreter(model, index) { BodyModule = source.Module };
                var target = model.Method(tested); var world = new World(index, 0, new Hints([], []), target.DeclaringType);
                var left = interpreter.Run(world, reference, model.Method(reference), []);
                var right = interpreter.Run(world, tested, target, []);
                checks.True(Execution.Trace.Difference(world, left, right) is null, method.Name + " 固定拆箱输入 " + input);
                var expected = input == "box" ? "return 0x25" : method.Name is "IsBoxResult" or "IsBoxOriginal" ? "return 0x9" : null;
                checks.True(expected is not null ? right.Result == expected : right.Events.Any(e => e.Text.StartsWith("throw " +
                    (input == "null" && method.Name == "UnboxThrow" ? "System.NullReferenceException " : "System.InvalidCastException "), StringComparison.Ordinal)),
                    method.Name + " 固定输入路径确实执行 " + input + "：" + right.Result);
            }
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
}
