using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
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
    private static void MergedAllocationChecks(Assertions checks, ProgramModel primitives)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a"); var layouts = new FieldLayouts(spec, 8, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").ToList();
        TypeRef Type(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        TypeDef Define(string name)
        {
            var type = new TypeDef { Index = definitions.Count, Assembly = "MergedAllocations.dll", Namespace = "", Name = name,
                Token = (uint)(0x02000001 + definitions.Count), Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false, BaseType = Type("Object") };
            definitions.Add(type); return type;
        }
        var owner = Define("Cases"); var error = Define("MessageError"); Define("OtherError");
        var methods = new List<MethodDef>();
        MethodDef Method(TypeDef type, string name, TypeRef[] parameters, bool constructor = false)
        {
            var method = new MethodDef { Index = methods.Count, Owner = type, Name = name, Token = (uint)(0x06000001 + methods.Count),
                Attributes = MethodAttributes.Public | (constructor ? MethodAttributes.SpecialName | MethodAttributes.RTSpecialName : MethodAttributes.Static), ImplAttributes = 0, Slot = -1,
                ReturnType = Type("Void"), Parameters = parameters.Select((p, i) => new ParameterDef("p" + i, p, 0, null, false)).ToArray() };
            methods.Add(method); type.Methods = type.Methods.Append(method).ToArray(); return method;
        }
        var constructor = Method(error, ".ctor", [Type("String")], true);
        var touch = Method(owner, "Touch", []);
        string[] modes = ["Two", "Three", "Nested", "Duplicate", "NotAllocation", "DifferentClass", "CallBetween", "UsedBefore", "FirstUse", "PrivateUseAfterMerge", "CallAfterMerge", "TrapBetween", "SplitExit", "Cycle", "OtherMergeUse"];
        var callers = modes.ToDictionary(mode => mode, mode => Method(owner, mode, [Type("Int32")]));
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = [], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(d => d.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var types = new ManagedTypes(program, layouts, 8); var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var calls = new CallNamingQuery(binder, new ReferenceCodeMap(constructor, touch), new NamingChecks.RuntimeMap(catalog.Functions[0]), catalog);
        using var source = new CompiledSource("""
            public class MessageError : System.Exception { public MessageError(string message) : base(message) { } }
            public static class Cases {
                public static void Reference(int value) { if (value == 0) throw new MessageError("left message"); throw new MessageError("right message"); }
                public static void Three(int value) { if (value == 0) throw new MessageError("left message"); if (value == 1) throw new MessageError("middle message"); throw new MessageError("right message"); }
                public static void Output(int value) { }
            }
            """);
        foreach (var mode in modes)
        {
            var t = new TermTable(); var head = new BlockIdentity(); var left = new BlockIdentity(); var right = new BlockIdentity(); var join = new BlockIdentity(); var middle = new BlockIdentity(); var decision = new BlockIdentity(); var exit = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            var slot = new AbstractSlot(SlotKind.Integer); var parameter = t.Atom(new EntryAtom(slot), 64);
            var f = new FunctionBuilder(t, head, 64, new(frame)) { ImageBase = image }; f.Inputs.Add(new(slot, parameter));
            var facts = NamingFacts.Empty;
            Term Address(Term root, ulong offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, root, t.Constant(offset, 64));
            var privateSlot = Address(frame, unchecked((ulong)-16L));
            Term Entity(ulong offset, MetadataEntity entity, List<Statement> statements)
            {
                var id = new ReadIdentity(); var value = t.Atom(new ResultAtom(id), 64);
                statements.Add(new MemoryRead(id, Address(image, offset), 64, value)); facts = facts with { Slots = facts.Slots.SetItem(offset, Outcome<MetadataEntity>.Success(entity)) }; return value;
            }
            Term Invoke(string name, List<Statement> list, params Term[] inputs)
            {
                var runtime = catalog.Functions.First(r => r.Operation.Name == name && r.Signature is not null);
                var id = new CallIdentity(); var value = t.Atom(new ResultAtom(id), 64);
                list.Add(new Call(id, new NamedFunction(runtime.MangledName), inputs.Select((v, i) => new SlotValue(new(SlotKind.Integer, i), v)).ToImmutableArray(),
                    runtime.Operation.Result.Kind == RuntimeValueKind.Void ? [] : [new(slot, value)], runtime.Operation.DoesNotReturn)); return value;
            }
            var ls = new List<Statement>(); var rs = new List<Statement>(); var ms = new List<Statement>(); var js = new List<Statement>();
            var a = Invoke("AllocateObject", ls, Entity(128, new ClassEntity(Type("MessageError")), ls));
            var b = mode == "NotAllocation" ? t.Constant(0, 64) : Invoke("AllocateObject", rs, Entity(136, new ClassEntity(Type(mode == "DifferentClass" ? "OtherError" : "MessageError")), rs));
            var firstText = Entity(144, new StringEntity("left message"), ls); var lastText = Entity(152, new StringEntity("right message"), rs);
            // 独立的帧写入和元数据读取允许跨过，存入新对象本身则属于使用。
            ls.Add(new MemoryWrite(new(), privateSlot, 64, mode == "UsedBefore" ? a : t.Constant(7, 64)));
            if (mode == "CallBetween") ls.Add(new Call(new(), new ImageFunction(11), [new(slot, t.Constant(0, 64))], []));
            if (mode == "TrapBetween") ls.Add(new TrapWhen(new(), t.Slice(parameter, 0, 1)));
            var mid = new MergeIdentity(); var merged = t.Atom(new ResultAtom(mid), 64);
            var sid = new MergeIdentity(); var text = t.Atom(new ResultAtom(sid), 64);
            var objects = new List<Incoming> { new(left, a), new(right, b) }; var strings = new List<Incoming> { new(left, firstText), new(right, lastText) };
            var isZero = t.Apply(new CoreOperator(CoreOperation.Equal), 1, t.Slice(parameter, 0, 32), t.Constant(0, 32));
            f.Blocks.Add(new(head, [], [], new Branch(isZero, left, mode is "Three" or "Nested" ? decision : right)));
            if (mode is "Three" or "Nested")
            {
                var third = Invoke("AllocateObject", ms, Entity(160, new ClassEntity(Type("MessageError")), ms)); var middleText = Entity(168, new StringEntity("middle message"), ms);
                if (mode == "Nested")
                {
                    var objectId = new MergeIdentity(); var objectValue = t.Atom(new ResultAtom(objectId), 64);
                    var stringId = new MergeIdentity(); var stringValue = t.Atom(new ResultAtom(stringId), 64);
                    f.Blocks.Add(new(exit, [new(objectId, objectValue, [new(left, a), new(middle, third)]),
                        new(stringId, stringValue, [new(left, firstText), new(middle, middleText)])], [], new Jump(join)));
                    objects[0] = new(exit, objectValue); strings[0] = new(exit, stringValue);
                }
                else { objects.Add(new(middle, third)); strings.Add(new(middle, middleText)); }
                f.Blocks.Add(new(decision, [], [], new Branch(t.Apply(new CoreOperator(CoreOperation.Equal), 1, t.Slice(parameter, 0, 32), t.Constant(1, 32)), middle, right)));
                f.Blocks.Add(new(middle, [], [.. ms], new Jump(mode == "Nested" ? exit : join)));
            }
            if (mode == "Cycle")
            {
                objects[0] = new(decision, a); strings[0] = new(decision, firstText);
                f.Blocks.Add(new(decision, [], [], new Branch(t.Slice(parameter, 1, 1), join, decision)));
            }
            f.Blocks.Add(new(left, [], [.. ls], mode == "SplitExit" ? new Branch(t.Slice(parameter, 1, 1), join, exit) : new Jump(mode == "Cycle" ? decision : mode == "Nested" ? exit : join)));
            f.Blocks.Add(new(right, [], [.. rs], new Jump(join)));
            if (mode == "SplitExit") f.Blocks.Add(new(exit, [], [], new Return([])));
            if (mode == "PrivateUseAfterMerge") js.Add(new MemoryWrite(new(), privateSlot, 64, merged));
            if (mode == "CallAfterMerge") js.Add(new Call(new(), new ImageFunction(11), [new(slot, t.Constant(0, 64))], []));
            var joinMerges = new List<Merge> { new(mid, merged, [.. objects]), new(sid, text, [.. strings]) };
            var exceptionValue = merged;
            if (mode is "OtherMergeUse" or "Duplicate")
            {
                var other = new MergeIdentity(); var alias = t.Atom(new ResultAtom(other), 64); joinMerges.Add(new(other, alias, [.. objects]));
                if (mode == "Duplicate") exceptionValue = alias;
                else js.Add(new MemoryWrite(new(), privateSlot, 64, alias));
            }
            if (mode != "FirstUse") js.Add(new Call(new(), new ImageFunction(10), [new(slot, merged), new(new(SlotKind.Integer, 1), text), new(new(SlotKind.Integer, 2), t.Constant(0, 64))], []));
            Invoke("ThrowManaged", js, exceptionValue, t.Constant(0, 64));
            f.Blocks.Add(new(join, [.. joinMerges], [.. js], new Unreachable()));
            var input = f.Freeze(); checks.True(ExitChecker.Check(input).IsValid, mode + " 分配合流输入契约");
            var lowered = new IntegerLowering(input, MethodRef.Open(callers[mode]), binder, types, calls: calls, effects: new ManagedCallEffects(calls), spec: spec, names: facts).Run();
            if (mode is not ("Two" or "Three" or "Nested" or "Duplicate"))
            {
                var reason = mode switch { "NotAllocation" => "Input", "DifferentClass" => "Class.Constructor", "CallBetween" or "TrapBetween" or "CallAfterMerge" => "Event", "UsedBefore" => "Used", "SplitExit" or "Cycle" => "Flow", _ => "FirstUse" };
                checks.True(lowered.Body is null && lowered.Failure?.Reason.Code == (mode == "TrapBetween" ? "lowering.ConditionalTrap" : "lowering.Allocation.Merge." + reason), mode + " 保留明确的分配合流洞：" + lowered.Failure); continue;
            }
            checks.True(lowered.Body is not null, mode + " 同类分配与合流实参配对：" + lowered.Failure); if (lowered.Body is not { } body) continue;
            checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().Count(s => s.Value is NewObjectValue) == 1, mode + " 汇合处只创建一个对象");
            checks.True(emitter.Emit([body]).Count == 0, mode + " 分配合流 CIL 校验");
            var tested = source.Method("Cases", "Output"); tested.Body = skeleton.Method(callers[mode]).Body;
            var core = source.Module.TypeSystem.Object.Resolve().Module;
            Mono.Cecil.TypeReference MapType(Mono.Cecil.TypeReference type) => source.Module.ImportReference(source.Module.GetType(type.FullName) ?? core.GetType(type.FullName));
            foreach (var local in tested.Body.Variables) local.VariableType = MapType(local.VariableType);
            foreach (var instruction in tested.Body.Instructions) instruction.Operand = instruction.Operand switch {
                Mono.Cecil.MethodReference method => source.Module.ImportReference(source.Module.GetType(method.DeclaringType.FullName).Methods.Single(m => m.FullName == method.FullName)),
                Mono.Cecil.TypeReference type => MapType(type), Mono.Cecil.ParameterDefinition p => tested.Parameters[p.Index], _ => instruction.Operand };
            var comparison = CilComparison.Compare(source.Method("Cases", mode is "Two" or "Duplicate" ? "Reference" : "Three"), tested);
            checks.True(comparison.Status == CilComparisonStatus.Match, mode + " 各条抛出路径的构造与消息执行对照：" + comparison);
            checks.True(comparison.Coverage?.Branches.All(b => b.Directions.All(x => x)) == true, mode + " 所有分支方向均执行");
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
    private static void DeferredAllocationChecks(Assertions checks, ProgramModel primitives)
    {
        using var source = new CompiledSource("""
            public class Constructed { public int Value; public Constructed(int value) { Value = value; } }
            public class RelaxedConstructed { public static int Seed = 3; public int Value; public RelaxedConstructed(int value) { Value = value; } }
            public static class DeferredCases {
                public static int Side(int value) => value + 3;
                public static void Consume(object value) { }
                public static Constructed Image(int[] values, int n) => new Constructed(7);
                public static Constructed Length(int[] values, int n) => new Constructed(values.Length);
                public static Constructed ArgumentCall(int[] values, int n) => new Constructed(Side(n));
                public static Constructed IndependentCall(int[] values, int n) { Side(n); return new Constructed(7); }
                public static Constructed Check(int[] values, int n) { if (values == null) throw new System.NullReferenceException(); return new Constructed(7); }
                public static Constructed Runtime(int[] values, int n) => new Constructed(7);
                public static Constructed Jump(int[] values, int n) => new Constructed(7);
                public static Constructed Diamond(int[] values, int n) { if (n == 0) return new Constructed(5); return new Constructed(9); }
                public static Constructed Private(int[] values, int n) => new Constructed(7);
                public static RelaxedConstructed RelaxedCall(int[] values, int n) => new RelaxedConstructed(Side(n));
                public static Constructed Output(int[] values, int n) => null;
                public static RelaxedConstructed RelaxedOutput(int[] values, int n) => null;
            }
            """);
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").ToList();
        int objectIndex = definitions.FindIndex(t => t.Name == "Object"); var originalObject = definitions[objectIndex];
        definitions[objectIndex] = new TypeDef { Index = originalObject.Index, Assembly = originalObject.Assembly, Namespace = originalObject.Namespace,
            Name = originalObject.Name, Token = originalObject.Token, Attributes = originalObject.Attributes, IsValueType = false, IsEnum = false,
            Size = 16, PackingSize = 0, ClassSizeIsDefault = true };
        TypeRef Type(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        TypeDef Define(string name, bool relaxed = false, bool core = false)
        {
            var type = new TypeDef { Index = definitions.Count, Assembly = core ? "mscorlib.dll" : "DeferredAllocations.dll", Namespace = core ? "System" : "", Name = name,
                Token = (uint)(0x02000001 + definitions.Count), Attributes = TypeAttributes.Public | (relaxed ? TypeAttributes.BeforeFieldInit : 0), IsValueType = false,
                IsEnum = false, BaseType = Type(name == "NullReferenceException" ? "Exception" : "Object"), Size = 24, PackingSize = 0, ClassSizeIsDefault = true };
            definitions.Add(type); return type;
        }
        var owner = Define("DeferredCases"); var created = Define("Constructed"); var precise = Define("PreciseConstructed"); var relaxed = Define("RelaxedConstructed", true);
        Define("Exception", core: true); var nullError = Define("NullReferenceException", core: true);
        var fields = new[] { created, precise, relaxed }.Select((type, i) => new FieldDef { Index = i, Owner = type, Name = "Value", Type = Type("Int32"), Offset = 16, Attributes = FieldAttributes.Public }).ToArray();
        foreach (var field in fields) field.Owner.Fields = [field];
        var methods = new List<MethodDef>();
        MethodDef Method(TypeDef type, string name, bool statics, TypeRef result, params TypeRef[] parameters)
        {
            var method = new MethodDef { Index = methods.Count, Owner = type, Name = name, Token = (uint)(0x06000001 + methods.Count),
                Attributes = MethodAttributes.Public | (statics ? MethodAttributes.Static : 0) | (name is ".ctor" or ".cctor" ? MethodAttributes.SpecialName | MethodAttributes.RTSpecialName : 0),
                ImplAttributes = 0, Slot = -1, ReturnType = result, Parameters = parameters.Select((p, i) => new ParameterDef("p" + i, p, 0, null, false)).ToArray() };
            methods.Add(method); type.Methods = type.Methods.Append(method).ToArray(); return method;
        }
        var ctor = Method(created, ".ctor", false, Type("Void"), Type("Int32"));
        var side = Method(owner, "Side", true, Type("Int32"), Type("Int32"));
        var consume = Method(owner, "Consume", true, Type("Void"), Type("Object"));
        var preciseCtor = Method(precise, ".ctor", false, Type("Void"), Type("Int32"));
        var relaxedCtor = Method(relaxed, ".ctor", false, Type("Void"), Type("Int32"));
        Method(precise, ".cctor", true, Type("Void")); Method(relaxed, ".cctor", true, Type("Void")); Method(nullError, ".ctor", false, Type("Void"));
        string[] positive = ["Image", "Length", "ArgumentCall", "IndependentCall", "Check", "Runtime", "Jump", "Diamond", "Private", "RelaxedCall"];
        string[] negative = ["ObjectCall", "PreciseCall", "PreciseRead", "Partial", "Cycle", "ObjectWrite", "OtherConstructor"];
        var callers = positive.Concat(negative).ToDictionary(mode => mode, mode => Method(owner, mode, true,
            Type(mode.StartsWith("Precise", StringComparison.Ordinal) ? "PreciseConstructed" : mode == "RelaxedCall" ? "RelaxedConstructed" : "Constructed"), new ArrayRef(Type("Int32"), 1), Type("Int32")));
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = fields, RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(d => d.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var spec = InputCorpusChecks.Spec("arm64-v8a"); var layouts = new FieldLayouts(spec, 8, 8); var types = new ManagedTypes(program, layouts, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64()); var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var calls = new CallNamingQuery(binder, new ReferenceCodeMap(ctor, side, consume, preciseCtor, relaxedCtor), new NamingChecks.RuntimeMap(), catalog);
        var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        foreach (var mode in positive.Concat(negative))
        {
            var t = new TermTable(); var entry = new BlockIdentity(); var continuation = new BlockIdentity(); var left = new BlockIdentity(); var right = new BlockIdentity();
            var slot = new AbstractSlot(SlotKind.Integer); var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            var values = t.Atom(new EntryAtom(slot), 64); var n = t.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64);
            var f = new FunctionBuilder(t, entry, 64, new(frame)) { ImageBase = image }; f.Inputs.Add(new(slot, values)); f.Inputs.Add(new(new(SlotKind.Integer, 1), n));
            Term Add(Term root, ulong offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, root, t.Constant(offset, 64));
            var statements = new List<Statement>(); var facts = NamingFacts.Empty;
            Term Read(Term address, int width)
            { var id = new ReadIdentity(); var result = t.Atom(new ResultAtom(id), width); statements.Add(new MemoryRead(id, address, width, result)); return result; }
            Term Entity(ulong offset, MetadataEntity entity)
            { facts = facts with { Slots = facts.Slots.Add(offset, Outcome<MetadataEntity>.Success(entity)) }; return Read(Add(image, offset), 64); }
            Term Invoke(string operation, params Term[] inputs)
            {
                var runtime = catalog.Functions.First(r => r.Operation.Name == operation && r.Signature is not null);
                var id = new CallIdentity(); var result = t.Atom(new ResultAtom(id), 64);
                statements.Add(new Call(id, new NamedFunction(runtime.MangledName), inputs.Select((v, i) => new SlotValue(new(SlotKind.Integer, i), v)).ToImmutableArray(),
                    runtime.Operation.Result.Kind == RuntimeValueKind.Void ? [] : [new(slot, result)], runtime.Operation.DoesNotReturn)); return result;
            }
            var target = mode.StartsWith("Precise", StringComparison.Ordinal) ? preciseCtor : mode == "RelaxedCall" ? relaxedCtor : ctor;
            var obj = Invoke("AllocateObject", Entity(128, new ClassEntity(MethodRef.Open(target).DeclaringType)));
            var argument = t.Constant(7, 64); var information = t.Constant(0, 64);
            if (mode == "Image") information = Entity(136, new MethodEntity(MethodRef.Open(target)));
            if (mode is "Length" or "PreciseRead") argument = Read(Add(values, (ulong)spec.Layout.Field("Il2CppArray", "max_length").ByteOffset), 32);
            if (mode is "ArgumentCall" or "IndependentCall" or "PreciseCall" or "RelaxedCall")
            {
                var id = new CallIdentity(); var result = t.Atom(new ResultAtom(id), 64);
                statements.Add(new Call(id, new ImageFunction(11), [new(slot, n), new(new(SlotKind.Integer, 1), t.Constant(0, 64))], [new(slot, result)]));
                if (mode != "IndependentCall") argument = result;
            }
            if (mode == "Check") Invoke("CheckNull", values);
            if (mode == "Runtime") Invoke("IsInstance", values, Entity(144, new ClassEntity(Type("Object"))));
            if (mode == "ObjectCall") statements.Add(new Call(new(), new ImageFunction(12), [new(slot, obj), new(new(SlotKind.Integer, 1), t.Constant(0, 64))], []));
            if (mode == "ObjectWrite") statements.Add(new MemoryWrite(new(), Add(obj, 16), 32, t.Slice(n, 0, 32)));
            if (mode == "Private")
            { var address = Add(frame, unchecked((ulong)-16L)); statements.Add(new MemoryWrite(new(), address, 64, argument)); argument = Read(address, 64); }
            if (mode == "Diamond")
            {
                f.Blocks.Add(new(entry, [], [.. statements], new Branch(t.Apply(new CoreOperator(CoreOperation.Equal), 1, t.Slice(n, 0, 32), t.Constant(0, 32)), left, right)));
                f.Blocks.Add(new(left, [], [], new Jump(continuation))); f.Blocks.Add(new(right, [], [], new Jump(continuation)));
                var id = new MergeIdentity(); argument = t.Atom(new ResultAtom(id), 64);
                statements.Clear();
                var construction = new Call(new(), new ImageFunction(10), [new(slot, obj), new(new(SlotKind.Integer, 1), argument), new(new(SlotKind.Integer, 2), information)], []);
                f.Blocks.Add(new(continuation, [new(id, argument, [new(left, t.Constant(5, 64)), new(right, t.Constant(9, 64))])], [construction], new Return([new(slot, obj)])));
            }
            else
            {
                if (mode is "Jump" or "Partial" or "Cycle" or "OtherConstructor")
                {
                    var condition = t.Apply(new CoreOperator(CoreOperation.Equal), 1, t.Slice(n, 0, 32), t.Constant(0, 32));
                    f.Blocks.Add(new(entry, [], [.. statements], mode == "Jump" ? new Jump(continuation) : new Branch(condition, continuation, right))); statements.Clear();
                    f.Blocks.Add(new(right, [], mode == "OtherConstructor" ? [new Call(new(), new ImageFunction(10), [new(slot, obj), new(new(SlotKind.Integer, 1), t.Constant(9, 64)), new(new(SlotKind.Integer, 2), information)], [])] : [],
                        mode == "Cycle" ? new Jump(right) : new Return([new(slot, mode == "OtherConstructor" ? obj : t.Constant(0, 64))])));
                }
                ulong targetAddress = target == preciseCtor ? 13UL : target == relaxedCtor ? 14UL : 10UL;
                statements.Add(new Call(new(), new ImageFunction(targetAddress), [new(slot, obj), new(new(SlotKind.Integer, 1), argument), new(new(SlotKind.Integer, 2), information)], []));
                f.Blocks.Add(new(mode is "Jump" or "Partial" or "Cycle" or "OtherConstructor" ? continuation : entry, [], [.. statements], new Return([new(slot, obj)])));
            }
            var input = f.Freeze(); checks.True(ExitChecker.Check(input).IsValid, mode + " 延后分配输入契约");
            var lowered = new IntegerLowering(input, MethodRef.Open(callers[mode]), binder, types, calls: calls, effects: new ManagedCallEffects(calls), spec: spec, names: facts).Run();
            if (negative.Contains(mode))
            {
                checks.True(lowered.Body is null, mode + " 不接受未证明的分配移动");
                if (mode.StartsWith("Precise", StringComparison.Ordinal)) checks.True(lowered.Failure?.Reason.Code == "lowering.Allocation.Deferred.ClassInitialization", mode + " 区分可观察类初始化：" + lowered.Failure);
                if (mode is "Partial" or "Cycle" or "OtherConstructor") checks.True(lowered.Failure?.Reason.Code == "lowering.Allocation.Deferred.Flow", mode + " 区分路径缺口：" + lowered.Failure);
                continue;
            }
            checks.True(lowered.Body is not null, mode + " 延后分配配对：" + lowered.Failure); if (lowered.Body is not { } body) continue;
            checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().Count(s => s.Value is NewObjectValue) == 1, mode + " 只在构造点创建对象");
            checks.True(emitter.Emit([body]).Count == 0, mode + " 延后分配 CIL 校验");
            var tested = source.Method("DeferredCases", mode == "RelaxedCall" ? "RelaxedOutput" : "Output"); tested.Body = skeleton.Method(callers[mode]).Body;
            var core = source.Module.TypeSystem.Object.Resolve().Module;
            Mono.Cecil.TypeReference MapType(Mono.Cecil.TypeReference type) => type is Mono.Cecil.ArrayType array ? new Mono.Cecil.ArrayType(MapType(array.ElementType))
                : source.Module.ImportReference(source.Module.GetType(type.FullName) ?? core.GetType(type.FullName));
            foreach (var local in tested.Body.Variables) local.VariableType = MapType(local.VariableType);
            foreach (var instruction in tested.Body.Instructions) instruction.Operand = instruction.Operand switch {
                Mono.Cecil.MethodReference method => source.Module.ImportReference((source.Module.GetType(method.DeclaringType.FullName) ?? core.GetType(method.DeclaringType.FullName)).Methods.Single(m => m.FullName == method.FullName)),
                Mono.Cecil.TypeReference type => MapType(type), Mono.Cecil.ParameterDefinition p => tested.Parameters[p.Index], _ => instruction.Operand };
            var comparison = CilComparison.Compare(source.Method("DeferredCases", mode), tested);
            checks.True(comparison.Status == CilComparisonStatus.Match, mode + " newobj 次序、实参和异常执行对照：" + comparison);
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
}
