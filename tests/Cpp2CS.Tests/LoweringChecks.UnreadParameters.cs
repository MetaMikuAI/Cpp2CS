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
    private sealed class ParameterReadMap(Dictionary<ulong, MethodRef[]> methods) : IBindingCodeMap
    {
        public ImmutableArray<BindingEntry> At(ulong entry) => methods.TryGetValue(entry, out var found)
            ? [.. found.Select(method => new BindingEntry(method, BindingEntryKind.Ordinary))] : [];
    }
    private sealed class ParameterRuntimeMap(RuntimeFunction function) : IRuntimeFunctionMap
    { public RuntimeFunction? Find(CallTarget target) => target is ImageFunction { EntryOffset: 1 } ? function : null; }
    private sealed class ParameterReadSource(Func<MethodRef, Outcome<ParameterReads>> prove) : IParameterReadsSource
    {
        public int Requests { get; private set; }
        public Outcome<ParameterReads> Get(ulong entry, MethodRef method) { Requests++; return prove(method); }
    }
    private static void UnreadParameterChecks(Assertions checks, ProgramModel primitives)
    {
        using var reference = new CompiledSource("""
            public struct UnreadData { public long First, Second; }
            public interface IUnreadTarget { int FinalThis(); }
            public class UnreadHost : IUnreadTarget {
                public static int Producer() => 3;
                public static long Producer64() => 3;
                public static string ProducerText() => "value";
                public static void Barrier() { }
                public static int Ignore(UnreadHost value) => 7;
                public static int IgnoreData(UnreadData value) => 7;
                public static int IgnoreRef(ref UnreadHost value) => 7;
                public int IgnoreThis() => 7;
                public int FinalThis() => 7;
                public static int Use(UnreadHost value) { Producer(); return Ignore(value); }
                public static int UseOut(UnreadHost value) => 0;
                public static int UseMerged(UnreadHost value, bool choose) { Producer(); return Ignore(value); }
                public static int UseMergedOut(UnreadHost value, bool choose) => 0;
                public static int Use64(UnreadHost value) { Producer64(); return Ignore(value); }
                public static int Use64Out(UnreadHost value) => 0;
                public static int UseText(UnreadHost value) { ProducerText(); return Ignore(value); }
                public static int UseTextOut(UnreadHost value) => 0;
                public static int UseData(UnreadData value) { Producer(); return IgnoreData(value); }
                public static int UseDataOut(UnreadData value) => 0;
                public static int Checked(UnreadHost value) { Producer(); return value.IgnoreThis(); }
                public static int CheckedOut(UnreadHost value) => 0;
                public static int CheckedFinal(UnreadHost value) { Producer(); return value.FinalThis(); }
                public static int CheckedFinalOut(UnreadHost value) => 0;
                public int Own() { Producer(); return IgnoreThis(); }
                public int OwnOut() => 0;
            }
            """);
        var definitions = primitives.Types.Where(type => type.Assembly == "mscorlib.dll" && type.Name != "BitConverter").ToList();
        var objectIndex = definitions.FindIndex(type => type.Name == "Object"); var originalObject = definitions[objectIndex];
        definitions[objectIndex] = new TypeDef { Index = originalObject.Index, Assembly = originalObject.Assembly, Namespace = originalObject.Namespace,
            Name = originalObject.Name, Token = originalObject.Token, Attributes = originalObject.Attributes, IsValueType = false, IsEnum = false,
            Size = 16, PackingSize = 0, ClassSizeIsDefault = true };
        TypeRef Type(string name) => new DefinitionRef(definitions.Single(type => type.Name == name), []);
        TypeDef Define(string name, bool value = false, string assembly = "UnreadChecks.dll", string ns = "", int size = 16)
        {
            var type = new TypeDef { Index = definitions.Count, Assembly = assembly, Namespace = ns, Name = name,
                Token = (uint)(0x02000001 + definitions.Count), Attributes = TypeAttributes.Public, IsValueType = value,
                IsEnum = false, BaseType = value ? null : Type("Object"), Size = size, PackingSize = 0, ClassSizeIsDefault = true };
            definitions.Add(type); return type;
        }
        var host = Define("UnreadHost"); var other = Define("UnreadOther"); var data = Define("UnreadData", true);
        var large = Define("UnreadLarge", true, size: 24);
        var nullException = Define("NullReferenceException", assembly: "mscorlib.dll", ns: "System");
        data.Fields = [new FieldDef { Index = 0, Owner = data, Name = "First", Type = Type("Int64"), Offset = 0, Attributes = FieldAttributes.Public },
            new FieldDef { Index = 1, Owner = data, Name = "Second", Type = Type("Int64"), Offset = 8, Attributes = FieldAttributes.Public }];
        large.Fields = Enumerable.Range(0, 3).Select(i => new FieldDef { Index = 2 + i, Owner = large, Name = "Part" + i, Type = Type("Int64"), Offset = i * 8, Attributes = FieldAttributes.Public }).ToArray();
        var methods = new List<MethodDef>();
        MethodRef Method(TypeDef owner, string name, bool statics, TypeRef returned, params TypeRef[] arguments)
        {
            var method = new MethodDef { Index = methods.Count, Owner = owner, Name = name, Token = (uint)(0x06000001 + methods.Count),
                Attributes = MethodAttributes.Public | (statics ? MethodAttributes.Static : 0), ImplAttributes = 0, Slot = -1,
                ReturnType = returned, Parameters = arguments.Select((type, i) => new ParameterDef("p" + i, type, 0, null, false)).ToArray() };
            methods.Add(method); owner.Methods = owner.Methods.Append(method).ToArray(); return MethodRef.Open(method);
        }
        var hostType = new DefinitionRef(host, []); var dataType = new DefinitionRef(data, []);
        Method(nullException, ".ctor", false, Type("Void"));
        var producer = Method(host, "Producer", true, Type("Int32"));
        var producer64 = Method(host, "Producer64", true, Type("Int64"));
        var producerText = Method(host, "ProducerText", true, Type("String"));
        var barrier = Method(host, "Barrier", true, Type("Void"));
        var ignore = Method(host, "Ignore", true, Type("Int32"), hostType);
        var ignoreData = Method(host, "IgnoreData", true, Type("Int32"), dataType);
        var ignoreLarge = Method(host, "IgnoreLarge", true, Type("Int32"), new DefinitionRef(large, []));
        var ignoreRef = Method(host, "IgnoreRef", true, Type("Int32"), new ByRefRef(hostType));
        var ignoreThis = Method(host, "IgnoreThis", false, Type("Int32"));
        var finalThisDefinition = new MethodDef { Index = methods.Count, Owner = host, Name = "FinalThis", Token = (uint)(0x06000001 + methods.Count),
            Attributes = MethodAttributes.Public | MethodAttributes.Virtual | MethodAttributes.Final | MethodAttributes.NewSlot,
            ImplAttributes = 0, Slot = 0, ReturnType = Type("Int32") };
        methods.Add(finalThisDefinition); host.Methods = host.Methods.Append(finalThisDefinition).ToArray();
        var finalThis = MethodRef.Open(finalThisDefinition);
        var valueThis = Method(data, "IgnoreThis", false, Type("Int32"));
        var use = Method(host, "Use", true, Type("Int32"), hostType);
        var useMerged = Method(host, "UseMerged", true, Type("Int32"), hostType, Type("Boolean"));
        var use64 = Method(host, "Use64", true, Type("Int32"), hostType);
        var useText = Method(host, "UseText", true, Type("Int32"), hostType);
        var useData = Method(host, "UseData", true, Type("Int32"), dataType);
        var checkedUse = Method(host, "Checked", true, Type("Int32"), hostType);
        var checkedFinal = Method(host, "CheckedFinal", true, Type("Int32"), hostType);
        var ownUse = Method(host, "Own", false, Type("Int32"));
        var foreign = Method(host, "Foreign", true, Type("Int32"), new DefinitionRef(other, []));
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = data.Fields.Concat(large.Fields).ToArray(),
            RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [], Assemblies = definitions.GroupBy(type => type.Assembly)
                .Select(group => new AssemblyDef { Name = group.Key, AssemblyName = Path.GetFileNameWithoutExtension(group.Key),
                    Version = new(1, 0), Culture = "", PublicKey = [], Types = group.ToArray() }).ToArray() };
        var spec = InputCorpusChecks.Spec("arm64-v8a"); var layouts = new FieldLayouts(spec, 8, 8);
        var types = new ManagedTypes(program, layouts, 8); var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var runtime = new ParameterRuntimeMap(catalog.Functions.First(function => function.Operation.Name == "ThrowNullReference"));
        var map = new ParameterReadMap(new() { [10] = [producer], [20] = [ignore], [30] = [barrier] });
        var calls = new CallNamingQuery(binder, map, runtime, catalog);
        NativeFunction Function(string mode, MethodRef method)
        {
            var terms = new TermTable(); var entry = new BlockIdentity(); var left = new BlockIdentity(); var right = new BlockIdentity(); var join = new BlockIdentity();
            var frame = terms.Atom(new RootAtom(AddressRoot.Frame), 64);
            var builder = new FunctionBuilder(terms, entry, 64, new(frame)) { IncomingArgumentArea = frame };
            Term Input(int i) => terms.Atom(new EntryAtom(new(SlotKind.Integer, i)), 64);
            for (int i = mode == "missing" ? 1 : 0; i < 8; i++) builder.Inputs.Add(new(new(SlotKind.Integer, i), Input(i)));
            var body = new List<Statement>(); var used = Input(0); Term returned = terms.Constant(7, 64);
            if (mode == "saved")
            {
                var saved = terms.Atom(new CallerValue(0), 64); var address = terms.Apply(new CoreOperator(CoreOperation.Add), 64, frame, terms.Constant(ulong.MaxValue - 7, 64));
                var id = new ReadIdentity(); body.Add(new MemoryWrite(new(), address, 64, saved));
                body.Add(new MemoryRead(id, address, 64, terms.Atom(new ResultAtom(id), 64)));
            }
            if (mode == "store") body.Add(new MemoryWrite(new(), frame, 64, used));
            if (mode == "passed")
            {
                var id = new CallIdentity();
                body.Add(new Call(id, new ImageFunction(20),
                    [new(new(SlotKind.Integer), used), new(new(SlotKind.Integer, 1), terms.Constant(0, 64))],
                    [new(new(SlotKind.Integer), terms.Atom(new ResultAtom(id), 64))]));
            }
            if (mode is "merge" or "dead-merge")
            {
                var merge = new MergeIdentity(); var result = terms.Atom(new ResultAtom(merge), 64);
                builder.Blocks.Add(new(entry, [], [], new Branch(terms.Slice(Input(1), 0, 1), left, right)));
                builder.Blocks.Add(new(left, [], [], new Jump(join))); builder.Blocks.Add(new(right, [], [], new Jump(join)));
                builder.Blocks.Add(new(join, [new(merge, result, [new(left, used), new(right, terms.Constant(0, 64))])], [],
                    new Return([new(new(SlotKind.Integer), mode == "merge" ? result : returned)])));
                return builder.Freeze();
            }
            if (mode == "read") returned = used;
            builder.Blocks.Add(new(entry, [], [.. body], new Return([new(new(SlotKind.Integer), returned)])));
            return builder.Freeze();
        }
        Outcome<ParameterReads> Prove(MethodRef target, string mode = "unused") => ParameterReads.Prove(Function(mode, target),
            binder.Entry(target, BindingEntryKind.Ordinary).Value!, binder, calls, new(new ManagedCallEffects(calls)));
        foreach (var (mode, expected) in new[] { ("unused", false), ("saved", false), ("passed", true), ("merge", true), ("dead-merge", false), ("store", true), ("read", true) })
        {
            var fact = Prove(ignore, mode);
            checks.True(fact.IsSuccess && fact.Value.Parameters[0].IsRead == expected, "形参读取证明 " + mode + "：" + fact.Why);
        }
        var savedBody = Function("saved", ignore); var savedState = new StateQueries();
        var restored = savedState.CreateContext(savedBody).Get(savedState.Read, savedBody.Blocks.SelectMany(block => block.Statements).OfType<MemoryRead>().Single().Identity);
        checks.True(restored is { IsSuccess: true, Value.Identity: CallerValue }, "保存槽只恢复同一个调用方的值");
        checks.True(!Prove(ignore, "missing").IsSuccess, "形参绑定失败不建立未读事实");
        var largeSignature = binder.Entry(ignoreLarge, BindingEntryKind.Ordinary).Value!;
        checks.True(largeSignature.Parameters[0].CopyAddress is not null, "大结构体按地址绑定");
        checks.True(Prove(ignoreLarge) is { IsSuccess: true, Value.Parameters: [{ IsRead: false }] }
            && Prove(ignoreLarge, "store") is { IsSuccess: true, Value.Parameters: [{ IsRead: true }] }, "间接结构体的地址槽参与未读证明");
        var receiverFact = Prove(ignoreThis);
        checks.True(receiverFact is { IsSuccess: true, Value.This.IsRead: false }, "接收者独立于隐藏的方法信息绑定");
        using var skeleton = new UnreadSkeleton(new Skeleton(program, 16));
        var emitter = new BodyEmitter(skeleton.Value, types);
        foreach (var mode in new[] { "default", "merge", "int-reference", "reference-local", "data", "checked", "final-checked", "own", "read", "byref", "value-receiver", "static", "barrier", "multiple", "indirect", "valid", "argument", "proof-failure" })
        {
            var caller = mode switch { "merge" => useMerged, "int-reference" => use64, "reference-local" => useText, "data" => useData, "own" => ownUse, "argument" => foreign, _ => use };
            if (mode == "checked" || mode == "final-checked" || mode == "barrier") caller = mode == "final-checked" ? checkedFinal : checkedUse;
            var target = mode switch { "data" => ignoreData, "byref" => ignoreRef, "value-receiver" => valueThis,
                "final-checked" => finalThis, "checked" or "own" or "static" or "barrier" => ignoreThis, _ => ignore };
            var localMap = new ParameterReadMap(new() { [10] = [mode == "int-reference" ? producer64 : mode == "reference-local" ? producerText : producer], [20] = mode == "multiple" ? [target, ignoreThis] : [target], [30] = [barrier] });
            var named = new CallNamingQuery(binder, localMap, runtime, catalog);
            var t = new TermTable(); var entry = new BlockIdentity(); var pass = new BlockIdentity(); var fail = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var f = new FunctionBuilder(t, entry, 64, new(frame));
            Term Input(int i) => t.Atom(new EntryAtom(new(SlotKind.Integer, i)), 64);
            for (int i = 0; i < 8; i++) f.Inputs.Add(new(new(SlotKind.Integer, i), Input(i)));
            var statements = new List<Statement>(); var callBlock = entry; ImmutableArray<Merge> callMerges = [];
            var produced = new CallIdentity(); var residue = t.Atom(new ResultAtom(produced), 64);
            statements.Add(new Call(produced, new ImageFunction(10), [new(new(SlotKind.Integer), t.Constant(0, 64))], [new(new(SlotKind.Integer), residue)]));
            if (mode is "checked" or "final-checked" or "barrier")
            {
                f.Blocks.Add(new(entry, [], [.. statements], new Branch(t.Apply(new CoreOperator(CoreOperation.Equal), 1, Input(0), t.Constant(0, 64)), fail, pass)));
                f.Blocks.Add(new(fail, [], [new Call(new(), new ImageFunction(1), [], [], true)], new Unreachable()));
                statements.Clear(); callBlock = pass;
                if (mode == "barrier")
                {
                    var id = new CallIdentity(); residue = t.Atom(new ResultAtom(id), 64);
                    statements.Add(new Call(id, new ImageFunction(30), [new(new(SlotKind.Integer), t.Constant(0, 64))], [new(new(SlotKind.Integer), residue)]));
                }
            }
            if (mode == "merge")
            {
                var join = new BlockIdentity(); var id = new MergeIdentity(); var merged = t.Atom(new ResultAtom(id), 64);
                f.Blocks.Add(new(entry, [], [.. statements], new Branch(t.Slice(Input(1), 0, 1), pass, fail)));
                f.Blocks.Add(new(pass, [], [], new Jump(join))); f.Blocks.Add(new(fail, [], [], new Jump(join)));
                callMerges = [new(id, merged, [new(pass, Input(0)), new(fail, residue)])];
                statements.Clear(); callBlock = join; residue = merged;
            }
            var idCall = new CallIdentity(); var result = t.Atom(new ResultAtom(idCall), 64);
            var args = Enumerable.Range(0, 8).Select(i => new SlotValue(new(SlotKind.Integer, i), i == 0
                ? mode is "valid" or "argument" ? Input(0) : residue : t.Constant(0, 64))).ToImmutableArray();
            statements.Add(new Call(idCall, mode == "indirect" ? new ComputedTarget(t.Constant(20, 64)) : new ImageFunction(20), args, [new(new(SlotKind.Integer), result)]));
            f.Blocks.Add(new(callBlock, callMerges, [.. statements], new Return([new(new(SlotKind.Integer), result)])));
            var facts = new ParameterReadSource(method => mode == "proof-failure"
                ? Outcome<ParameterReads>.Failure(new("binding.parameter-reads.lift", "测试提升失败")) : Prove(method, mode == "read" ? "read" : "unused"));
            var lowered = new IntegerLowering(f.Freeze(), caller, binder, types, calls: named, effects: new ManagedCallEffects(named), spec: spec, parameterReads: facts).Run();
            bool success = mode is "default" or "merge" or "int-reference" or "reference-local" or "data" or "checked" or "final-checked" or "own" or "valid" or "argument";
            checks.True((lowered.Body is not null) == success, "未读实参下降 " + mode + "：" + lowered.Failure);
            checks.True(mode == "valid" ? facts.Requests == 0 : mode is "multiple" or "indirect" or "byref" or "value-receiver" || facts.Requests > 0,
                "只在失败后查询未读事实 " + mode);
            if (mode == "read") checks.True(lowered.Failure?.Reason.Cause?.Message.Contains("形参被读", StringComparison.Ordinal) == true, "被读原因接在原洞后");
            if (lowered.Body is not { } body) continue;
            var invocation = body.Blocks.SelectMany(block => block.Statements).OfType<ManagedCall>().Single(call => call.Invocation.Method.Method == target.Method).Invocation;
            if (mode is "default" or "merge" or "int-reference" or "reference-local" or "argument") checks.True(invocation.Arguments is [ConstantValue { Bits: 0 }], "普通形参写同类型默认值");
            if (mode == "data") checks.True(invocation.Arguments is [ComposedValue { Leaves.Count: 0 }], "结构体形参写 default(T)");
            if (mode is "checked" or "final-checked") checks.True(invocation.Virtual && body.Blocks.SelectMany(block => block.Statements).OfType<ManagedBranch>().Count() == 0, "显式判空由接收者 callvirt 吸收");
            if (mode == "own") checks.True(invocation.Receiver is ArgumentValue { Index: -1 }, "无判空时使用调用方 this");
            if (mode is not ("default" or "merge" or "int-reference" or "reference-local" or "data" or "checked" or "final-checked" or "own")) continue;
            checks.True(emitter.Emit([body]).Count == 0, "未读实参通过输出校验 " + mode);
            string originalName = mode switch { "default" => "Use", "merge" => "UseMerged", "int-reference" => "Use64", "reference-local" => "UseText", "data" => "UseData", "checked" => "Checked", "final-checked" => "CheckedFinal", _ => "Own" };
            var tested = reference.Method("UnreadHost", originalName + "Out"); tested.Body = skeleton.Value.Method(caller.Method).Body;
            Mono.Cecil.TypeReference MapType(Mono.Cecil.TypeReference type) => type is Mono.Cecil.ByReferenceType byref
                ? new Mono.Cecil.ByReferenceType(MapType(byref.ElementType))
                : reference.Module.GetType(type.FullName) ?? reference.Module.TypeSystem.Object.Resolve().Module.GetType(type.FullName) ?? type;
            foreach (var instruction in tested.Body.Instructions) instruction.Operand = instruction.Operand switch
            {
                Mono.Cecil.MethodReference method when method.DeclaringType.FullName == "System.NullReferenceException" => reference.Module.ImportReference(typeof(NullReferenceException).GetConstructor(System.Type.EmptyTypes)!),
                Mono.Cecil.MethodReference method => reference.Method(method.DeclaringType.Name, method.Name),
                Mono.Cecil.TypeReference type => MapType(type),
                Mono.Cecil.ParameterDefinition parameter => tested.Parameters[parameter.Index], _ => instruction.Operand,
            };
            foreach (var local in tested.Body.Variables) local.VariableType = MapType(local.VariableType);
            var comparison = CilComparison.Compare(reference.Method("UnreadHost", originalName), tested);
            checks.True(comparison.Status == CilComparisonStatus.Match && comparison.CompletedCases == 32, "未读实参 32 个输入执行对照 " + mode + "：" + comparison.Reason);
            if (mode is "checked" or "final-checked")
            {
                var model = new CecilModel(reference.Module); var index = new WorldIndex(model.Program, new ManagedTypes(model.Program, new ManagedStorage(model.Prepare), 8));
                var interpreter = new CilInterpreter(model, index) { BodyModule = reference.Module };
                foreach (bool isNull in new[] { true, false })
                {
                    var testedTarget = model.Method(tested); var world = new World(index, 0, new Hints([], []), testedTarget.DeclaringType);
                    var value = isNull ? 0 : world.Instance(new DefinitionRef(model.Program.Types.Single(type => type.Name == "UnreadHost"), []), "value", 0);
                    var arguments = new[] { StackValue.O(value) };
                    var left = interpreter.Run(world, reference.Method("UnreadHost", originalName), model.Method(reference.Method("UnreadHost", originalName)), arguments);
                    var right = interpreter.Run(world, tested, testedTarget, arguments);
                    checks.True(Execution.Trace.Difference(world, left, right) is null, "未读接收者的显式输入对照 " + mode + " null=" + isNull);
                    checks.True(isNull ? right.Events.Any(e => e.Text.StartsWith("throw System.NullReferenceException ", StringComparison.Ordinal))
                        : right.Result?.StartsWith("return ", StringComparison.Ordinal) == true, "未读接收者空输入仍抛空引用异常 " + mode + " null=" + isNull);
                }
            }
        }
    }
    private sealed class UnreadSkeleton(Skeleton value) : IDisposable
    {
        public Skeleton Value => value;
        public void Dispose() { foreach (var assembly in value.Assemblies) assembly.Dispose(); }
    }
}
