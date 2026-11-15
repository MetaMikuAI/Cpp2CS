using System.Collections.Immutable;
using System.Reflection;
using System.Runtime.Loader;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Output;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Exceptions;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Structure;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Tests.Execution;

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    private sealed class ProtectedInitializationRuntime(RuntimeFunction initialize) : IRuntimeFunctionMap
    {
        public RuntimeFunction? Find(CallTarget target) => target is ImageFunction { EntryOffset: 20 } ? initialize : null;
    }
    private static void ProtectedInitializationExecution(Assertions checks, ProgramModel primitives)
    {
        using var source = new CompiledSource("""
            public static class Control { public static bool Fail; public static int Count; }
            public static class Owner {
                static Owner() { Control.Count++; if(Control.Fail) throw new System.Exception(); }
                public static int Use() { Control.Count+=10; return 11; }
            }
            public static class Cases {
                public static int Reference() {
                    try { System.Runtime.CompilerServices.RuntimeHelpers.RunClassConstructor(typeof(Owner).TypeHandle); return Owner.Use(); }
                    catch { return 7; }
                }
                public static int Output() => 0;
            }
            """);
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").ToList();
        TypeRef Type(string name) => new DefinitionRef(definitions.Single(d => d.Name == name), []);
        TypeDef Define(string name)
        {
            var result = new TypeDef { Index = definitions.Count, Assembly = "Initialization.dll", Namespace = "", Name = name,
                Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false, BaseType = Type("Object") };
            definitions.Add(result); return result;
        }
        var owner = Define("Owner"); var caller = Define("Cases");
        var initializer = new MethodDef { Index = 0, Owner = owner, Name = ".cctor", Token = 0,
            Attributes = MethodAttributes.Static | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName,
            ImplAttributes = 0, Slot = -1, ReturnType = Type("Void"), Parameters = [] };
        var use = new MethodDef { Index = 1, Owner = owner, Name = "Use", Token = 0,
            Attributes = MethodAttributes.Static | MethodAttributes.Public, ImplAttributes = 0, Slot = -1, ReturnType = Type("Int32"), Parameters = [] };
        var method = new MethodDef { Index = 2, Owner = caller, Name = "Output", Token = 0,
            Attributes = MethodAttributes.Static | MethodAttributes.Public, ImplAttributes = 0, Slot = -1, ReturnType = Type("Int32"), Parameters = [] };
        owner.Methods = [initializer, use]; caller.Methods = [method];
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = [initializer, use, method], Fields = [],
            RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key,
                AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var spec = InputCorpusChecks.Spec("arm64-v8a"); var layouts = new FieldLayouts(spec, 8, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64()); var types = new ManagedTypes(program, layouts, 8);
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var runtime = catalog.Functions.First(f => f.Operation.Name == "InitializeClassPrecise" && f.Signature is not null);
        var calls = new CallNamingQuery(binder, new NamingChecks.Map([new(MethodRef.Open(use), BindingEntryKind.Ordinary)]), new ProtectedInitializationRuntime(runtime), catalog);
        var t = new TermTable(); var entry = new BlockIdentity(); var handler = new BlockIdentity();
        var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
        var slot = new AbstractSlot(SlotKind.Integer); var f = new FunctionBuilder(t, entry, 64, new(frame)) { ImageBase = image };
        var readId = new ReadIdentity(); var klass = t.Atom(new ResultAtom(readId), 64);
        var init = new Call(new(), new ImageFunction(20), [new(slot, klass)], [], Unwind: handler);
        var useId = new CallIdentity(); var returned = t.Atom(new ResultAtom(useId), 64);
        f.Blocks.Add(new(entry, [], [new MemoryRead(readId, t.Apply(new CoreOperator(CoreOperation.Add), 64, image, t.Constant(256, 64)), 64, klass),
            init, new Call(useId, new ImageFunction(10), [new(slot, t.Constant(0, 64))], [new(slot, returned)], Unwind: handler)], new Return([new(slot, t.Slice(returned, 0, 32))])));
        var exception = t.Atom(new ExceptionAtom(handler), 64); var beginId = new CallIdentity(); var payload = t.Atom(new ResultAtom(beginId), 64);
        var capture = new BlockIdentity();
        f.Blocks.Add(new(handler, [], [], new Jump(capture),
            new(exception, t.Atom(new SelectorAtom(handler), 64), [new(ClauseKind.CatchAll, [])])));
        f.Blocks.Add(new(capture, [], [new Call(beginId, new ImportedTarget(new("__cxa_begin_catch")), [new(slot, exception)], [new(slot, payload)]),
            new Call(new(), new ImportedTarget(new("__cxa_end_catch")), [], [])], new Return([new(slot, t.Constant(7, 32))])));
        var names = NamingFacts.Empty with { Slots = ImmutableDictionary<ulong, Outcome<MetadataEntity>>.Empty.Add(256,
            Outcome<MetadataEntity>.Success(new ClassEntity(Type("Owner")))) };
        var state = new StateQueries(new ManagedCallEffects(calls));
        var values = new ValueNamingQuery(state, calls, names, spec, binder, binder.Entry(MethodRef.Open(method), BindingEntryKind.Ordinary).Value, exceptionType: types.Object);
        var locations = new ManagedLocationQuery(state, values, layouts, spec);
        var regions = new ExceptionRegionQuery(state, calls, values, spec, types.Object, nested: true);
        var initialization = new ClassInitializationQuery(state, calls, values, locations, spec, regions);
        var transformed = new UnobservableEffects(state, calls, values, new InputMemoryImage(), new HashSet<AbstractSlot> { slot }, locations, initialization).Run(f.Freeze());
        checks.True(!transformed.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Any(c => c.Identity == init.Identity), "同一区域的静态调用吸收初始化");
        var result = new IntegerLowering(transformed.Function, MethodRef.Open(method), binder, types, calls: calls,
            effects: new ManagedCallEffects(calls), spec: spec, names: names).Run();
        checks.True(result.Body is not null, "受保护初始化吸收后下降：" + result.Failure);
        if (result.Body is null) return;
        var skeleton = new Skeleton(program, 16); var problems = new BodyEmitter(skeleton, types).Emit([result.Body]);
        checks.True(problems.Count == 0, "受保护初始化输出契约");
        if (problems.Count != 0) return;
        var output = source.Method("Cases", "Output"); output.Body = skeleton.Method(method).Body;
        foreach (var instruction in output.Body.Instructions)
            if (instruction.Operand is Mono.Cecil.MethodReference) instruction.Operand = source.Method("Owner", "Use");
        foreach (var clause in output.Body.ExceptionHandlers) clause.CatchType = source.Module.TypeSystem.Object;
        foreach (var local in output.Body.Variables)
            local.VariableType = local.VariableType.FullName == "System.Object" ? source.Module.TypeSystem.Object : source.Module.TypeSystem.Int32;
        checks.True(output.Body.ExceptionHandlers.Count == 1 && output.Body.ExceptionHandlers[0].HandlerType == Mono.Cecil.Cil.ExceptionHandlerType.Catch,
            "吸收后的静态调用仍在 catch 保护内");
        using var bytes = new MemoryStream(); source.Module.Write(bytes);
        foreach (bool fail in new[] { false, true })
        foreach (var name in new[] { "Reference", "Output" })
        {
            var load = new AssemblyLoadContext("初始化执行对照", isCollectible: true);
            using var stream = new MemoryStream(bytes.ToArray()); var assembly = load.LoadFromStream(stream);
            var control = assembly.GetType("Control")!; control.GetField("Fail")!.SetValue(null, fail);
            var returnedValue = (int)assembly.GetType("Cases")!.GetMethod(name)!.Invoke(null, null)!;
            var count = (int)control.GetField("Count")!.GetValue(null)!;
            checks.True(returnedValue == (fail ? 7 : 11) && count == (fail ? 1 : 11),
                name + (fail ? " 初始化抛出被原 catch 接住且未执行访问" : " 正常初始化与访问各执行一次"));
            load.Unload();
        }
    }
}
