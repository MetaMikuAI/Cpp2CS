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
    private static void DelegateChecks(Assertions checks, ProgramModel primitives)
    {
        using var source = new CompiledSource("""
            public interface IReceiver { int Apply(int x); }
            public class Receiver : IReceiver {
                public int Instance(int x) => x + 2;
                public static int Static(int x) => x + 5;
                public virtual int Virtual(int x) => x + 3;
                public virtual int Apply(int x) => x + 4;
                private int Hidden(int x) => x;
            }
            public class DerivedReceiver : Receiver { public override int Virtual(int x) => x + 30; public override int Apply(int x) => x + 40; }
            public delegate int Callback(int x);
            public static class DelegateCases {
                public static int Bound(this Receiver receiver, int x) => x + 7;
                public static int Instance(Receiver r, Receiver other, int x) => new Callback(r.Instance)(x);
                public static int Static(Receiver r, Receiver other, int x) => new Callback(Receiver.Static)(x);
                public static int Bound(Receiver r, Receiver other, int x) => new Callback(r.Bound)(x);
                public static int Virtual(Receiver r, Receiver other, int x) => new Callback(r.Virtual)(x);
                public static int Interface(IReceiver r, IReceiver other, int x) => new Callback(r.Apply)(x);
                public static int Output(Receiver r, Receiver other, int x) => 0;
                public static int InterfaceOutput(IReceiver r, IReceiver other, int x) => 0;
            }
            """);
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").ToList();
        TypeRef Type(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        TypeDef Define(string name, string assembly = "DelegateChecks.dll", string ns = "", TypeRef? parent = null, bool itf = false)
        {
            var d = new TypeDef { Index = definitions.Count, Assembly = assembly, Namespace = ns, Name = name,
                Token = (uint)(0x02000001 + definitions.Count), Attributes = TypeAttributes.Public | (itf ? TypeAttributes.Interface | TypeAttributes.Abstract : 0),
                IsValueType = false, IsEnum = false, BaseType = parent ?? Type("Object") }; definitions.Add(d); return d;
        }
        var multicast = Define("MulticastDelegate", "mscorlib.dll", "System");
        var callback = Define("Callback", parent: new DefinitionRef(multicast, []));
        var holder = Define("Receiver"); var contract = Define("IReceiver", itf: true); var owner = Define("DelegateCases"); var plain = Define("Plain");
        var methods = new List<MethodDef>();
        MethodDef Method(TypeDef type, string name, TypeRef result, TypeRef[] parameters, bool statics = false, int slot = -1, bool hidden = false)
        {
            var m = new MethodDef { Index = methods.Count, Owner = type, Name = name, Token = (uint)(0x06000001 + methods.Count),
                Attributes = (hidden ? MethodAttributes.Private : MethodAttributes.Public) | (statics ? MethodAttributes.Static : 0)
                    | (slot >= 0 ? MethodAttributes.Virtual | MethodAttributes.NewSlot : 0)
                    | (name == ".ctor" ? MethodAttributes.SpecialName | MethodAttributes.RTSpecialName : 0),
                ImplAttributes = type == callback ? MethodImplAttributes.Runtime : 0, Slot = slot, ReturnType = result,
                Parameters = parameters.Select((p, i) => new ParameterDef("p" + i, p, 0, null, false)).ToArray() };
            methods.Add(m); type.Methods = type.Methods.Append(m).ToArray(); return m;
        }
        var ctor = Method(callback, ".ctor", Type("Void"), [Type("Object"), Type("IntPtr")]);
        var invoke = Method(callback, "Invoke", Type("Int32"), [Type("Int32")]);
        var nonstandardCtor = Method(callback, ".ctor", Type("Void"), [Type("Object"), Type("Int64")]);
        var ordinaryCtor = Method(plain, ".ctor", Type("Void"), [Type("Object"), Type("IntPtr")]);
        var instance = Method(holder, "Instance", Type("Int32"), [Type("Int32")]);
        var statics = Method(holder, "Static", Type("Int32"), [Type("Int32")], true);
        var bound = Method(owner, "Bound", Type("Int32"), [Type("Receiver"), Type("Int32")], true);
        var virtualMethod = Method(holder, "Virtual", Type("Int32"), [Type("Int32")], slot: 3);
        var interfaceMethod = Method(contract, "Apply", Type("Int32"), [Type("Int32")], slot: 0);
        var hidden = Method(holder, "Hidden", Type("Int32"), [Type("Int32")], hidden: true);
        string[] modes = ["Instance", "Static", "Bound", "Virtual", "Interface", "VirtualCall", "InterfaceCall", "Mismatch", "NotDelegate", "OrdinaryArgument", "Inaccessible", "UnknownSlot", "LookupUnused", "LookupIntervening", "LookupBetween", "Nonstandard", "UnverifiedVirtual"];
        var callers = modes.ToDictionary(mode => mode, mode => Method(owner, mode, Type("Int32"),
            [Type(mode.StartsWith("Interface", StringComparison.Ordinal) ? "IReceiver" : "Receiver"), Type(mode.StartsWith("Interface", StringComparison.Ordinal) ? "IReceiver" : "Receiver"), Type("Int32")], true));
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = [], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(d => d.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var spec = InputCorpusChecks.Spec("arm64-v8a"); var layouts = new FieldLayouts(spec, 8, 8); var types = new ManagedTypes(program, layouts, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64()); var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var calls = new CallNamingQuery(binder, new ReferenceCodeMap(ctor, invoke, ordinaryCtor, statics, nonstandardCtor), new NamingChecks.RuntimeMap(), catalog);
        var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        foreach (var mode in modes)
        {
            var t = new TermTable(); var entry = new BlockIdentity(); var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            var f = new FunctionBuilder(t, entry, 64, new(frame)) { ImageBase = image };
            Term Input(int n) { var slot = new AbstractSlot(SlotKind.Integer, n); var term = t.Atom(new EntryAtom(slot), 64); f.Inputs.Add(new(slot, term)); return term; }
            var receiver = Input(0); var other = Input(1); var argument = Input(2); var statements = new List<Statement>(); var facts = NamingFacts.Empty;
            Term Add(Term root, long offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, root, t.Constant(offset, 64));
            Term Read(Term address, int width = 64) { var id = new ReadIdentity(); var term = t.Atom(new ResultAtom(id), width); statements.Add(new MemoryRead(id, address, width, term)); return term; }
            Term Entity(ulong offset, MetadataEntity entity) { facts = facts with { Slots = facts.Slots.SetItem(offset, Outcome<MetadataEntity>.Success(entity)) }; return Read(Add(image, (long)offset)); }
            Term Runtime(string operation, params Term[] args)
            {
                var function = catalog.Functions.First(fn => fn.Operation.Name == operation && fn.Signature is not null); var id = new CallIdentity(); var result = t.Atom(new ResultAtom(id), 64);
                statements.Add(new Call(id, new NamedFunction(function.MangledName), args.Select((v, i) => new SlotValue(new(SlotKind.Integer, i), v)).ToImmutableArray(), [new(new(SlotKind.Integer), result)])); return result;
            }
            Term Managed(ulong address, params Term[] args)
            {
                var id = new CallIdentity(); var result = t.Atom(new ResultAtom(id), 64);
                statements.Add(new Call(id, new ImageFunction(address), args.Select((v, i) => new SlotValue(new(SlotKind.Integer, i), v)).ToImmutableArray(), address is 10 or 12 ? [] : [new(new(SlotKind.Integer), result)])); return result;
            }
            var target = mode == "Static" ? t.Constant(0, 64) : receiver;
            var selected = mode switch { "Static" or "OrdinaryArgument" => statics, "Bound" => bound, "Inaccessible" => hidden, "UnverifiedVirtual" => virtualMethod, _ => instance };
            Term information;
            if (mode.StartsWith("Interface", StringComparison.Ordinal))
            {
                var itf = Entity(144, new ClassEntity(Type("IReceiver")));
                information = mode == "InterfaceCall" ? Runtime("LookupInterfaceMethod", receiver, t.Constant(0, 64), itf)
                    : Read(Add(Runtime("LookupInterfaceData", receiver, itf, t.Constant(0, 64)), spec.Layout.Field("VirtualInvokeData", "method").ByteOffset));
            }
            else if (mode is "Virtual" or "VirtualCall" or "Mismatch" or "UnknownSlot" or "LookupUnused" or "LookupIntervening")
            {
                var obj = mode == "Mismatch" ? other : receiver;
                information = mode is "VirtualCall" or "LookupUnused" or "LookupIntervening" ? Runtime("LookupVirtualMethod", obj, t.Constant(3, 64))
                    : Read(Add(Read(obj), spec.Layout.VtableStart + (mode == "UnknownSlot" ? 99 : 3) * spec.Layout.VtableSlotSize + spec.Layout.Field("VirtualInvokeData", "method").ByteOffset));
            }
            else information = Entity(136, new MethodEntity(MethodRef.Open(selected)));
            if (mode == "LookupIntervening") Managed(13, t.Constant(2, 64), t.Constant(0, 64));
            if (mode == "LookupUnused") information = Entity(136, new MethodEntity(MethodRef.Open(instance)));
            var klass = Entity(128, new ClassEntity(Type(mode is "NotDelegate" or "OrdinaryArgument" ? "Plain" : "Callback")));
            var allocated = Runtime("AllocateObject", klass);
            if (mode == "LookupBetween") information = Runtime("LookupVirtualMethod", receiver, t.Constant(3, 64));
            Managed(mode is "NotDelegate" or "OrdinaryArgument" ? 12UL : mode == "Nonstandard" ? 14UL : 10UL, allocated, target, information, t.Constant(0, 64));
            var returned = mode is "NotDelegate" or "OrdinaryArgument" ? t.Constant(0, 64) : Managed(11, allocated, argument, t.Constant(0, 64));
            f.Blocks.Add(new(entry, [], [.. statements], new Return([new(new(SlotKind.Integer), returned)])));
            var input = f.Freeze(); checks.True(ExitChecker.Check(input).IsValid, mode + " 委托输入契约");
            var lowered = new IntegerLowering(input, MethodRef.Open(callers[mode]), binder, types, calls: calls, effects: new ManagedCallEffects(calls), spec: spec, names: facts).Run();
            if (mode is "Mismatch" or "NotDelegate" or "OrdinaryArgument" or "Inaccessible" or "UnknownSlot" or "LookupUnused" or "LookupIntervening" or "LookupBetween" or "Nonstandard" or "UnverifiedVirtual")
            {
                checks.True(lowered.Body is null, mode + " 保持洞：" + lowered.Failure);
                if (mode == "Mismatch") checks.True(lowered.Failure?.Reason.Code == "lowering.Delegate.Receiver", "虚表对象与目标不同有明确原因");
                if (mode == "Inaccessible") checks.True(lowered.Failure?.Reason.Code == "lowering.Access.Method", "不可访问的委托方法在恢复层拒绝");
                if (mode == "UnverifiedVirtual")
                {
                    checks.True(lowered.Failure?.Reason.Code == "lowering.Delegate.DirectBinding", "直接虚方法绑定的验证失败在恢复层报洞");
                    var local = new LocalValue(new(), Type("Callback"), 64);
                    var invalid = new ManagedBody(MethodRef.Open(callers[mode]), [new ManagedBlock(0, [
                        new ManagedAssignment(0, local, new DelegateValue((DefinitionRef)Type("Callback"), new ArgumentValue(0, Type("Receiver"), 64), MethodRef.Open(virtualMethod), DelegateBinding.ClosedInstance, 64)),
                        new ManagedReturn(0, new ConstantValue(0, Type("Int32"), 32))])]);
                    checks.True(emitter.Emit([invalid]).Values.Any(p => p.Message == "委托 直接虚方法绑定的验证条件未证明"), "输出仍以同一条件拒绝直接虚方法绑定");
                }
                continue;
            }
            checks.True(lowered.Body is not null, mode + " 委托下降：" + lowered.Failure); if (lowered.Body is not { } body) continue;
            var delegated = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().Select(a => a.Value).OfType<DelegateValue>().Single();
            checks.True(delegated.Binding == (mode is "Static" or "Bound" ? DelegateBinding.Static : mode == "Instance" ? DelegateBinding.ClosedInstance : DelegateBinding.VirtualInstance), mode + " 绑定种类");
            checks.True(emitter.Emit([body]).Count == 0, mode + " 委托输出校验");
            var tested = source.Method("DelegateCases", mode.StartsWith("Interface", StringComparison.Ordinal) ? "InterfaceOutput" : "Output"); tested.Body = skeleton.Method(callers[mode]).Body;
            var core = source.Module.TypeSystem.Object.Resolve().Module;
            Mono.Cecil.TypeReference MapType(Mono.Cecil.TypeReference type) => source.Module.ImportReference(source.Module.GetType(type.FullName) ?? core.GetType(type.FullName));
            foreach (var local in tested.Body.Variables) local.VariableType = MapType(local.VariableType);
            foreach (var instruction in tested.Body.Instructions) instruction.Operand = instruction.Operand switch {
                Mono.Cecil.MethodReference method => source.Module.ImportReference(source.Module.GetType(method.DeclaringType.FullName).Methods.Single(m => m.FullName == method.FullName)),
                Mono.Cecil.TypeReference type => MapType(type), Mono.Cecil.ParameterDefinition parameter => tested.Parameters[parameter.Index], _ => instruction.Operand };
            var reference = source.Module.GetType("DelegateCases").Methods.Single(m => m.Name == mode.Replace("Call", "", StringComparison.Ordinal) && m.Parameters.Count == 3);
            using var imageBytes = new MemoryStream(); source.Module.Write(imageBytes);
            var loaded = System.Reflection.Assembly.Load(imageBytes.ToArray());
            var runtimeCases = loaded.GetType("DelegateCases")!;
            var runtimeReference = runtimeCases.GetMethods().Single(m => m.Name == reference.Name && m.GetParameters().Length == 3);
            var runtimeOutput = runtimeCases.GetMethod(tested.Name)!;
            object? Execute(System.Reflection.MethodInfo method, object? receiver, int argument)
            {
                try { return method.Invoke(null, [receiver, receiver, argument]); }
                catch (TargetInvocationException error) when (error.InnerException is not null) { return error.InnerException.GetType().FullName; }
            }
            foreach (var receiverValue in new[] { null, Activator.CreateInstance(loaded.GetType("Receiver")!), Activator.CreateInstance(loaded.GetType("DerivedReceiver")!) })
                foreach (int number in new[] { -7, 0, 11 })
                {
                    // 非虚实例方法组的独立判空不属于此处手工原生输入；其余情形包含空输入。
                    if (mode == "Instance" && receiverValue is null) continue;
                    checks.True(Equals(Execute(runtimeReference, receiverValue, number), Execute(runtimeOutput, receiverValue, number)), mode + " CLR 创建后调用，与参考一致");
                }
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
}
