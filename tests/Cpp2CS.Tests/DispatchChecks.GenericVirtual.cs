using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Dispatch;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Tests;

internal static partial class DispatchChecks
{
    private static void GenericVirtualCases(Assertions checks, RuntimeSpec spec)
    {
        var layouts = new FieldLayouts(spec, 8, 8); var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(), catalog);
        var integer = new DefinitionRef(new TypeDef { Index = 0, Assembly = "mscorlib.dll", Namespace = "System", Name = "Int32", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false }, []);
        var owner = new TypeDef { Index = 1, Assembly = "test", Namespace = "", Name = "VirtualOwner", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false, PackingSize = 0, ClassSizeIsDefault = true, Size = 16 };
        var parameter = new GenericParameterDef { Name = "U", Position = 0, Attributes = 0 };
        var generic = new GenericParameterRef("U", true, 0) { Parameter = parameter };
        var method = new MethodDef { Index = 0, Owner = owner, Name = "Apply", Token = 0, Attributes = MethodAttributes.Public | MethodAttributes.Virtual,
            ImplAttributes = 0, Slot = 3, ReturnType = generic, Parameters = [new("value", generic, 0, null, false)], GenericParameters = [parameter] };
        owner.Methods = [method]; var instance = new MethodRef(method, [], [integer]);
        foreach (var mode in new[] { "Dynamic", "Constant", "OtherReceiver", "WrongInformation", "OtherUse", "EscapedPointer", "Intervening", "WrongSlot", "NoMethod", "SecondCall" })
        {
            var t = new TermTable(); var entry = new BlockIdentity(); var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            var f = new FunctionBuilder(t, entry, 64, new(frame)) { ImageBase = image };
            Term Input(int i) { var slot = new AbstractSlot(SlotKind.Integer, i); var value = t.Atom(new EntryAtom(slot), 64); f.Inputs.Add(new(slot, value)); return value; }
            var receiver = Input(0); var argument = Input(1); var other = mode == "OtherReceiver" ? Input(2) : receiver;
            var statements = new List<Statement>();
            Term Add(Term root, long offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, root, t.Constant(offset, 64));
            Term Read(Term address, int width = 64)
            { var id = new ReadIdentity(); var result = t.Atom(new ResultAtom(id), width); statements.Add(new MemoryRead(id, address, width, result)); return result; }
            var information = Read(Add(image, 128)); var klass = Read(Add(receiver, spec.Layout.Field("Il2CppObject", "klass").ByteOffset));
            var slot = mode == "Dynamic" ? Read(Add(information, spec.Layout.Field("MethodInfo", "slot").ByteOffset), 16)
                : t.Constant(method.Slot + (mode == "WrongSlot" ? 1 : 0), 16);
            var index = t.Apply(new CoreOperator(CoreOperation.Multiply), 64, t.Apply(new CoreOperator(CoreOperation.ZeroExtend), 64, slot), t.Constant(spec.Layout.VtableSlotSize, 64));
            var definition = Read(Add(t.Apply(new CoreOperator(CoreOperation.Add), 64, klass, index), spec.Layout.VtableStart + spec.Layout.Field("VirtualInvokeData", "method").ByteOffset));
            var runtime = catalog.Functions.Single(fn => fn.Operation.Name == "ResolveGenericVirtual");
            var resolveId = new CallIdentity(); var resolved = t.Atom(new ResultAtom(resolveId), 64);
            statements.Add(new Call(resolveId, new NamedFunction(runtime.MangledName), [new(new(SlotKind.Integer), definition), new(new(SlotKind.Integer, 1), information)], [new(new(SlotKind.Integer), resolved)]));
            if (mode == "OtherUse") statements.Add(new MemoryWrite(new(), frame, 64, resolved));
            if (mode == "Intervening") statements.Add(new Call(new(), new ImageFunction(999), [], []));
            var pointer = Read(Add(resolved, spec.Layout.Field("MethodInfo", "virtualMethodPointer").ByteOffset));
            var id = new CallIdentity(); var returned = t.Atom(new ResultAtom(id), 64);
            var indirect = new Call(id, new ComputedTarget(pointer), [new(new(SlotKind.Integer), other), new(new(SlotKind.Integer, 1), argument),
                new(new(SlotKind.Integer, 2), mode == "WrongInformation" ? information : resolved)], [new(new(SlotKind.Integer), returned)]);
            statements.Add(indirect);
            if (mode == "SecondCall") statements.Add(indirect with { Identity = new(), Results = [] });
            f.Blocks.Add(new(entry, [], [.. statements], new Return([new(new(SlotKind.Integer), mode == "EscapedPointer" ? pointer : returned)])));
            var caller = new MethodRef(new MethodDef { Index = 1, Owner = owner, Name = "Caller", Token = 0, Attributes = MethodAttributes.Static, ImplAttributes = 0, Slot = -1,
                ReturnType = integer, Parameters = mode == "OtherReceiver" ? [new("self", new DefinitionRef(owner, []), 0, null, false), new("value", integer, 0, null, false), new("other", new DefinitionRef(owner, []), 0, null, false)]
                    : [new("self", new DefinitionRef(owner, []), 0, null, false), new("value", integer, 0, null, false)] }, [], []);
            var facts = mode == "NoMethod" ? NamingFacts.Empty : NamingFacts.Empty with { Slots = ImmutableDictionary<ulong, Outcome<MetadataEntity>>.Empty.Add(128, Outcome<MetadataEntity>.Success(new MethodEntity(instance))) };
            var state = new StateQueries(); var names = new ValueNamingQuery(state, calls, facts, spec, binder, binder.Entry(caller, BindingEntryKind.Ordinary).Value);
            var locations = new ManagedLocationQuery(state, names, layouts, spec); var dispatch = new DispatchQuery(state, calls, names, locations, binder, spec);
            var result = locations.CreateContext(f.Freeze()).Get(dispatch, id);
            bool accepted = mode is "Dynamic" or "Constant";
            checks.True(result.IsSuccess && (result.Value.Kind != DispatchKind.Unresolved) == accepted, mode + " 泛型虚解析正反例：" + (result.IsSuccess ? result.Value.Why : result.Why));
            if (accepted) checks.True(result.Value.Method == instance && result.Value.Receiver == receiver && result.Value.GenericResolution == resolveId,
                "泛型虚调用保留方法实例、同一对象及解析身份");
        }
    }
}
