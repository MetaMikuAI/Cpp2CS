using System.Reflection;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Tests;

internal static partial class NamingChecks
{
    private static void SharedReferenceLoop(Assertions checks, RuntimeSpec spec)
    {
        var obj = new DefinitionRef(new TypeDef { Index = 0, Assembly = "mscorlib.dll", Namespace = "System", Name = "Object", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false, Size = 16, PackingSize = 0, ClassSizeIsDefault = true }, []);
        var parameter = new GenericParameterDef { Name = "T", Position = 0, Attributes = 0 };
        var node = new TypeDef { Index = 1, Assembly = "test", Namespace = "", Name = "Node`1", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false, Size = 32, PackingSize = 0, ClassSizeIsDefault = true,
            BaseType = obj, GenericParameters = [parameter] };
        var argument = new GenericParameterRef("T", false, 0) { Parameter = parameter };
        var openNode = new DefinitionRef(node, [argument]);
        var next = new MethodDef { Index = 0, Owner = node, Name = "Next", Token = 0, Attributes = MethodAttributes.Public,
            ImplAttributes = 0, Slot = -1, ReturnType = openNode, Parameters = [] };
        var caller = new MethodDef { Index = 1, Owner = node, Name = "Walk", Token = 0, Attributes = MethodAttributes.Static,
            ImplAttributes = 0, Slot = -1, ReturnType = openNode, Parameters = [new("node", openNode, 0, null, false)] };
        node.Methods = [next, caller];
        var definition = MethodRef.Open(caller); var instance = new MethodRef(caller, [obj], []);
        var layouts = new FieldLayouts(spec, 8, 8); var witness = new GenericWitness(definition, instance, layouts);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var calls = new CallNamingQuery(binder, new Map([new(new MethodRef(next, [obj], []), BindingEntryKind.SharedGeneric)]), new RuntimeMap(), catalog);
        var t = new TermTable(); var head = new BlockIdentity(); var loop = new BlockIdentity(); var exit = new BlockIdentity();
        var input = t.Atom(new EntryAtom(new(SlotKind.Integer)), 64); var mergeId = new MergeIdentity(); var receiver = t.Atom(new ResultAtom(mergeId), 64);
        var callId = new CallIdentity(); var returned = t.Atom(new ResultAtom(callId), 64);
        var f = new FunctionBuilder(t, head, 64, new(t.Atom(new RootAtom(AddressRoot.Frame), 64)));
        f.Inputs.Add(new(new(SlotKind.Integer), input));
        f.Blocks.Add(new(head, [], [], new Jump(loop)));
        f.Blocks.Add(new(loop, [new(mergeId, receiver, [new(head, input), new(loop, returned)])],
            [new Call(callId, new ImageFunction(10), [new(new(SlotKind.Integer), receiver), new(new(SlotKind.Integer, 1), t.Constant(0, 64))], [new(new(SlotKind.Integer), returned)])],
            new Branch(t.Unknown(1, new("test.loop", "循环条件。")), loop, exit)));
        f.Blocks.Add(new(exit, [], [], new Return([])));
        var names = new ValueNamingQuery(new StateQueries(), calls, NamingFacts.Empty, spec, binder,
            binder.Definition(definition, BindingEntryKind.SharedGeneric, instance).Value, witness: witness);
        var function = f.Freeze(); checks.True(ExitChecker.Check(function).IsValid, "共享调用反馈的引用循环满足原生契约");
        foreach (bool resultFirst in new[] { false, true })
        {
            var c = names.CreateContext(function);
            _ = c.Get(names, resultFirst ? returned : receiver);
            checks.True(c.Get(names, receiver).Value is { Kind: ValueKind.ManagedReference, Name: ReferenceValueName, StaticType: var merged } && merged == openNode,
                "共享调用结果反馈的接收者保留开放定义类型");
            checks.True(c.Get(names, returned).Value is { Kind: ValueKind.ManagedReference, Name: CallResultName, StaticType: var result } && result == openNode,
                "空方法信息的共享调用按接收者见证命名返回值");
            checks.True(!names.SameValue(c, receiver, returned).Value, "共享调用结果与接收者合流保留不同定义身份");
        }
    }
}
