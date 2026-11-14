using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Kernel.Queries;
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
    private static void SpecificationValues(Assertions checks, RuntimeSpec spec)
    {
        var t = new TermTable(); var head = new BlockIdentity(); var left = new BlockIdentity();
        var right = new BlockIdentity(); var join = new BlockIdentity();
        var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
        var builder = new FunctionBuilder(t, head, 64, new(frame)) { ImageBase = image };
        var input = t.Atom(new EntryAtom(new(SlotKind.Integer)), 64);
        builder.Inputs.Add(new(new(SlotKind.Integer), input));
        var statements = new List<Statement>();
        Term Add(Term a, Term b) => t.Apply(new CoreOperator(CoreOperation.Add), 64, a, b);
        Term Offset(Term a, long n) => Add(a, t.Constant(unchecked((ulong)n), 64));
        Term Read(Term address, int width = 64)
        {
            var id = new ReadIdentity(); var value = t.Atom(new ResultAtom(id), width);
            statements.Add(new MemoryRead(id, address, width, value)); return value;
        }
        var objectClass = Read(Offset(input, spec.Layout.Field("Il2CppObject", "klass").ByteOffset));
        var klass = Read(Offset(image, 128));
        var statics = Read(Offset(klass, spec.Layout.Field("Il2CppClass", "static_fields").ByteOffset));
        var otherClass = Read(Offset(image, 256));
        var otherStatics = Read(Offset(otherClass, spec.Layout.Field("Il2CppClass", "static_fields").ByteOffset));
        var hierarchy = Read(Offset(klass, spec.Layout.Field("Il2CppClass", "typeHierarchy").ByteOffset));
        var depth = Read(Offset(klass, spec.Layout.Field("Il2CppClass", "typeHierarchyDepth").ByteOffset), 8);
        var index = t.Apply(new CoreOperator(CoreOperation.Add), 64,
            t.Apply(new CoreOperator(CoreOperation.ZeroExtend), 64, depth), t.Constant(ulong.MaxValue, 64));
        var elementAddress = Offset(Add(hierarchy, t.Apply(new CoreOperator(CoreOperation.ShiftLeft), 64,
            t.Apply(new CoreOperator(CoreOperation.ZeroExtend), 64, depth), t.Constant(3, 64))), -8);
        var element = Read(elementAddress);
        var wrong = Read(Offset(elementAddress, 1));
        var partial = Read(elementAddress, 32);
        var flagOffset = spec.Layout.Field("Il2CppClass", "cctor_finished_or_no_cctor").ByteOffset;
        var flag = Read(Offset(klass, flagOffset), 32);
        var sameVersion = Read(Offset(klass, flagOffset), 32);
        statements.Add(new Call(new(), new ImageFunction(99), [], []));
        var objectClassAgain = Read(Offset(input, spec.Layout.Field("Il2CppObject", "klass").ByteOffset));
        var again = Read(Offset(image, 128));
        var second = Read(Offset(again, spec.Layout.Field("Il2CppClass", "static_fields").ByteOffset));
        var hierarchyAgain = Read(Offset(again, spec.Layout.Field("Il2CppClass", "typeHierarchy").ByteOffset));
        var elementAgain = Read(Offset(Add(hierarchyAgain, t.Apply(new CoreOperator(CoreOperation.ShiftLeft), 64,
            t.Apply(new CoreOperator(CoreOperation.ZeroExtend), 64, depth), t.Constant(3, 64))), -8));
        var flagAgain = Read(Offset(again, flagOffset), 32);
        builder.Blocks.Add(new(head, [], statements.ToImmutableArray(), new Branch(t.Unknown(1, new("test", "条件")), left, right)));
        builder.Blocks.Add(new(left, [], [], new Jump(join)));
        builder.Blocks.Add(new(right, [], [new Call(new(), new ImageFunction(99), [], [])], new Jump(join)));
        Merge Phi(Term a, Term b)
        {
            var id = new MergeIdentity(); return new(id, t.Atom(new ResultAtom(id), a.Width), [new(left, a), new(right, b)]);
        }
        var fixedMerge = Phi(statics, second); var mutableMerge = Phi(flag, flagAgain); var sameVersionMerge = Phi(flag, sameVersion);
        statements.Clear();
        var joinedFlag = Read(Offset(klass, flagOffset), 32);
        statements.Add(new Call(new(), new ImageFunction(99), [], []));
        var changedFlag = Read(Offset(klass, flagOffset), 32);
        builder.Blocks.Add(new(join, [fixedMerge, mutableMerge, sameVersionMerge], [.. statements], new Return([])));
        var owner = new TypeDef { Index = 0, Assembly = "test", Namespace = "", Name = "Owner", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var facts = NamingFacts.Empty with { Slots = ImmutableDictionary<ulong, Outcome<MetadataEntity>>.Empty.Add(128,
            Outcome<MetadataEntity>.Success(new ClassEntity(new DefinitionRef(owner, [])))).Add(256,
            Outcome<MetadataEntity>.Success(new ClassEntity(new ArrayRef(new DefinitionRef(owner, []), 1)))) };
        var binder = new MethodBinder(new(new FieldLayouts(spec, 8, 8)), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var calls = new CallNamingQuery(binder, new Map([]), new RuntimeMap(), catalog);
        var type = new DefinitionRef(owner, []);
        var method = new MethodRef(new MethodDef { Index = 0, Owner = owner, Name = "Inspect", Token = 0,
            Attributes = MethodAttributes.Static, ImplAttributes = 0, Slot = -1, ReturnType = type,
            Parameters = [new("value", type, 0, null, false)] }, [], []);
        var state = new StateQueries(); var names = new ValueNamingQuery(state, calls, facts, spec, binder,
            binder.Entry(method, BindingEntryKind.Ordinary).Value);
        var function = builder.Freeze(); var c = names.CreateContext(function);
        checks.True(ExitChecker.Check(function).IsValid, "规格下标与定值用例满足原生契约");
        var named = c.Get(names, element);
        checks.True(named.IsSuccess && named.Value is { Record: "Il2CppClass", Name: ArrayElementName { Array.Field: "Il2CppClass.typeHierarchy", Index: var actual } }
            && actual == c.Get(state.Resolve, index).Value, "规格数组动态元素保留下标项及元素结构名");
        checks.True(c.Get(names, wrong).Value.Kind == ValueKind.Unnamed && c.Get(names, partial).Value.Kind == ValueKind.Unnamed,
            "未对齐或不完整的规格数组元素不命名");
        checks.True(names.FixedValue(c, element).Value is ArrayElementName && names.SameValue(c, element, elementAgain).Value,
            "同一下标的不可变规格元素跨内存版本同值，保留下标的读取身份");
        checks.True(names.SameValue(c, objectClass, objectClassAgain).Value,
            "同一形参对象的不可变类指针跨调用同值");
        checks.True(c.Get(state.Resolve, statics).Value != c.Get(state.Resolve, second).Value && names.SameValue(c, statics, second).Value,
            "同一不可变规格字段跨内存版本同值");
        checks.True(c.Get(names, fixedMerge.Result).Value.Name is FieldName { Field: "Il2CppClass.static_fields" },
            "定值合流保留唯一名字");
        checks.True(names.SameValue(c, fixedMerge.Result, statics).Value && !names.SameValue(c, statics, otherStatics).Value,
            "定值合流与来源同值，不同类的相同不可变字段不同值");
        checks.True(names.SameValue(c, flag, sameVersion).Value && c.Get(names, sameVersionMerge.Result).Value.Name is FieldName,
            "可变字段的同一读取版本仍由状态身份保证同值");
        checks.True(!names.SameValue(c, flag, flagAgain).Value && c.Get(names, mutableMerge.Result).Value.Kind == ValueKind.Unnamed,
            "可变的同名规格字段保留版本，合流不冒充定值");
        checks.True(c.Get(state.Resolve, joinedFlag).Value.Identity is MemoryMerge
            && c.Get(names, joinedFlag).Value is { Kind: ValueKind.Integer, Name: FieldName }
            && names.FixedValue(c, joinedFlag).Value is null && !names.SameValue(c, joinedFlag, changedFlag).Value,
            "汇合处规格字段重读有种类，不以同一字段名消去不同读取版本");
    }
}
