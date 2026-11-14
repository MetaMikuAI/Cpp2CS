using System.Collections.Immutable;
using System.Reflection;
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
    private static void MergedReceivers(Assertions checks, RuntimeSpec spec)
    {
        TypeDef Type(string name, string ns = "", string assembly = "test", bool value = false, bool contract = false) => new()
        { Index = 0, Assembly = assembly, Namespace = ns, Name = name, Token = 0, Attributes = TypeAttributes.Public | (contract ? TypeAttributes.Interface : 0),
            IsValueType = value, IsEnum = false, Size = 64, PackingSize = 0, ClassSizeIsDefault = true };
        var obj = new DefinitionRef(Type("Object", "System", "mscorlib.dll"), []);
        var integer = new DefinitionRef(Type("Int32", "System", "mscorlib.dll", true), []);
        var parent = Type("Parent"); parent.BaseType = obj; var parentType = new DefinitionRef(parent, []);
        var left = Type("Left"); left.BaseType = parentType; var leftType = new DefinitionRef(left, []);
        var right = Type("Right"); right.BaseType = parentType; var rightType = new DefinitionRef(right, []);
        var holder = Type("Holder"); holder.BaseType = obj; var holderType = new DefinitionRef(holder, []);
        int header = (int)spec.Layout.ObjectHeaderSize;
        FieldDef Field(TypeDef owner, string name, TypeRef type, int offset, bool statics = false) => new()
        { Index = offset, Owner = owner, Name = name, Type = type, Offset = offset,
            Attributes = FieldAttributes.Public | (statics ? FieldAttributes.Static : 0) };
        parent.Fields = [Field(parent, "Number", integer, header)];
        holder.Fields = [Field(holder, "Receiver", parentType, header), Field(holder, "Counter", integer, header + 8),
            Field(holder, "Global", parentType, 0, true)];
        MethodDef Method(TypeDef owner, string name, int slot, TypeRef type) => new()
        { Index = slot, Owner = owner, Name = name, Token = 0, Attributes = MethodAttributes.Public | MethodAttributes.Virtual,
            ImplAttributes = 0, Slot = slot, ReturnType = type, Parameters = [] };
        var apply = Method(parent, "Apply", 4, integer); var next = Method(parent, "Next", 5, parentType);
        parent.Methods = [apply, next]; left.Methods = [Method(left, "Extra", 6, integer)];
        var entry = new MethodRef(new MethodDef { Index = 0, Owner = holder, Name = "Inspect", Token = 0,
            Attributes = MethodAttributes.Static, ImplAttributes = 0, Slot = -1, ReturnType = integer,
            Parameters = [new("holder", holderType, 0, null, false), new("left", leftType, 0, null, false), new("right", rightType, 0, null, false)] }, [], []);
        var layouts = new FieldLayouts(spec, 8, 8); var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var allocate = catalog.Functions.First(f => f.Operation.Name == "AllocateObject" && f.Signature is not null);
        var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(), catalog);
        var facts = NamingFacts.Empty with { Slots = ImmutableDictionary<ulong, Cpp2CS.Kernel.Queries.Outcome<MetadataEntity>>.Empty
            .Add(256, Cpp2CS.Kernel.Queries.Outcome<MetadataEntity>.Success(new ClassEntity(holderType)))
            .Add(264, Cpp2CS.Kernel.Queries.Outcome<MetadataEntity>.Success(new ClassEntity(rightType))) };
        foreach (var mode in Enumerable.Range(0, 10))
        {
            var t = new TermTable(); var head = new BlockIdentity(); var a = new BlockIdentity(); var b = new BlockIdentity();
            var join = new BlockIdentity(); var exit = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            var owner = t.Atom(new EntryAtom(new(SlotKind.Integer)), 64);
            var x = t.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64); var y = t.Atom(new EntryAtom(new(SlotKind.Integer, 2)), 64);
            var condition = t.Unknown(1, new("test.condition", "分支条件。"));
            var f = new FunctionBuilder(t, head, 64, new(frame)) { ImageBase = image };
            f.Inputs.Add(new(new(SlotKind.Integer), owner)); f.Inputs.Add(new(new(SlotKind.Integer, 1), x)); f.Inputs.Add(new(new(SlotKind.Integer, 2), y));
            Term Add(Term root, long offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, root, t.Constant(offset, 64));
            Term Read(List<Statement> statements, Term address, int width = 64)
            { var id = new ReadIdentity(); var result = t.Atom(new ResultAtom(id), width); statements.Add(new MemoryRead(id, address, width, result)); return result; }
            var start = new List<Statement>(); var other = new List<Statement>(); var body = new List<Statement>();
            var address = Add(owner, header);
            if (mode == 9)
            {
                var klass = Read(start, Add(image, 256));
                address = Read(start, Add(klass, spec.Layout.Field("Il2CppClass", "static_fields").ByteOffset));
            }
            var first = Read(start, address); var counter = Read(start, Add(owner, header + 8), 32);
            var klassInput = Read(other, Add(image, 264)); var newId = new CallIdentity(); var allocated = t.Atom(new ResultAtom(newId), 64);
            other.Add(new Call(newId, new NamedFunction(allocate.MangledName), [new(new(SlotKind.Integer), klassInput)], [new(new(SlotKind.Integer), allocated)]));
            other.Add(new Call(new(), new ImageFunction(99), [new(new(SlotKind.Integer), allocated)], []));
            if (mode != 3) other.Add(new MemoryWrite(new(), address, 64, allocated));
            var mergeId = new MergeIdentity(); var merged = t.Atom(new ResultAtom(mergeId), 64);
            var merges = new List<Merge>();
            Term receiver = mode switch
            {
                2 or 3 or 9 => Read(body, address),
                4 => t.Apply(new CoreOperator(CoreOperation.Select), 64, condition, x, y),
                6 => t.Apply(new CoreOperator(CoreOperation.Select), 64, condition, x, t.Constant(0, 64)),
                _ => merged,
            };
            (CallIdentity Identity, Term Result) Invoke(Term self, int slot, List<Statement> statements)
            {
                var klass = Read(statements, self);
                long offset = spec.Layout.VtableStart + slot * spec.Layout.VtableSlotSize;
                var pointer = Read(statements, Add(klass, offset + spec.Layout.Field("VirtualInvokeData", "methodPtr").ByteOffset));
                var info = Read(statements, Add(klass, offset + spec.Layout.Field("VirtualInvokeData", "method").ByteOffset));
                var id = new CallIdentity(); var result = t.Atom(new ResultAtom(id), 64);
                statements.Add(new Call(id, new ComputedTarget(pointer), [new(new(SlotKind.Integer), self), new(new(SlotKind.Integer, 1), info)], [new(new(SlotKind.Integer), result)]));
                return (id, result);
            }
            var initial = receiver;
            if (mode == 5)
            {
                var test = catalog.Functions.First(f => f.Operation.Name == "IsInstance" && f.Signature is not null);
                var targetClass = Read(body, Add(image, 264)); var testId = new CallIdentity();
                body.Add(new Call(testId, new NamedFunction(test.MangledName),
                    [new(new(SlotKind.Integer), receiver), new(new(SlotKind.Integer, 1), targetClass)],
                    [new(new(SlotKind.Integer), t.Atom(new ResultAtom(testId), 64))]));
            }
            if (mode is 7 or 8) receiver = Invoke(receiver, 5, body).Result;
            if (mode == 8) merges.Add(new(mergeId, merged, [new(head, x), new(join, receiver)]));
            else merges.Add(new(mergeId, merged, [new(a, mode == 1 ? first : x), new(b, mode == 1 ? allocated : mode == 5 ? t.Constant(1, 64) : y)]));
            var twinId = new MergeIdentity(); var twin = t.Atom(new ResultAtom(twinId), 64);
            if (mode == 0) merges.Add(new(twinId, twin, merges[0].Inputs));
            var number = Read(body, Add(receiver, header), 32);
            var countAgain = Read(body, Add(owner, header + 8), 32);
            var call = Invoke(receiver, 4, body); var extra = Invoke(receiver, 6, body);
            f.Blocks.Add(new(head, [], [.. start], mode == 8 ? new Jump(join) : new Branch(condition, a, b)));
            if (mode != 8)
            { f.Blocks.Add(new(a, [], [], new Jump(join))); f.Blocks.Add(new(b, [], [.. other], new Jump(join))); }
            f.Blocks.Add(new(join, [.. merges], [.. body], mode == 8 ? new Branch(condition, join, exit) : new Return([])));
            if (mode == 8) f.Blocks.Add(new(exit, [], [], new Return([])));
            var function = f.Freeze(); checks.True(ExitChecker.Check(function).IsValid, "引用接收者用例满足原生契约：" + mode);
            var state = new StateQueries(); var names = new ValueNamingQuery(state, calls, facts, spec, binder, binder.Entry(entry, BindingEntryKind.Ordinary).Value);
            var locations = new ManagedLocationQuery(state, names, layouts, spec); var dispatch = new DispatchQuery(state, calls, names, locations, binder, spec);
            foreach (bool typesFirst in new[] { false, true })
            {
                var c = locations.CreateContext(function);
                if (typesFirst) _ = c.Get(locations.Types, receiver);
                var name = c.Get(names, receiver); var found = c.Get(dispatch, call.Identity);
                if (mode == 5)
                { checks.True(name.IsSuccess && name.Value.Kind == ValueKind.Unnamed && found.Value.Kind == DispatchKind.Unresolved,
                    "运行时对象用途不覆盖混有整数输入的合流定义"); continue; }
                checks.True(name.IsSuccess && name.Value.Kind == ValueKind.ManagedReference
                    && name.Value.StaticType == (mode == 6 ? leftType : parentType), "引用接收者的种类及公共类型：" + mode + " " + name.Value);
                checks.True(found.IsSuccess && found.Value is { Kind: DispatchKind.Virtual, Method: { } method } && method.Method == apply,
                    "合流、重读或选择作基类虚调用接收者：" + mode + " " + found.Value);
                checks.True(c.Get(names, number).Value.Kind == ValueKind.Integer && c.Get(locations.Types, number).Value?.Type == integer,
                    "引用结果作字段访问的基值：" + mode);
                checks.True(c.Get(dispatch, extra.Identity).Value.Why?.Code == (mode == 6 ? null : "dispatch.slot-method"),
                    "公共祖先没有派生类独有的槽：" + mode);
                if (mode is 2 or 3 or 9)
                {
                    checks.True(name.Value.Name is LoadedName && !names.SameValue(c, first, receiver).Value, "汇合重读按声明类型命名并保留版本：" + mode);
                    checks.True(c.Get(names, countAgain).Value is { Kind: ValueKind.Integer, Name: LoadedName, StaticType: var type } && type == integer
                        && !names.SameValue(c, counter, countAgain).Value, "值类型字段的汇合重读保留声明类型和版本：" + mode);
                }
                if (mode == 0) checks.True(names.FixedValue(c, receiver).Value is ReferenceValueName && !names.SameValue(c, receiver, twin).Value,
                    "相同输入的不同引用合流不构成同值凭据");
                if (mode == 8) checks.True(c.Get(names, initial).Value.StaticType == parentType, "循环类型从派生类扩大到基类后收敛");
            }
        }
        var itf = Type("Contract", contract: true);
        checks.True(ManagedTypes.CommonReferenceType([leftType, rightType], obj) == parentType, "类合流取最近公共祖先");
        checks.True(ManagedTypes.CommonReferenceType([new ArrayRef(leftType, 1), new ArrayRef(rightType, 1)], obj) == obj
            && ManagedTypes.CommonReferenceType([new DefinitionRef(itf, []), leftType], obj) == obj
            && ManagedTypes.CommonReferenceType([leftType, null], obj) == obj, "不同数组、接口及缺少静态类型的引用取 object");
        TypeRef[] references = [obj, parentType, leftType, rightType, new DefinitionRef(itf, []), new ArrayRef(leftType, 1), new ArrayRef(rightType, 1)];
        TypeRef? Join(TypeRef? x, TypeRef? y) => ManagedTypes.CommonReferenceType([x, y], obj);
        checks.True(references.All(type => Join(type, type) == type), "引用类型的并满足幂等律，包含接口与数组");
        checks.True(references.All(x => references.All(y => Join(x, y) == Join(y, x))), "引用类型的并满足交换律");
        checks.True(references.All(x => references.All(y => references.All(z => Join(Join(x, y), z) == Join(x, Join(y, z))))),
            "引用类型的并满足结合律，迭代合流不依赖来源次序");
    }
}
