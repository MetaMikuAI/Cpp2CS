using System.Reflection;
using Cpp2CS.Input;
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

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    private static void GenericChecks(Assertions checks, ProgramModel primitives)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var layouts = new FieldLayouts(spec, 8, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var primitiveTypes = primitives.Types.Where(t => t.Assembly == "mscorlib.dll").Select((t, i) => new TypeDef
        { Index = i, Assembly = t.Assembly, Namespace = t.Namespace, Name = t.Name, Token = t.Token,
            Attributes = t.Attributes, IsValueType = t.IsValueType, IsEnum = t.IsEnum }).ToArray();
        TypeRef Type(string name) => new DefinitionRef(primitiveTypes.Single(t => t.Name == name), []);
        var parameter = new GenericParameterDef { Name = "T", Position = 0, Attributes = 0 };
        var t = new GenericParameterRef("T", false, 0) { Parameter = parameter };
        var owner = new TypeDef { Index = primitiveTypes.Length, Assembly = "GenericChecks.dll", Namespace = "", Name = "Cell`1",
            Token = 0x02000001, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false,
            PackingSize = 0, ClassSizeIsDefault = true, GenericParameters = [parameter] };
        var field = new FieldDef { Index = 0, Owner = owner, Name = "Value", Type = t, Offset = -1, Attributes = FieldAttributes.Public };
        owner.Fields = [field];
        MethodDef Method(int i, string name, TypeRef result, params TypeRef[] args) => new() { Index = i, Owner = owner, Name = name,
            Token = (uint)(0x06000001 + i), Attributes = MethodAttributes.Public | (i is 9 or 10 ? 0 : MethodAttributes.Static), ImplAttributes = 0, Slot = -1,
            ReturnType = result, Parameters = args.Select((a, p) => new ParameterDef("p" + p, a, 0, null, false)).ToArray() };
        var cell = new DefinitionRef(owner, [t]);
        var methods = new[] { Method(0, "Identity", t, t), Method(1, "Get", t, cell), Method(2, "Set", Type("Void"), cell, t),
            Method(3, "Element", t, new ArrayRef(t, 1)), Method(4, "StoreElement", Type("Void"), new ArrayRef(t, 1), t),
            Method(5, "Null", Type("Boolean"), t), Method(6, "Convert", Type("Object"), t), Method(7, "Arithmetic", t, t),
            Method(8, "MethodIdentity", new GenericParameterRef("U", true, 0), new GenericParameterRef("U", true, 0)),
            Method(9, "GetThis", t), Method(10, "SetThis", Type("Void"), t),
            Method(11, "Choose", t, t, t, Type("Int32")), Method(12, "Compare", Type("Boolean"), t, t),
            Method(13, "ConvertInteger", Type("Int64"), t), Method(14, "Default", t), Method(15, "UncheckedCast", t, Type("Object")),
            Method(16, "CheckedCast", t, Type("Object")), Method(17, "Receiver", Type("Int32"), t) };
        methods[8].GenericParameters = [new() { Name = "U", Position = 0, Attributes = 0 }];
        owner.Methods = methods;
        var definitions = primitiveTypes.Append(owner).ToArray();
        var objectDef = ((DefinitionRef)Type("Object")).Definition;
        var hash = new MethodDef { Index = methods.Length, Owner = objectDef, Name = "GetHashCode", Token = 0x06000001,
            Attributes = MethodAttributes.Public | MethodAttributes.Virtual, ImplAttributes = 0, Slot = 2, ReturnType = Type("Int32") };
        objectDef.Methods = [hash];
        objectDef.VTable = [null, null, new(hash, [], [])];
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = [.. methods, hash], Fields = [field], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(d => d.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key),
                Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        checks.True(GenericWitness.IsValueInstance(new(methods[0], [Type("Int32")], []))
            && !GenericWitness.IsValueInstance(new(methods[0], [Type("Object")], [])), "代码地图的封闭实参决定是否有值类型实例");
        var sharedType = new TypeDef { Index = definitions.Length, Assembly = "GenericChecks.dll", Namespace = "Unity.IL2CPP.Metadata",
            Name = "__Il2CppFullySharedGenericStructType", Token = 0x02000002, Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false };
        checks.True(!GenericWitness.IsValueInstance(new(methods[0], [new DefinitionRef(sharedType, [])], [])), "完全共享实例不计为值见证");
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(), catalog);
        var skeleton = new Skeleton(program, 16);
        var emitter = new BodyEmitter(skeleton, new(program, layouts, 8));
        foreach (var method in methods)
        {
            var open = MethodRef.Open(method);
            var witness = new MethodRef(method, [Type("Object")], method.GenericParameters.Select(_ => Type("Object")).ToArray());
            var nativeLayouts = new GenericWitness(open, witness, layouts);
            var terms = new TermTable(); var block = new BlockIdentity();
            var frame = terms.Atom(new RootAtom(AddressRoot.Frame), 64);
            var image = terms.Atom(new RootAtom(AddressRoot.Image), 64);
            var builder = new FunctionBuilder(terms, block, 64, new(frame)) { ImageBase = image };
            Term Input(int index) { var slot = new AbstractSlot(SlotKind.Integer, index); var value = terms.Atom(new EntryAtom(slot), 64); builder.Inputs.Add(new(slot, value)); return value; }
            var input = Input(0); var second = Input(1);
            var statements = new List<Statement>(); var value = input;
            Term Address(long offset) => terms.Apply(new CoreOperator(CoreOperation.Add), 64, input, terms.Constant((ulong)offset, 64));
            var fieldOffset = nativeLayouts.Of(cell)!.Fields.Single().Offset;
            if (method.Name is "Get" or "GetThis" or "Element")
            {
                var id = new ReadIdentity(); value = terms.Atom(new ResultAtom(id), 64);
                statements.Add(new MemoryRead(id, Address(method.Name is "Get" or "GetThis" ? fieldOffset : spec.Layout.ArrayDataStart), 64, value));
            }
            if (method.Name is "Set" or "SetThis" or "StoreElement")
                statements.Add(new MemoryWrite(new(), Address(method.Name is "Set" or "SetThis" ? fieldOffset : spec.Layout.ArrayDataStart), 64, second));
            if (method.Name == "Null") value = terms.Apply(new CoreOperator(CoreOperation.ZeroExtend), 64, terms.Apply(new CoreOperator(CoreOperation.Equal), 1, input, terms.Constant(0, 64)));
            if (method.Name == "Default") value = terms.Constant(0, 64);
            if (method.Name == "Choose") value = terms.Apply(new CoreOperator(CoreOperation.Select), 64,
                terms.Slice(Input(2), 0, 1), input, second);
            if (method.Name == "Compare") value = terms.Apply(new CoreOperator(CoreOperation.ZeroExtend), 64,
                terms.Apply(new CoreOperator(CoreOperation.Equal), 1, input, second));
            if (method.Name == "Arithmetic") value = terms.Apply(new CoreOperator(CoreOperation.Add), 64, input, terms.Constant(1, 64));
            var evidence = NamingFacts.Empty;
            var methodCalls = calls;
            if (method.Name is "CheckedCast" or "Receiver")
            {
                Term Read(Term root, long offset)
                {
                    var read = new ReadIdentity(); var result = terms.Atom(new ResultAtom(read), 64);
                    statements.Add(new MemoryRead(read, terms.Apply(new CoreOperator(CoreOperation.Add), 64, root, terms.Constant(offset, 64)), 64, result));
                    return result;
                }
                var klass = Read(image, 128);
                evidence = evidence with { Slots = evidence.Slots.Add(128, Cpp2CS.Kernel.Queries.Outcome<MetadataEntity>.Success(new ClassEntity(t))) };
                var id = new CallIdentity(); value = terms.Atom(new ResultAtom(id), 64);
                if (method.Name == "CheckedCast")
                {
                    var cast = catalog.Functions.First(f => f.Operation.Name == "CastClass" && f.Signature is not null);
                    methodCalls = new(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(cast), catalog);
                    statements.Add(new Call(id, new ImageFunction(20), [new(new(SlotKind.Integer), input), new(new(SlotKind.Integer, 1), klass)], [new(new(SlotKind.Integer), value)]));
                }
                else
                {
                    var target = Read(klass, spec.Layout.VtableStart + 2 * spec.Layout.VtableSlotSize + spec.Layout.Field("VirtualInvokeData", "methodPtr").ByteOffset);
                    var info = Read(klass, spec.Layout.VtableStart + 2 * spec.Layout.VtableSlotSize + spec.Layout.Field("VirtualInvokeData", "method").ByteOffset);
                    statements.Add(new Call(id, new ComputedTarget(target), [new(new(SlotKind.Integer), input), new(new(SlotKind.Integer, 1), info)], [new(new(SlotKind.Integer), value)]));
                }
            }
            builder.Blocks.Add(new(block, [], [.. statements], new Return(ManagedTypes.IsVoid(method.ReturnType) ? [] : [new(new(SlotKind.Integer), value)])));
            var function = builder.Freeze();
            var result = new IntegerLowering(function, open, binder, new(program, nativeLayouts, 8), calls: methodCalls, spec: spec, names: evidence, witness: witness).Run(BindingEntryKind.SharedGeneric);
            if (method.Name is "UncheckedCast" or "ConvertInteger" or "Arithmetic" or "Compare")
            {
                var reason = method.Name is "UncheckedCast" or "ConvertInteger" ? "Conversion" : "Arithmetic";
                checks.True(result.Failure?.Reason.Code == "lowering.Generic." + reason, method.Name + "：类型参数的禁用操作分原因报洞：" + result.Failure);
            }
            else
            {
                checks.True(result.Body?.Method == open, method.Name + "：见证恢复开放体：" + result.Failure);
                if (result.Body is { } body)
                {
                    checks.True(emitter.Emit([body]).Count == 0, method.Name + "：开放位置通过 CIL 写出校验");
                    var il = skeleton.Method(method).Body.Instructions;
                    if (method.Name is "Element" or "StoreElement") checks.True(il.Any(i => i.Operand is Mono.Cecil.GenericParameter), method.Name + "：元素指令保留 T");
                    if (method.Name is "Null" or "Convert") checks.True(il.Any(i => i.OpCode.Code == Mono.Cecil.Cil.Code.Box && i.Operand is Mono.Cecil.GenericParameter), method.Name + "：类型参数流向对象或判空时写 box T");
                    if (method.Name == "Default") checks.True(il.Any(i => i.OpCode.Code == Mono.Cecil.Cil.Code.Initobj && i.Operand is Mono.Cecil.GenericParameter), "空常量流入 T 写 default(T)");
                    if (method.Name == "CheckedCast") checks.True(il.Any(i => i.OpCode.Code == Mono.Cecil.Cil.Code.Unbox_Any && i.Operand is Mono.Cecil.GenericParameter), "原生检查 T 后写 unbox.any T");
                    if (method.Name == "Receiver") checks.True(il.Any(i => i.OpCode.Code == Mono.Cecil.Cil.Code.Constrained && i.Operand is Mono.Cecil.GenericParameter)
                        && il.Any(i => i.OpCode.Code == Mono.Cecil.Cil.Code.Callvirt), "T 类解析的虚调用写 constrained. T callvirt");
                    if (method.Name is "Get" or "Set") checks.True(il.Select(i => i.Operand).OfType<Mono.Cecil.FieldReference>().Any(f => f.DeclaringType.ContainsGenericParameter), method.Name + "：字段引用保留开放声明类型");
                    if (method.Name is "Identity" or "Default")
                    {
                        var valueWitness = witness with { TypeArguments = [Type("Int32")] };
                        var valueLayouts = new GenericWitness(open, valueWitness, layouts);
                        var valueResult = new IntegerLowering(function, open, binder, new(program, valueLayouts, 8), calls: calls,
                            spec: spec, witness: valueWitness).Run(BindingEntryKind.SharedGeneric);
                        checks.True(valueResult.Body is { } valueBody && GenericBodyComparison.Compare(body, valueBody) is null,
                            method.Name + "：值见证使用实例 ABI，开放 T 的搬运与零值写法相同：" + valueResult.Failure);
                    }
                }
            }
            var rejected = new IntegerLowering(function, open, binder, new(program, nativeLayouts, 8), witness: witness with { TypeArguments = [Type("String")] }).Run(BindingEntryKind.SharedGeneric);
            checks.True(rejected.Failure?.Reason.Code == "lowering.Generic.Witness", method.Name + "：非规范实例不能作为定义见证");
            var entries = new[] { new CodeEntry(1, EntryKind.GenericMethod, witness with { TypeArguments = [Type("String")] }, 0, null), new CodeEntry(2, EntryKind.GenericMethod, witness, 1, null) };
            checks.True(RecoverySession.SelectEntry(method, entries).Address == 2, "见证选择依据全部实参，不依据地址");
            var valueEntries = new[] { new CodeEntry(1, EntryKind.GenericMethod, witness with { TypeArguments = [new DefinitionRef(sharedType, [])] }, 0, null),
                new CodeEntry(3, EntryKind.GenericMethod, witness with { TypeArguments = [Type("Int32")] }, 1, null) };
            checks.True(RecoverySession.SelectValueEntry(valueEntries)?.Address == 3, "值见证排除完全共享实例");
        }
        var definition = MethodRef.Open(methods[0]);
        ManagedBody Copy(int local, int width, ulong label) => new(definition, [new(label, [
            new ManagedAssignment(10, new(new(local), t, width), new ArgumentValue(0, t, width)),
            new ManagedReturn(20, new LocalValue(new(local), t, width))])]);
        checks.True(GenericBodyComparison.Compare(Copy(7, 64, 100), Copy(15, 32, 200)) is null, "见证比较按首次出现归一局部，忽略实例位宽和原生地址");
        var branched = new ManagedBody(definition, [new(0, [new ManagedBranch(0, new ConstantValue(1, Type("Boolean"), 1), new(1, []), new(2, []))]),
            new(1, [new ManagedReturn(0, new ArgumentValue(0, t, 64))]), new(2, [new ManagedReturn(0, new ComposedValue(t, []))])]);
        var specialized = GenericBodyComparison.Compare(branched, Copy(0, 32, 0));
        checks.True(specialized is { Code: "lowering.Generic.Specialized" } && specialized.Message.Contains("第一处不同", StringComparison.Ordinal), "值实例少分支时保留 Specialized 与第一处不同");
        var wrongType = Copy(0, 64, 0) with { Blocks = [new(0, [new ManagedAssignment(0, new(new(0), Type("Object"), 64), new ArgumentValue(0, t, 64))])] };
        checks.True(GenericBodyComparison.Compare(Copy(0, 64, 0), wrongType)?.Code == "lowering.Generic.Specialized", "见证比较不忽略局部的开放类型");
        {
            var method = methods[6]; var open = MethodRef.Open(method);
            var instance = new MethodRef(method, [Type("Int32")], []);
            var nativeLayouts = new GenericWitness(open, instance, layouts);
            var terms = new TermTable(); var block = new BlockIdentity();
            var frame = terms.Atom(new RootAtom(AddressRoot.Frame), 64); var image = terms.Atom(new RootAtom(AddressRoot.Image), 64);
            var argument = terms.Atom(new EntryAtom(new(SlotKind.Integer)), 64);
            var read = new ReadIdentity(); var klass = terms.Atom(new ResultAtom(read), 64);
            var call = new CallIdentity(); var result = terms.Atom(new ResultAtom(call), 64);
            var builder = new FunctionBuilder(terms, block, 64, new(frame)) { ImageBase = image };
            builder.Inputs.Add(new(new(SlotKind.Integer), argument));
            builder.Blocks.Add(new(block, [], [
                new MemoryRead(read, terms.Apply(new CoreOperator(CoreOperation.Add), 64, image, terms.Constant(128, 64)), 64, klass),
                new MemoryWrite(new(), frame, 32, terms.Slice(argument, 0, 32)),
                new Call(call, new ImageFunction(20), [new(new(SlotKind.Integer), klass), new(new(SlotKind.Integer, 1), frame)], [new(new(SlotKind.Integer), result)])],
                new Return([new(new(SlotKind.Integer), result)])));
            var runtime = catalog.Functions.First(f => f.Operation.Name == "Box" && f.Signature is not null);
            var boxing = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(runtime), catalog);
            var evidence = NamingFacts.Empty with { Slots = NamingFacts.Empty.Slots.Add(128, Cpp2CS.Kernel.Queries.Outcome<MetadataEntity>.Success(new ClassEntity(t))) };
            var lowered = new IntegerLowering(builder.Freeze(), open, binder, new(program, nativeLayouts, 8), calls: boxing,
                effects: new ManagedCallEffects(boxing), spec: spec, names: evidence, witness: instance).Run(BindingEntryKind.SharedGeneric);
            checks.True(lowered.Body is { } body && body.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>()
                .Any(s => s.Value is BoxValue { Boxed: GenericParameterRef, Operand.Type: GenericParameterRef }) && emitter.Emit([body]).Count == 0,
                "基元值见证经 T 类的运行时装箱写 box T：" + lowered.Failure);
        }
        GenericContextChecks(checks, program, methods, binder, layouts, spec);
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
}
