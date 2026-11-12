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
            Method(13, "ConvertInteger", Type("Int64"), t) };
        methods[8].GenericParameters = [new() { Name = "U", Position = 0, Attributes = 0 }];
        owner.Methods = methods;
        var definitions = primitiveTypes.Append(owner).ToArray();
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = [field], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(d => d.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key),
                Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
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
            var builder = new FunctionBuilder(terms, block, 64, new(frame));
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
            if (method.Name == "Choose") value = terms.Apply(new CoreOperator(CoreOperation.Select), 64,
                terms.Slice(Input(2), 0, 1), input, second);
            if (method.Name == "Compare") value = terms.Apply(new CoreOperator(CoreOperation.ZeroExtend), 64,
                terms.Apply(new CoreOperator(CoreOperation.Equal), 1, input, second));
            if (method.Name == "Arithmetic") value = terms.Apply(new CoreOperator(CoreOperation.Add), 64, input, terms.Constant(1, 64));
            builder.Blocks.Add(new(block, [], [.. statements], new Return(ManagedTypes.IsVoid(method.ReturnType) ? [] : [new(new(SlotKind.Integer), value)])));
            var function = builder.Freeze();
            var result = new IntegerLowering(function, open, binder, new(program, nativeLayouts, 8), calls: calls, spec: spec, witness: witness).Run(BindingEntryKind.SharedGeneric);
            if (method.Name is "Null" or "Convert" or "ConvertInteger" or "Arithmetic" or "Compare")
            {
                var reason = method.Name == "Null" ? "NullTest" : method.Name is "Convert" or "ConvertInteger" ? "Conversion" : "Arithmetic";
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
                    if (method.Name is "Get" or "Set") checks.True(il.Select(i => i.Operand).OfType<Mono.Cecil.FieldReference>().Any(f => f.DeclaringType.ContainsGenericParameter), method.Name + "：字段引用保留开放声明类型");
                }
            }
            var rejected = new IntegerLowering(function, open, binder, new(program, nativeLayouts, 8), witness: witness with { TypeArguments = [Type("String")] }).Run(BindingEntryKind.SharedGeneric);
            checks.True(rejected.Failure?.Reason.Code == "lowering.Generic.Witness", method.Name + "：非规范实例不能作为定义见证");
            var entries = new[] { new CodeEntry(1, EntryKind.GenericMethod, witness with { TypeArguments = [Type("String")] }, 0, null), new CodeEntry(2, EntryKind.GenericMethod, witness, 1, null) };
            checks.True(RecoverySession.SelectEntry(method, entries).Address == 2, "见证选择依据全部实参，不依据地址");
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
}
