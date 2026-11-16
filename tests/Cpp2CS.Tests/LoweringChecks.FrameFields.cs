using System.Collections.Immutable;
using System.Reflection;
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
    private static void FrameFieldChecks(Assertions checks, ProgramModel primitives)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var layouts = new FieldLayouts(spec, 8, 8); var binder = new MethodBinder(new(layouts), new Aapcs64());
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").ToList();
        TypeRef Primitive(string n) => new DefinitionRef(definitions.Single(t => t.Name == n), []);
        TypeDef Define(string name, int size, bool value = true) { var d = new TypeDef { Index = definitions.Count, Assembly = "FrameFields.dll", Namespace = "", Name = name,
            Token = (uint)(0x02000001 + definitions.Count), Attributes = TypeAttributes.Public, IsValueType = value, IsEnum = false,
            Size = size, PackingSize = 0, ClassSizeIsDefault = true }; definitions.Add(d); return d; }
        var s = Define("S", 16); var b = Define("B", 8); var x = Define("X", 4); var owner = Define("Owner", 64, false);
        TypeRef Ref(TypeDef d) => new DefinitionRef(d, []);
        int fieldId = 0;
        FieldDef Field(TypeDef d, string name, TypeRef type, int offset) => new() { Index = fieldId++, Owner = d, Name = name, Type = type,
            Offset = offset, Attributes = FieldAttributes.Public };
        s.Fields = [Field(s, "a", Primitive("Int32"), 0), Field(s, "b", Ref(b), 4), Field(s, "c", Primitive("Int32"), 12)];
        b.Fields = [Field(b, "x", Ref(x), 0), Field(b, "y", Primitive("Int32"), 4)];
        x.Fields = [Field(x, "value", Primitive("Int32"), 0)];
        owner.Fields = [Field(owner, "Pointer", Primitive("Int64"), 16)];
        var methods = new List<MethodDef>();
        MethodDef Method(TypeDef d, string name, TypeRef result, TypeRef[] parameters, bool instance = false)
        { var m = new MethodDef { Index = methods.Count, Owner = d, Name = name, Token = (uint)(0x06000001 + methods.Count), Attributes = MethodAttributes.Public | (instance ? 0 : MethodAttributes.Static),
            ImplAttributes = 0, Slot = -1, ReturnType = result, Parameters = parameters.Select((p,i) => new ParameterDef("p"+i, p, 0, null, false)).ToArray() }; methods.Add(m); return m; }
        var witness = Method(s, "Witness", Primitive("Void"), [], true);
        var mutate = Method(b, "Mutate", Primitive("Void"), [], true);
        var nested = Method(x, "Mutate", Primitive("Void"), [], true);
        var take = Method(owner, "Take", Primitive("Void"), [new ByRefRef(Ref(b))]);
        var wrong = Method(owner, "Wrong", Primitive("Void"), [new ByRefRef(Primitive("Int64"))]);
        string[] modes = ["Receiver", "Reference", "Nested", "Reversed", "Middle", "WrongType", "Heap", "NoWitness", "Arithmetic"];
        var entries = modes.ToDictionary(m => m, m => Method(owner, m, Primitive("Int32"), [Ref(owner)]));
        foreach (var d in definitions.Where(d => d.Assembly == "FrameFields.dll")) d.Methods = methods.Where(m => m.Owner == d).ToArray();
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = [.. s.Fields, .. b.Fields, .. x.Fields, .. owner.Fields], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(d => d.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1,0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var types = new ManagedTypes(program, layouts, 8); var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        foreach (var mode in modes)
        {
            var t = new TermTable(); var block = new BlockIdentity(); var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64);
            var f = new FunctionBuilder(t, block, 64, new(frame)); var root = t.Atom(new EntryAtom(new(SlotKind.Integer)), 64); f.Inputs.Add(new(new(SlotKind.Integer), root));
            var statements = new List<Statement>();
            Term Add(Term at, long n) => t.Apply(new CoreOperator(CoreOperation.Add), 64, at, t.Constant(unchecked((ulong)n), 64));
            var obj = Add(frame, -32);
            var inside = mode == "Arithmetic" ? t.Apply(new CoreOperator(CoreOperation.Or), 64, obj, t.Constant(4, 64))
                : Add(obj, mode == "Middle" ? 5 : 4);
            void Call(ulong address, Term argument) => statements.Add(new Call(new(), new ImageFunction(address), [new(new(SlotKind.Integer), argument), new(new(SlotKind.Integer, 1), t.Constant(0,64))], []));
            // 整体清零也覆盖邻接字段；缺少整体类型见证时不能猜外层类型。
            statements.Add(new MemoryWrite(new(), obj, 128, t.Constant(0,128)));
            if (mode is not ("NoWitness" or "Reversed")) Call(10, obj);
            for (int i=0;i<4;i++) statements.Add(new MemoryWrite(new(), Add(obj,i*4), 32, t.Constant((ulong)(i+3),32)));
            if (mode == "Heap") statements.Add(new MemoryWrite(new(), Add(root,16), 64, inside));
            else Call(30, inside);
            // 候选认定不依赖整个对象和内部字段的使用顺序。
            if (mode == "Reversed") Call(10, obj);
            Term Read(int offset, int width = 32)
            { var id = new ReadIdentity(); var term = t.Atom(new ResultAtom(id), width); statements.Add(new MemoryRead(id, Add(obj, offset), width, term)); return term; }
            var a = Read(0); var wholeB = Read(4, 64); var c = Read(12);
            var result = t.Apply(new CoreOperator(CoreOperation.Add), 32, a, t.Slice(wholeB, 0, 32));
            result = t.Apply(new CoreOperator(CoreOperation.Add), 32, result, t.Slice(wholeB, 32, 32));
            result = t.Apply(new CoreOperator(CoreOperation.Add), 32, result, c);
            f.Blocks.Add(new(block, [], [..statements], new Return([new(new(SlotKind.Integer), t.Concat(result,t.Constant(0,32)))])));
            var target = mode == "Reference" ? take : mode == "Nested" ? nested : mode == "WrongType" ? wrong : mutate;
            var calls = new CallNamingQuery(binder,new AddressMap(witness,target,witness), new NamingChecks.RuntimeMap(RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion,spec.Layout.Triple,spec.Layout.DataModel).Functions.First(k=>k.Signature is not null)),RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion,spec.Layout.Triple,spec.Layout.DataModel));
            var lowered=new IntegerLowering(f.Freeze(),MethodRef.Open(entries[mode]),binder,types,calls:calls,effects:new ManagedCallEffects(calls),spec:spec).Run();
            if (mode is "Middle" or "WrongType" or "Heap" or "NoWitness" or "Arithmetic")
            {
                checks.True(lowered.Body is null && lowered.Failure?.Reason.Code == "lowering.Frame.Use", mode + " 内部地址保留洞：" + lowered.Failure);
                var detail = mode switch { "Middle" => "偏移不在字段起点", "WrongType" => "字段类型与使用类型不同",
                    "NoWitness" => "外层对象没有类型见证", "Arithmetic" => "帧对象的地址参与运算后使用", _ => null };
                if (detail is not null) checks.True(lowered.Failure?.Reason.Cause?.Message == detail, mode + " 内部地址的具体拒绝原因：" + lowered.Failure);
                continue;
            }
            checks.True(lowered.Body is not null,mode+" 帧字段取址下降："+lowered.Failure);
            if(lowered.Body is not {} body) continue;
            var errors=emitter.Emit([body]); checks.True(errors.Count==0,mode+" 帧字段取址 CIL 校验："+string.Join(';',errors.Values));
            var call=body.Blocks.SelectMany(q=>q.Statements).OfType<ManagedCall>().Single(q=>q.Invocation.Method.Method==target);
            var argument=call.Invocation.Receiver ?? call.Invocation.Arguments[0];
            checks.True(argument is AddressValue { Target: FieldValue }, mode + " 使用局部字段地址");
            checks.True(Cpp2CS.Managed.ManagedValues.Walk(argument).OfType<LocalValue>().Select(v => v.Type).Distinct().SequenceEqual([Ref(s)]),
                mode + " 字段地址只以外层 S 局部为根，不建立内部重叠对象");
            var emitted=skeleton.Method(entries[mode]);
            checks.True(emitted.Body.Instructions.Count(i=>i.OpCode.Code==Mono.Cecil.Cil.Code.Ldflda)>= (mode=="Nested"?2:1),mode+" 写出完整字段地址路径");
        }
        const string source="""
            public struct X { public int value; public void Mutate() { value += 13; } }
            public struct B { public X x; public int y; public void Mutate() { x.value += 11; y *= 3; } }
            public struct S { public int a; public B b; public int c; public void Witness() {} }
            public class Owner {
                public static void Take(ref B b) { b.x.value += 17; b.y *= 5; }
                public static int Receiver(Owner owner) { S s=default; s.Witness(); s.a=3; s.b.x.value=4; s.b.y=5; s.c=6; s.b.Mutate(); return s.a+s.b.x.value+s.b.y+s.c; }
                public static int Reference(Owner owner) { S s=default; s.Witness(); s.a=3; s.b.x.value=4; s.b.y=5; s.c=6; Take(ref s.b); return s.a+s.b.x.value+s.b.y+s.c; }
                public static int Nested(Owner owner) { S s=default; s.Witness(); s.a=3; s.b.x.value=4; s.b.y=5; s.c=6; s.b.x.Mutate(); return s.a+s.b.x.value+s.b.y+s.c; }
                public static int Reversed(Owner owner) { S s=default; s.a=3; s.b.x.value=4; s.b.y=5; s.c=6; s.b.Mutate(); s.Witness(); return s.a+s.b.x.value+s.b.y+s.c; }
            }
            """;
        using var reference = new CompiledSource(source); using var tested = new CompiledSource(source);
        foreach(var mode in new[]{"Receiver","Reference","Nested","Reversed"})
        {
            var output=tested.Method("Owner",mode); var emitted=skeleton.Method(entries[mode]); if(!emitted.HasBody) continue;
            output.Body=emitted.Body;
            Mono.Cecil.TypeReference MapType(Mono.Cecil.TypeReference type)=>type is Mono.Cecil.ByReferenceType byref ? new Mono.Cecil.ByReferenceType(MapType(byref.ElementType)) : tested.Module.GetType(type.FullName) ?? tested.Module.ImportReference(System.Type.GetType(type.FullName,true)!);
            foreach(var i in output.Body.Instructions)
                if(i.Operand is Mono.Cecil.FieldReference field) i.Operand=tested.Module.GetType(field.DeclaringType.FullName).Fields.Single(q=>q.Name==field.Name);
                else if(i.Operand is Mono.Cecil.MethodReference m) i.Operand=tested.Module.GetType(m.DeclaringType.FullName).Methods.Single(q=>q.Name==m.Name);
                else if(i.Operand is Mono.Cecil.TypeReference type) i.Operand=MapType(type);
                else if(i.Operand is Mono.Cecil.ParameterDefinition p) i.Operand=output.Parameters[p.Index];
            foreach(var local in output.Body.Variables) local.VariableType=MapType(local.VariableType);
            var comparison=CilComparison.Compare(reference.Method("Owner",mode),output);
            checks.True(comparison.Status==CilComparisonStatus.Match && comparison.CompletedCases==32,mode+" 字段调用后读取与邻接字段值的执行对照："+comparison);
        }
        foreach(var assembly in skeleton.Assemblies) assembly.Dispose();
    }
}
