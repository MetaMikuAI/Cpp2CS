using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Output;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Dispatch;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Tests.Execution;
namespace Cpp2CS.Tests;
internal static partial class DispatchChecks
{
    private static void IdentityCases(Assertions checks)
    {
        var spec=InputCorpusChecks.Spec("arm64-v8a");
        var definitions=new List<TypeDef>(); var methods=new List<MethodDef>();
        TypeDef Define(string name, bool core=false, bool value=false, TypeRef? parent=null)
        {
            var type=new TypeDef { Index=definitions.Count,Assembly=core?"mscorlib.dll":"DispatchIdentity.dll",Namespace=core?"System":"",Name=name,
                Token=(uint)(0x02000001+definitions.Count),Attributes=TypeAttributes.Public,IsValueType=value,IsEnum=false,BaseType=parent,
                Size=value?name switch { "Void"=>0,"Boolean" or "SByte" or "Byte"=>1,"Char" or "Int16" or "UInt16"=>2,"Int32" or "UInt32" or "Single"=>4,_=>8 }:128,PackingSize=0,ClassSizeIsDefault=true };
            definitions.Add(type); return type;
        }
        TypeRef Ref(TypeDef type)=>new DefinitionRef(type,[]);
        var obj=Define("Object",true); var integer=Ref(Define("Int32",true,true)); var boolean=Ref(Define("Boolean",true,true));
        var pointer=Ref(Define("IntPtr",true,true)); var nothing=Ref(Define("Void",true,true));
        Define("Int64",true,true); Define("UInt64",true,true); Define("UIntPtr",true,true);
        Define("String",true,parent:Ref(obj));
        foreach(var name in new[] { "Char","SByte","Byte","Int16","UInt16","UInt32","Single","Double","RuntimeTypeHandle","RuntimeFieldHandle","RuntimeMethodHandle","TypedReference" })
            Define(name,true,true);
        var del=Define("Delegate",true,parent:Ref(obj)); var multi=Define("MulticastDelegate",true,parent:Ref(del));
        del.Fields=new[] { "invoke_impl","method_code","method" }.Select((n,i)=>new FieldDef { Index=i,Owner=del,Name=n,Type=pointer,Offset=(int)spec.Layout.ObjectHeaderSize+i*8,Attributes=FieldAttributes.Public }).ToArray();
        var callback=Define("Callback",parent:Ref(multi)); var child=Define("Child",parent:Ref(obj)); var owner=Define("Cases",parent:Ref(obj));
        MethodDef Method(TypeDef type,string name,TypeRef result,TypeRef[] parameters,bool instance=false,int slot=-1)
        {
            var m=new MethodDef { Index=methods.Count,Owner=type,Name=name,Token=(uint)(0x06000001+methods.Count),
                Attributes=MethodAttributes.Public | (instance?MethodAttributes.Virtual:MethodAttributes.Static),ImplAttributes=0,Slot=slot,
                ReturnType=result,Parameters=parameters.Select((p,i)=>new ParameterDef("p"+i,p,0,null,false)).ToArray() };
            methods.Add(m); return m;
        }
        var invoke=Method(callback,"Invoke",integer,[integer],true,4); var apply=Method(child,"Apply",integer,[integer],true,4);
        obj.VTable=[null,null,null,null]; child.VTable=[null,null,null,null,new(apply,[],[])];
        var touch=Method(owner,"Touch",nothing,[]);
        var modes=new[] { "Memory","Merged","Write","WrongObject","Intervening","Mixed","Cast","Guard","GuardOriginal","UncheckedTypeTest","WrongCastObject","Unproved" };
        var entries=modes.ToDictionary(mode=>mode,mode=>Method(owner,mode,integer,[boolean,mode is "Cast" or "Guard" or "GuardOriginal" or "UncheckedTypeTest" or "WrongCastObject" or "Unproved"?Ref(obj):Ref(callback),Ref(callback),integer]));
        foreach(var type in definitions) type.Methods=methods.Where(m=>m.Owner==type).ToArray();
        var program=new ProgramModel { MetadataVersion=0,Types=definitions,Methods=methods,Fields=del.Fields,RuntimeTypes=[],MethodSpecs=[],FieldRefs=[],StringLiterals=[],
            Assemblies=definitions.GroupBy(t=>t.Assembly).Select(g=>new AssemblyDef { Name=g.Key,AssemblyName=Path.GetFileNameWithoutExtension(g.Key),Version=new(1,0),Culture="",PublicKey=[],Types=g.ToArray() }).ToArray() };
        var layouts=new FieldLayouts(spec,8,8); var binder=new MethodBinder(new(layouts),new Aapcs64());
        var types=new ManagedTypes(program,layouts,8); var skeleton=new Skeleton(program,16); var emitter=new BodyEmitter(skeleton,types);
        var catalog=RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion,spec.Layout.Triple,spec.Layout.DataModel);
        var calls=new CallNamingQuery(binder,new TouchMap(touch),new NamingChecks.RuntimeMap(),catalog);
        using var source=new CompiledSource("""
            public delegate int Callback(int value);
            public class Child { public virtual int Apply(int value) => value + 1; }
            public static class Cases {
                public static void Touch() { }
                public static int Memory(bool c, Callback a, Callback b, int value) { if(c) Touch(); return a(value); }
                public static int MemoryOut(bool c, Callback a, Callback b, int value) => 0;
                public static int Merged(bool c, Callback a, Callback b, int value) => (c ? a : b)(value);
                public static int MergedOut(bool c, Callback a, Callback b, int value) => 0;
                public static int Cast(bool c, object a, Callback b, int value) => ((Child)a).Apply(value);
                public static int CastOut(bool c, object a, Callback b, int value) => 0;
                public static int Guard(bool c, object a, Callback b, int value) { var d=a as Child; return d==null ? -1 : d.Apply(value); }
                public static int GuardOut(bool c, object a, Callback b, int value) => 0;
                public static int GuardOriginal(bool c, object a, Callback b, int value) { var d=a as Child; return d==null ? -1 : d.Apply(value); }
                public static int GuardOriginalOut(bool c, object a, Callback b, int value) => 0;
            }
            """);
        foreach(var mode in modes)
        {
            var t=new TermTable(); var head=new BlockIdentity(); var left=new BlockIdentity(); var right=new BlockIdentity(); var join=new BlockIdentity();
            var frame=t.Atom(new RootAtom(AddressRoot.Frame),64); var image=t.Atom(new RootAtom(AddressRoot.Image),64);
            var f=new FunctionBuilder(t,head,64,new(frame)) { ImageBase=image };
            var args=Enumerable.Range(0,4).Select(i=>t.Atom(new EntryAtom(new(SlotKind.Integer,i)),64)).ToArray();
            for(int i=0;i<4;i++) f.Inputs.Add(new(new(SlotKind.Integer,i),args[i]));
            Term Add(Term root,long offset)=>t.Apply(new CoreOperator(CoreOperation.Add),64,root,t.Constant(offset,64));
            Term Read(List<Statement> statements,Term address)
            { var id=new ReadIdentity(); var result=t.Atom(new ResultAtom(id),64); statements.Add(new MemoryRead(id,address,64,result)); return result; }
            var start=new List<Statement>(); var body=new List<Statement>(); var facts=NamingFacts.Empty; var receiver=args[1]; Term? checkedReceiver=null;
            bool virtualCall=mode is "Cast" or "Guard" or "GuardOriginal" or "UncheckedTypeTest" or "WrongCastObject" or "Unproved";
            if(mode is "Memory" or "Merged" or "Mixed")
            {
                f.Blocks.Add(new(head,[],[],new Branch(t.Slice(args[0],0,1),left,right)));
                f.Blocks.Add(new(left,[],mode=="Memory"?[new Call(new(),new ImageFunction(10),[new(new(SlotKind.Integer),t.Constant(0,64))],[])]:[],new Jump(join)));
                f.Blocks.Add(new(right,[],[],new Jump(join)));
                var merges=ImmutableArray<Merge>.Empty;
                if(mode is "Merged" or "Mixed")
                { var id=new MergeIdentity(); receiver=t.Atom(new ResultAtom(id),64); merges=[new(id,receiver,[new(left,args[1]),new(right,mode=="Mixed"?args[3]:args[2])])]; }
                f.Blocks.Add(new(join,merges,[],new Return([])));
            }
            else if(mode is "Cast" or "Guard" or "GuardOriginal" or "UncheckedTypeTest" or "WrongCastObject")
            {
                var klass=Read(start,Add(image,256)); facts=facts with { Slots=facts.Slots.Add(256,Outcome<MetadataEntity>.Success(new ClassEntity(Ref(child)))) };
                var operation=catalog.Functions.First(r=>r.Operation.Name==(mode is "Cast" or "WrongCastObject"?"CastClass":"IsInstance") && r.Arguments.SequenceEqual(new[] { "object","class" }) && r.Signature is not null);
                var id=new CallIdentity(); var narrowed=t.Atom(new ResultAtom(id),64);
                checkedReceiver=narrowed;
                start.Add(new Call(id,new NamedFunction(operation.MangledName),[new(new(SlotKind.Integer),mode=="WrongCastObject"?args[2]:receiver),new(new(SlotKind.Integer,1),klass)],[new(new(SlotKind.Integer),narrowed)]));
                f.Blocks.Add(new(head,[],[..start],mode is "Cast" or "WrongCastObject" or "UncheckedTypeTest"?new Jump(join):new Branch(t.Apply(new CoreOperator(CoreOperation.Equal),1,narrowed,t.Constant(0,64)),right,join)));
                if(mode is "Guard" or "GuardOriginal") f.Blocks.Add(new(right,[],[],new Return([new(new(SlotKind.Integer),t.Constant(uint.MaxValue,64))])));
                f.Blocks.Add(new(join,[],[],new Return([])));
            }
            else f.Blocks.Add(new(head,[],[],new Jump(join)));
            Term target,information,self=receiver;
            if(virtualCall)
            {
                var klass=Read(body,receiver); long offset=spec.Layout.VtableStart+4*spec.Layout.VtableSlotSize;
                target=Read(body,Add(klass,offset+spec.Layout.Field("VirtualInvokeData","methodPtr").ByteOffset));
                information=Read(body,Add(klass,offset+spec.Layout.Field("VirtualInvokeData","method").ByteOffset));
                if(mode is "Cast" or "Guard") self=checkedReceiver!;
            }
            else
            {
                target=Read(body,Add(receiver,del.Fields[0].Offset));
                if(mode=="Write") body.Add(new MemoryWrite(new(),Add(receiver,del.Fields[0].Offset),64,t.Constant(7,64)));
                if(mode=="Intervening") body.Add(new Call(new(),new ImageFunction(10),[new(new(SlotKind.Integer),t.Constant(0,64))],[]));
                self=Read(body,Add(mode=="WrongObject"?args[2]:receiver,del.Fields[1].Offset));
                information=Read(body,Add(receiver,del.Fields[2].Offset));
            }
            var callId=new CallIdentity(); var resultValue=t.Atom(new ResultAtom(callId),64);
            body.Add(new Call(callId,new ComputedTarget(target),[new(new(SlotKind.Integer),self),new(new(SlotKind.Integer,1),args[3]),new(new(SlotKind.Integer,2),information)],[new(new(SlotKind.Integer),resultValue)]));
            var at=f.Blocks.FindIndex(b=>b.Identity==join);
            if(at<0) f.Blocks.Add(new(join,[],[..body],new Return([new(new(SlotKind.Integer),resultValue)])));
            else f.Blocks[at]=f.Blocks[at] with { Statements=[..body],End=new Return([new(new(SlotKind.Integer),resultValue)]) };
            var function=f.Freeze(); checks.True(ExitChecker.Check(function).IsValid,mode+" 原生契约");
            var state=new StateQueries(new ManagedCallEffects(calls));
            var names=new ValueNamingQuery(state,calls,facts,spec,binder,binder.Entry(MethodRef.Open(entries[mode]),BindingEntryKind.Ordinary).Value);
            var locations=new ManagedLocationQuery(state,names,layouts,spec); var dispatch=new DispatchQuery(state,calls,names,locations,binder,spec);
            var found=locations.CreateContext(function).Get(dispatch,callId);
            bool positive=mode is "Memory" or "Merged" or "Cast" or "Guard" or "GuardOriginal";
            checks.True(found.IsSuccess && (positive?found.Value.Kind==(virtualCall?DispatchKind.Virtual:DispatchKind.Delegate):found.Value.Kind==DispatchKind.Unresolved),mode+" 分派："+found.Value);
            if(mode=="Unproved") checks.True(found.Value.Why?.Code=="dispatch.slot-method" && found.Value.Why.Message.Contains("4 项") && found.Value.Why.Message.Contains("槽号 4"),"没有窄类型凭据时报告静态类型、虚表项数和槽号");
            if(!positive) continue;
            var lowered=new IntegerLowering(function,MethodRef.Open(entries[mode]),binder,types,calls:calls,effects:new ManagedCallEffects(calls),spec:spec,names:facts).Run();
            checks.True(lowered.Body is not null,mode+" 下降："+lowered.Failure);
            if(lowered.Body is not { } bodyResult) continue;
            checks.True(emitter.Emit([bodyResult]).Count==0,mode+" CIL 校验");
            var output=source.Method("Cases",mode+"Out"); output.Body=skeleton.Method(entries[mode]).Body;
            var core=source.Module.TypeSystem.Object.Resolve().Module;
            Mono.Cecil.TypeReference MapType(Mono.Cecil.TypeReference type)=>source.Module.ImportReference(source.Module.GetType(type.FullName) ?? core.GetType(type.FullName));
            foreach(var local in output.Body.Variables) local.VariableType=MapType(local.VariableType);
            foreach(var instruction in output.Body.Instructions) instruction.Operand=instruction.Operand switch
            {
                Mono.Cecil.MethodReference method=>source.Module.ImportReference(source.Module.GetType(method.DeclaringType.FullName).Methods.Single(m=>m.FullName==method.FullName)),
                Mono.Cecil.TypeReference type=>MapType(type),Mono.Cecil.ParameterDefinition parameter=>output.Parameters[parameter.Index],_=>instruction.Operand
            };
            var comparison=CilComparison.Compare(source.Method("Cases",mode),output);
            checks.True(comparison.Status==CilComparisonStatus.Match,mode+" 执行对照："+comparison);
        }
        foreach(var assembly in skeleton.Assemblies) assembly.Dispose();
    }
    private sealed class TouchMap(MethodDef touch):IBindingCodeMap
    { public ImmutableArray<BindingEntry> At(ulong address)=>address==10?[new(MethodRef.Open(touch),BindingEntryKind.Ordinary)]:[]; }
}
