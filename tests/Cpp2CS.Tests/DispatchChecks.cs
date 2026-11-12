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
internal static class DispatchChecks
{
    public const string Command = "dispatch";
    public static int Run()
    {
        var a = new Assertions(); var spec = InputCorpusChecks.Spec("arm64-v8a");
        var layouts = new FieldLayouts(spec, 8, 8); var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(), catalog);
        TypeDef Type(string name, string ns = "", string assembly = "test", bool value = false) => new() { Index=0, Assembly=assembly, Namespace=ns, Name=name, Token=0, Attributes=TypeAttributes.Public, IsValueType=value, IsEnum=false, Size=128, PackingSize=0, ClassSizeIsDefault=true };
        var integer = new DefinitionRef(Type("Int32", "System", "mscorlib.dll", true), []);
        var pointer = new DefinitionRef(Type("IntPtr", "System", "mscorlib.dll", true), []);
        MethodDef Method(TypeDef owner, string name, int slot, bool statics = false) => new() { Index=0, Owner=owner, Name=name, Token=0, Attributes=statics ? MethodAttributes.Static : MethodAttributes.Public | MethodAttributes.Virtual, ImplAttributes=0, Slot=slot, ReturnType=integer, Parameters=[new("v",integer,0,null,false)] };
        var obj=Type("Object","System","mscorlib.dll"); var objMethod=Method(obj,"Hash",2); obj.Methods=[objMethod]; obj.VTable=[null,null,new(objMethod,[],[])];
        var parent=Type("Parent"); parent.BaseType=new DefinitionRef(obj,[]); var virtualMethod=Method(parent,"Apply",4); var many=Method(parent,"Many",5); many.Parameters=Enumerable.Range(0,7).Select(i=>new ParameterDef("p"+i,integer,0,null,false)).ToArray(); parent.Methods=[virtualMethod,many];
        var child=Type("Child"); child.BaseType=new DefinitionRef(parent,[]); child.VTable=[null,null,new(objMethod,[],[]),null,new(virtualMethod,[],[]),new(many,[],[])];
        var del=Type("Delegate","System","mscorlib.dll");
        del.Fields=new[] { "invoke_impl", "method_code", "method", "m_target" }.Select((n,i)=> new FieldDef { Index=i, Owner=del, Name=n, Type=pointer, Offset=(int)spec.Layout.ObjectHeaderSize+i*8, Attributes=FieldAttributes.Public }).ToArray();
        var multi=Type("MulticastDelegate","System","mscorlib.dll"); multi.BaseType=new DefinitionRef(del,[]);
        var concrete=Type("Callback"); concrete.BaseType=new DefinitionRef(multi,[]); var invoke=Method(concrete,"Invoke",5); concrete.Methods=[invoke];
        void Check(TypeDef receiverType, int slot, bool mismatch, bool isDelegate, MethodDef? expected, bool wrongThis=false, bool stackInfo=false, int loaded=0, bool unnamed=false)
        {
            var t=new TermTable(); var b=new BlockIdentity(); var root=t.Atom(new EntryAtom(new(SlotKind.Integer)),64);
            var f=new FunctionBuilder(t,b,64,new(t.Atom(new RootAtom(AddressRoot.Frame),64))); f.Inputs.Add(new(new(SlotKind.Integer),root));
            var statements=new List<Statement>();
            Term Read(Term owner,long offset) { var readId=new ReadIdentity(); var readValue=t.Atom(new ResultAtom(readId),64); statements.Add(new MemoryRead(readId,t.Apply(new CoreOperator(CoreOperation.Add),64,owner,t.Constant(offset,64)),64,readValue)); return readValue; }
            TypeRef inputType=new DefinitionRef(receiverType,[]);
            if (loaded==1)
            {
                var holder=Type("Holder"); holder.Fields=[new FieldDef { Index=0, Owner=holder, Name="Receiver", Type=inputType,
                    Offset=(int)spec.Layout.ObjectHeaderSize, Attributes=FieldAttributes.Public }];
                inputType=new DefinitionRef(holder,[]);
                root=Read(root,spec.Layout.ObjectHeaderSize);
            }
            if (loaded==2) { inputType=new ArrayRef(inputType,1); root=Read(root,spec.Layout.ArrayDataStart); }
            if (unnamed) root=t.Unknown(64,new("test.receiver","接收者定义未知。"));
            Term target, info, self=root;
            if (isDelegate) { target=Read(root,del.Fields[0].Offset); self=Read(root,del.Fields[wrongThis?3:1].Offset); info=Read(root,del.Fields[2].Offset); }
            else { var klass=Read(root,spec.Layout.Field("Il2CppObject","klass").ByteOffset); target=Read(klass,spec.Layout.VtableStart+slot*spec.Layout.VtableSlotSize+spec.Layout.Field("VirtualInvokeData","methodPtr").ByteOffset); info=Read(klass,spec.Layout.VtableStart+(slot+(mismatch?1:0))*spec.Layout.VtableSlotSize+spec.Layout.Field("VirtualInvokeData","method").ByteOffset); }
            var id=new CallIdentity(); var result=t.Atom(new ResultAtom(id),64);
            var arguments=new List<SlotValue> { new(new(SlotKind.Integer),self) };
            for(int i=1;i<=(stackInfo?7:1);i++) arguments.Add(new(new(SlotKind.Integer,i),t.Constant(7,64)));
            var area=t.Atom(new RootAtom(AddressRoot.Frame),64);
            if(stackInfo) statements.Add(new MemoryWrite(new WriteIdentity(),area,64,info));
            else arguments.Add(new(new(SlotKind.Integer,2),info));
            statements.Add(new Call(id,new ComputedTarget(target),arguments.ToImmutableArray(),[new(new(SlotKind.Integer),result)],OutgoingArgumentArea:stackInfo?area:null));
            f.Blocks.Add(new(b,[],statements.ToImmutableArray(),new Return([])));
            var entry=Method(receiverType,"Caller",-1,true); entry.Parameters=[new("receiver",inputType,0,null,false)];
            var state=new StateQueries(); var naming=new ValueNamingQuery(state,calls,NamingFacts.Empty,spec,binder,binder.Entry(new(entry,[],[]),BindingEntryKind.Ordinary).Value);
            var locations=new ManagedLocationQuery(state,naming,layouts,spec); var query=new DispatchQuery(state,calls,naming,locations,binder,spec);
            var found=locations.CreateContext(f.Freeze()).Get(query,id);
            if (unnamed)
            {
                a.True(found.IsSuccess && found.Value.Why is { Code:"dispatch.target-unnamed", Cause:not null },"目标未命名独立归因并保留原因链");
                var codes=new List<string>(); for(var why=found.Value.Why;why is not null;why=why.Cause) codes.Add(why.Code);
                a.True(codes.Contains("naming.definition"),"未命名接收者的命名原因传到分派");
            }
            a.True(found.IsSuccess && found.Value.Method?.Method==expected && (expected is not null ? found.Value.Kind==(isDelegate?DispatchKind.Delegate:DispatchKind.Virtual) : found.Value.Kind==DispatchKind.Unresolved),$"{receiverType} 槽={slot} 错槽={mismatch} 错首参={wrongThis}：{found.Value}");
        }
        Check(child,4,false,false,virtualMethod);
        Check(child,4,false,false,virtualMethod,loaded:1);
        Check(child,4,false,false,virtualMethod,loaded:2);
        Check(child,4,false,false,null,unnamed:true);
        Check(child,4,true,false,null);
        Check(child,5,false,false,many,stackInfo:true);
        Check(obj,2,false,false,objMethod);
        Check(obj,4,false,false,null);
        Check(concrete,0,false,true,invoke);
        Check(concrete,0,false,true,null,true);
        return a.Finish("分派快速检查");
    }
}
