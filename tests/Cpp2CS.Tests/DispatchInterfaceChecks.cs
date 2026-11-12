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
internal static class DispatchInterfaceChecks
{
    public const string Command = "dispatch-interface";
    public static int Run()
    {
        var a = new Assertions(); var spec = InputCorpusChecks.Spec("arm64-v8a");
        var layouts = new FieldLayouts(spec,8,8); var binder = new MethodBinder(new(layouts),new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion,spec.Layout.Triple,spec.Layout.DataModel);
        var runtime = catalog.Functions.Single(f => f.Operation.Name == "LookupInterfaceData");
        var calls = new CallNamingQuery(binder,new NamingChecks.Map([]),new NamingChecks.RuntimeMap(runtime),catalog);
        TypeDef Type(string name, bool itf = false) => new() { Index=0,Assembly="test",Namespace="",Name=name,Token=0,Attributes=TypeAttributes.Public | (itf?TypeAttributes.Interface:0),IsValueType=false,IsEnum=false };
        var obj = Type("Object"); var itf = Type("IAction",true); var other = Type("IOther",true);
        var reference = new DefinitionRef(obj,[]);
        MethodDef Method(TypeDef owner, string name, bool statics) => new() { Index=0,Owner=owner,Name=name,Token=0,Attributes=statics?MethodAttributes.Static:MethodAttributes.Public|MethodAttributes.Virtual,ImplAttributes=0,Slot=0,ReturnType=reference,Parameters=[] };
        var method = Method(itf,"Apply",false); itf.Methods=[method];
        var caller = Method(obj,"Caller",true); caller.Parameters=[new("o",reference,0,null,false)];
        void Check(bool slowOnly, bool wrongInterface, bool wrongSlot, bool loop = false, bool wrongStep = false, bool wrongPair = false, bool noEntry = false, bool spill = false)
        {
            var t = new TermTable(); var entry = new BlockIdentity(); var fast = new BlockIdentity(); var slow = new BlockIdentity(); var end = new BlockIdentity(); var scan = new BlockIdentity(); var advance = new BlockIdentity();
            var receiver = t.Atom(new EntryAtom(new(SlotKind.Integer)),64);
            var f = new FunctionBuilder(t,entry,64,new(t.Atom(new RootAtom(AddressRoot.Frame),64))); f.Inputs.Add(new(new(SlotKind.Integer),receiver));
            Term Add(Term x,long n) => t.Apply(new CoreOperator(CoreOperation.Add),64,x,t.Constant(unchecked((ulong)n),64));
            Term Read(List<Statement> list,Term address,int width=64) { var id = new ReadIdentity(); var term=t.Atom(new ResultAtom(id),width); list.Add(new MemoryRead(id,address,width,term)); return term; }
            var start = new List<Statement>(); var image=t.Atom(new RootAtom(AddressRoot.Image),64);
            var iface=Read(start,Add(image,128)); var compared=wrongInterface?Read(start,Add(image,256)):iface;
            var klass=Read(start,Add(receiver,spec.Layout.Field("Il2CppObject","klass").ByteOffset));
            var table=Read(start,Add(klass,spec.Layout.Field("Il2CppClass","interfaceOffsets").ByteOffset));
            var pairId = new MergeIdentity(); var cursor = t.Atom(new ResultAtom(pairId),64);
            var pair=loop ? cursor : Add(table,spec.Layout.Record("Il2CppRuntimeInterfaceOffsetPair").Size);
            var scanStatements = loop ? new List<Statement>() : start;
            var pairInterface=Read(scanStatements,Add(pair,spec.Layout.Field("Il2CppRuntimeInterfaceOffsetPair","interfaceType").ByteOffset));
            var fastStatements = new List<Statement>();
            var offset=Read(fastStatements,Add(wrongPair ? Add(pair,spec.Layout.Record("Il2CppRuntimeInterfaceOffsetPair").Size) : pair,spec.Layout.Field("Il2CppRuntimeInterfaceOffsetPair","offset").ByteOffset),32);
            var extended=t.Apply(new CoreOperator(CoreOperation.SignExtend),64,offset);
            var scaled=t.Apply(new CoreOperator(CoreOperation.Multiply),64,extended,t.Constant(spec.Layout.VtableSlotSize,64));
            var address=t.Apply(new CoreOperator(CoreOperation.Add),64,Add(klass,spec.Layout.VtableStart+(wrongSlot?spec.Layout.VtableSlotSize:0)),scaled);
            var slowId=new CallIdentity(); var slowResult=t.Atom(new ResultAtom(slowId),64);
            var slowCall=new Call(slowId,new ImageFunction(100),[new(new(SlotKind.Integer),receiver),new(new(SlotKind.Integer,1),iface),new(new(SlotKind.Integer,2),t.Constant(0,64))],[new(new(SlotKind.Integer),slowResult)]);
            var mergeId=new MergeIdentity(); var merged=t.Atom(new ResultAtom(mergeId),64);
            var endStatements=new List<Statement>(); var data=slowOnly?slowResult:merged;
            if (spill) data = Read(endStatements, Add(t.Atom(new RootAtom(AddressRoot.Frame),64), -16));
            var target=Read(endStatements,Add(data,spec.Layout.Field("VirtualInvokeData","methodPtr").ByteOffset));
            var info=Read(endStatements,Add(data,spec.Layout.Field("VirtualInvokeData","method").ByteOffset));
            var callId=new CallIdentity(); endStatements.Add(new Call(callId,new ComputedTarget(target),[new(new(SlotKind.Integer),receiver),new(new(SlotKind.Integer,1),info)],[new(new(SlotKind.Integer),t.Atom(new ResultAtom(callId),64))]));
            var equal = t.Apply(new CoreOperator(CoreOperation.Equal),1,
                t.Apply(new CoreOperator(CoreOperation.Add),64,pairInterface,t.Apply(new CoreOperator(CoreOperation.Not),64,compared)),t.Constant(ulong.MaxValue,64));
            f.Blocks.Add(new(entry,[],start.ToImmutableArray(),slowOnly?new Jump(slow):loop?new Jump(scan):new Branch(equal,fast,slow)));
            if (loop)
            {
                f.Blocks.Add(new(scan,[new(pairId,cursor,[new(entry,table),new(advance,Add(cursor,wrongStep?1:spec.Layout.Record("Il2CppRuntimeInterfaceOffsetPair").Size))])],scanStatements.ToImmutableArray(),new Branch(equal,fast,advance)));
                f.Blocks.Add(new(advance,[],[new Call(new(),new ImageFunction(200),[],[])],new Branch(t.Atom(new EntryAtom(new(SlotKind.Integer,3)),1),scan,slow)));
            }
            if (!slowOnly) f.Blocks.Add(new(fast,[],fastStatements.ToImmutableArray(),new Jump(end)));
            f.Blocks.Add(new(slow,[],spill ? [slowCall, new MemoryWrite(new(), Add(t.Atom(new RootAtom(AddressRoot.Frame),64), -16), 64, slowResult)] : [slowCall],new Jump(end)));
            f.Blocks.Add(new(end,slowOnly?[]:[new Merge(mergeId,merged,[new(fast,address),new(slow,slowResult)])],endStatements.ToImmutableArray(),new Return([])));
            var facts=NamingFacts.Empty with { Slots=ImmutableDictionary<ulong,Outcome<MetadataEntity>>.Empty.Add(128,Outcome<MetadataEntity>.Success(new ClassEntity(new DefinitionRef(itf,[])))).Add(256,Outcome<MetadataEntity>.Success(new ClassEntity(new DefinitionRef(other,[])))) };
            var state=new StateQueries(); var names=new ValueNamingQuery(state,calls,facts,spec,binder,noEntry?null:binder.Entry(new(caller,[],[]),BindingEntryKind.Ordinary).Value);
            var locations=new ManagedLocationQuery(state,names,layouts,spec); var q=new DispatchQuery(state,calls,names,locations,binder,spec);
            var result=locations.CreateContext(f.Freeze()).Get(q,callId);
            bool success=!wrongInterface&&!wrongSlot&&!wrongStep&&!wrongPair;
            a.True(result.IsSuccess && (success?result.Value.Kind==DispatchKind.Interface && result.Value.Method?.Method==method:result.Value.Kind==DispatchKind.Unresolved),$"接口 slow={slowOnly} wrongInterface={wrongInterface} wrongSlot={wrongSlot} loop={loop} wrongStep={wrongStep} wrongPair={wrongPair}: {result.Value}");
            if (slowOnly) a.True(result.IsSuccess && result.Value is { Kind: DispatchKind.Interface, Shape: TargetShape.ReadFromCallResult, Slot: 0 }
                && result.Value.Receiver == receiver && result.Value.StaticType is DefinitionRef staticType && staticType.Definition == itf && staticType.Arguments.Count == 0, "直接查找结果保留对象、接口和常量槽：" + result.Value);
        }
        Check(false,false,false); Check(false,true,false); Check(false,false,true); Check(true,false,false);
        Check(false,false,false,true); Check(false,false,false,true,true); Check(false,false,false,true,false,true);
        Check(false,false,false,true,false,false,true);
        Check(true,false,false,noEntry:true); Check(true,false,false,spill:true);
        foreach (var swapped in new[] { false, true })
        {
            var t = new TermTable(); var start = new BlockIdentity(); var left = new BlockIdentity(); var right = new BlockIdentity(); var end = new BlockIdentity();
            var f = new FunctionBuilder(t,start,64,new(t.Atom(new RootAtom(AddressRoot.Frame),64)));
            var receiver = t.Atom(new EntryAtom(new(SlotKind.Integer)),64);
            var second = t.Atom(new EntryAtom(new(SlotKind.Integer,1)),64);
            var image=t.Atom(new RootAtom(AddressRoot.Image),64);
            var interfaceRead=new ReadIdentity(); var iface=t.Atom(new ResultAtom(interfaceRead),64);
            Term Add(Term x,long n) => t.Apply(new CoreOperator(CoreOperation.Add),64,x,t.Constant(unchecked((ulong)n),64));
            f.Blocks.Add(new(start,[],[new MemoryRead(interfaceRead,Add(image,128),64,iface)],new Branch(t.Atom(new EntryAtom(new(SlotKind.Integer,2)),1),left,right)));
            (Term Pointer,Term Information) Arm(BlockIdentity block,Term self)
            {
                var id=new CallIdentity(); var data=t.Atom(new ResultAtom(id),64);
                var pointerId=new ReadIdentity(); var pointer=t.Atom(new ResultAtom(pointerId),64);
                var infoId=new ReadIdentity(); var info=t.Atom(new ResultAtom(infoId),64);
                f.Blocks.Add(new(block,[],[
                    new Call(id,new ImageFunction(100),[new(new(SlotKind.Integer),self),new(new(SlotKind.Integer,1),iface),new(new(SlotKind.Integer,2),t.Constant(0,64))],[new(new(SlotKind.Integer),data)]),
                    new MemoryRead(pointerId,Add(data,spec.Layout.Field("VirtualInvokeData","methodPtr").ByteOffset),64,pointer),
                    new MemoryRead(infoId,Add(data,spec.Layout.Field("VirtualInvokeData","method").ByteOffset),64,info)],new Jump(end)));
                return (pointer,info);
            }
            var leftValues=Arm(left,receiver); var rightValues=Arm(right,second);
            var merges=new List<Merge>();
            Term Join(Term leftValue,Term rightValue)
            {
                var id=new MergeIdentity(); var value=t.Atom(new ResultAtom(id),64);
                merges.Add(new(id,value,[new(left,leftValue),new(right,rightValue)])); return value;
            }
            var target=Join(leftValues.Pointer,rightValues.Pointer); var information=Join(leftValues.Information,rightValues.Information);
            var self=Join(swapped?second:receiver,swapped?receiver:second);
            var callId=new CallIdentity();
            f.Blocks.Add(new(end,merges.ToImmutableArray(),[new Call(callId,new ComputedTarget(target),[new(new(SlotKind.Integer),self),new(new(SlotKind.Integer,1),information)],[new(new(SlotKind.Integer),t.Atom(new ResultAtom(callId),64))])],new Return([])));
            var facts=NamingFacts.Empty with { Slots=ImmutableDictionary<ulong,Outcome<MetadataEntity>>.Empty.Add(128,Outcome<MetadataEntity>.Success(new ClassEntity(new DefinitionRef(itf,[])))) };
            var state=new StateQueries(); var names=new ValueNamingQuery(state,calls,facts,spec,binder);
            var locations=new ManagedLocationQuery(state,names,layouts,spec); var q=new DispatchQuery(state,calls,names,locations,binder,spec);
            var result=locations.CreateContext(f.Freeze()).Get(q,callId);
            a.True(result.IsSuccess && (swapped?result.Value.Kind==DispatchKind.Unresolved:result.Value.Kind==DispatchKind.Interface && result.Value.Receiver==self),"双接收者逐边对应："+swapped);
        }
        return a.Finish("接口分派快速检查");
    }
}
