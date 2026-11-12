using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;
namespace Cpp2CS.Tests;
internal static class LocationChecks
{
    public const string Command = "locations";
    public static int Run()
    {
        var a = new Assertions(); var spec = InputCorpusChecks.Spec("arm64-v8a");
        var layouts = new FieldLayouts(spec, 8, 8); int header = (int)spec.Layout.ObjectHeaderSize;
        TypeDef Type(string name, bool value = false, int size = 8) => new() { Index=0, Assembly="test", Namespace="", Name=name, Token=0,
            Attributes=TypeAttributes.Public, IsValueType=value, IsEnum=false, PackingSize=0, ClassSizeIsDefault=true, Size=size };
        var integer = new DefinitionRef(new TypeDef { Index=0, Assembly="mscorlib.dll", Namespace="System", Name="Int32", Token=0,
            Attributes=TypeAttributes.Public, IsValueType=true, IsEnum=false }, []);
        FieldDef Field(TypeDef owner, string name, TypeRef type, int offset, bool statics = false) => new() { Index=0, Owner=owner, Name=name, Type=type, Offset=offset, Attributes=statics ? FieldAttributes.Static : FieldAttributes.Public };
        var inner=Type("Inner",true); var leaf=Field(inner,"Leaf",integer,4); inner.Fields=[leaf];
        var outer=Type("Outer",true,16); var nested=Field(outer,"Nested",new DefinitionRef(inner,[]),4); outer.Fields=[nested];
        var owner=Type("Owner",size:header+32); var data=Field(owner,"Data",integer,header); var aggregate=Field(owner,"Aggregate",new DefinitionRef(outer,[]),header+8); var global=Field(owner,"Global",integer,0,true); owner.Fields=[data,aggregate,global];
        var child=Type("Child",size:header+40); child.BaseType=new DefinitionRef(owner,[]);
        var binder=new MethodBinder(new(layouts),new Aapcs64());
        var catalog=RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion,spec.Layout.Triple,spec.Layout.DataModel);
        var calls=new CallNamingQuery(binder,new NamingChecks.Map([]),new NamingChecks.RuntimeMap(),catalog);
        void Check(TypeRef receiver, long offset, int width, FieldDef? expected, ManagedLocationKind kind, bool array=false, bool instance=false, bool statics=false, bool addressRoot=false)
        {
            var t=new TermTable(); var block=new BlockIdentity(); var frame=t.Atom(new RootAtom(AddressRoot.Frame),64); var image=t.Atom(new RootAtom(AddressRoot.Image),64);
            var root=t.Atom(new EntryAtom(new(SlotKind.Integer)),64);
            var function=new FunctionBuilder(t,block,64,new(frame)) { ImageBase=image }; function.Inputs.Add(new(new(SlotKind.Integer),root));
            var method=new MethodRef(new MethodDef { Index=0, Owner=instance ? ((DefinitionRef)receiver).Definition : owner, Name="Access", Token=0,
                Attributes=instance ? MethodAttributes.Public : MethodAttributes.Static, ImplAttributes=0, Slot=-1, ReturnType=integer,
                Parameters=instance ? [] : [new("value",receiver,0,null,false)] },[],[]);
            var statements=new List<Statement>(); var facts=NamingFacts.Empty;
            Term Add(Term x,long n)=>t.Apply(new CoreOperator(CoreOperation.Add),64,x,t.Constant(n,64));
            if(statics)
            {
                var id=new ReadIdentity(); var klass=t.Atom(new ResultAtom(id),64); statements.Add(new MemoryRead(id,Add(image,256),64,klass));
                var sid=new ReadIdentity(); root=t.Atom(new ResultAtom(sid),64); statements.Add(new MemoryRead(sid,Add(klass,spec.Layout.Field("Il2CppClass","static_fields").ByteOffset),64,root));
                facts=facts with { Slots=ImmutableDictionary<ulong,Outcome<MetadataEntity>>.Empty.Add(256,Outcome<MetadataEntity>.Success(new ClassEntity(new DefinitionRef(owner,[])))) };
            }
            Term address=Add(root,offset);
            if(array)
            {
                var index=t.Atom(new EntryAtom(new(SlotKind.Integer,1)),64); function.Inputs.Add(new(new(SlotKind.Integer,1),index));
                address=t.Apply(new CoreOperator(CoreOperation.Add),64,address,t.Apply(new CoreOperator(CoreOperation.ShiftLeft),64,index,t.Constant(2,64)));
            }
            function.Blocks.Add(new(block,[],statements.ToImmutableArray(),new Return([])));
            var f=function.Freeze(); var state=new StateQueries(); var names=new ValueNamingQuery(state,calls,facts,spec,binder,binder.Entry(method,BindingEntryKind.Ordinary).Value);
            var query=new ManagedLocationQuery(state,names,layouts,spec); var context=query.CreateContext(f); var result=context.Get(query,new(address,width));
            if(addressRoot)
            {
                var taken=context.Get(query.Addresses,address);
                a.True(taken.IsSuccess && taken.Value.Any(v=>v.Path.IsEmpty && v.Type.Equals(((ArrayRef)receiver).Element)),"结构体元素起点可取址，不要求读取宽度覆盖整体");
                var reverse=query.CreateContext(f); reverse.Get(query.Addresses,address);
                a.True(reverse.Get(query,new(address,width)).Value.Kind==kind,"先查询地址不改变读取视图");
            }
            a.True(result.IsSuccess && result.Value.Kind==kind && (expected is null || result.Value.Views.Any(v=>v.Path.LastOrDefault()?.Field==expected)), $"{receiver} + {offset} => {kind} {expected}");
            if(array) a.True(result.Value.Views[0].Index==function.Inputs[1].Value,"移位还原为元素下标");
        }
        Check(new DefinitionRef(owner,[]),header,32,data,ManagedLocationKind.InstanceField);
        Check(new DefinitionRef(child,[]),header,32,data,ManagedLocationKind.InstanceField);
        Check(new DefinitionRef(owner,[]),header+16,32,leaf,ManagedLocationKind.InstanceField);
        Check(new DefinitionRef(inner,[]),4,32,leaf,ManagedLocationKind.InstanceField,instance:true);
        Check(new ArrayRef(integer,1),spec.Layout.ArrayDataStart,32,null,ManagedLocationKind.ArrayElement,array:true);
        Check(new ArrayRef(integer,1),spec.Layout.Field("Il2CppArray","max_length").ByteOffset,32,null,ManagedLocationKind.ArrayLength);
        Check(new DefinitionRef(owner,[]),0,32,global,ManagedLocationKind.StaticField,statics:true);
        Check(new DefinitionRef(owner,[]),header+30,16,null,ManagedLocationKind.Unknown);
        Check(new ByRefRef(new DefinitionRef(outer,[])),0,8,null,ManagedLocationKind.Unknown);
        Check(new ArrayRef(new DefinitionRef(outer,[]),1),spec.Layout.ArrayDataStart,8,null,ManagedLocationKind.Unknown,addressRoot:true);
        void Cycle(bool conflict)
        {
            var node=Type("Node",size:header+16); var nodeType=new DefinitionRef(node,[]);
            node.Fields=[Field(node,"Next",conflict ? new ArrayRef(integer,1) : nodeType,header),Field(node,"Value",integer,header+8)];
            var t=new TermTable(); var entryBlock=new BlockIdentity(); var loop=new BlockIdentity(); var exit=new BlockIdentity();
            var frame=t.Atom(new RootAtom(AddressRoot.Frame),64); var input=t.Atom(new EntryAtom(new(SlotKind.Integer)),64);
            var mid=new MergeIdentity(); var receiver=t.Atom(new ResultAtom(mid),64); var rid=new ReadIdentity(); var next=t.Atom(new ResultAtom(rid),64);
            Term Add(long offset)=>t.Apply(new CoreOperator(CoreOperation.Add),64,receiver,t.Constant(offset,64));
            var builder=new FunctionBuilder(t,entryBlock,64,new(frame)); builder.Inputs.Add(new(new(SlotKind.Integer),input));
            builder.Blocks.Add(new(entryBlock,[],[],new Jump(loop)));
            builder.Blocks.Add(new(loop,[new(mid,receiver,[new(entryBlock,input),new(loop,next)])],[new MemoryRead(rid,Add(header),64,next)],new Branch(t.Constant(1,1),loop,exit)));
            builder.Blocks.Add(new(exit,[],[],new Return([])));
            var method=new MethodRef(new MethodDef { Index=0, Owner=node, Name="Walk", Token=0, Attributes=MethodAttributes.Static, ImplAttributes=0, Slot=-1,
                ReturnType=integer, Parameters=[new("node",nodeType,0,null,false)] },[],[]);
            var function=builder.Freeze(); var state=new StateQueries(); var names=new ValueNamingQuery(state,calls,NamingFacts.Empty,spec,binder,binder.Entry(method,BindingEntryKind.Ordinary).Value);
            var query=new ManagedLocationQuery(state,names,layouts,spec); var context=query.CreateContext(function);
            var result=context.Get(query,new(Add(header+8),32));
            a.True(result.IsSuccess && result.Value.Kind==(conflict ? ManagedLocationKind.Unknown : ManagedLocationKind.InstanceField),"引用字段读取与循环合流的静态类型");
        }
        Cycle(false); Cycle(true);
        return a.Finish("托管位置查询");
    }
}
