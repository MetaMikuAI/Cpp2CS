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
internal static partial class NamingChecks
{
    public const string Command = "naming";
    internal sealed class RuntimeMap(RuntimeFunction? function = null) : IRuntimeFunctionMap
    { public RuntimeFunction? Find(CallTarget target) => function; }
    internal sealed class Map(ImmutableArray<BindingEntry> entries) : IBindingCodeMap
    { public ImmutableArray<BindingEntry> At(ulong address) => address == 10 ? entries : []; }
    private sealed class Decoder(MetadataEntity entity) : IMetadataSlotDecoder
    { public Outcome<MetadataEntity> Decode(ulong address) => Outcome<MetadataEntity>.Success(entity); }
    public static int Run()
    {
        var a = new Assertions(); var spec = InputCorpusChecks.Spec("arm64-v8a");
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var runtime = catalog.Functions.First(f => f.Operation.Name == "InitializeMetadata" && f.Signature is not null);
        var binder = new MethodBinder(new(new FieldLayouts(spec, 8, 8)), new Aapcs64());
        var type = new TypeDef { Index=0, Assembly="test", Namespace="", Name="Owner", Token=0, Attributes=TypeAttributes.Public, IsValueType=false, IsEnum=false };
        var reference = new DefinitionRef(type, []);
        var method = new MethodRef(new MethodDef { Index=0, Owner=type, Name="Apply", Token=0, Attributes=MethodAttributes.Static, ImplAttributes=0, Slot=-1, ReturnType=reference, Parameters=[] }, [], []);
        var calls = new CallNamingQuery(binder, new Map([new(method, BindingEntryKind.Ordinary),new(method, BindingEntryKind.Ordinary)]), new RuntimeMap(runtime), catalog);
        var t = new TermTable(); var b = new BlockIdentity(); var frame = t.Atom(new RootAtom(AddressRoot.Frame),64); var image = t.Atom(new RootAtom(AddressRoot.Image),64);
        Term Add(Term root, long offset) => t.Apply(new CoreOperator(CoreOperation.Add),64,root,t.Constant(offset,64));
        var slot = Add(image,100); var flag = Add(image,200);
        var id = new ReadIdentity(); var klass = t.Atom(new ResultAtom(id),64);
        var fid = new ReadIdentity(); var forwarded = t.Atom(new ResultAtom(fid),64);
        var sid = new ReadIdentity(); var statics = t.Atom(new ResultAtom(sid),64);
        var resultId = new CallIdentity(); var result = t.Atom(new ResultAtom(resultId),64);
        var managed = new Call(resultId,new ImageFunction(10),[new(new(SlotKind.Integer),t.Constant(0,64))],[new(new(SlotKind.Integer),result)]);
        var initIdentity = new CallIdentity();
        var init = new Call(initIdentity,new ImageFunction(20),[new(new(SlotKind.Integer),slot)],[new(new(SlotKind.Integer),t.Atom(new ResultAtom(initIdentity),64))]);
        var flagId = new ReadIdentity(); var flagValue = t.Atom(new ResultAtom(flagId),8);
        var exit = new BlockIdentity();
        var builder = new FunctionBuilder(t,b,64,new(frame)) { ImageBase=image };
        builder.Blocks.Add(new(b,[],[managed,init,new MemoryWrite(new(),flag,8,t.Constant(1,8)),new MemoryRead(flagId,flag,8,flagValue),
            new MemoryRead(id,slot,64,klass),new MemoryWrite(new(),frame,64,klass),new MemoryRead(fid,frame,64,forwarded),
            new MemoryRead(sid,Add(forwarded,spec.Layout.Field("Il2CppClass","static_fields").ByteOffset),64,statics)],new Branch(t.Slice(flagValue,0,1),exit,exit)));
        builder.Blocks.Add(new(exit,[],[],new Return([])));
        var function = builder.Freeze(); a.True(ExitChecker.Check(function).IsValid,"合成输入通过原生契约检查"); var state = new StateQueries(); var c = state.CreateContext(function);
        var survey = new NamingSurvey(calls,new Decoder(new ClassEntity(reference)),new InputMemoryImage(),binder,spec); survey.Observe(function); var facts = survey.Finish();
        var names = new ValueNamingQuery(state,calls,facts,spec,binder); c = names.CreateContext(function);
        a.True(c.Get(calls,managed.Identity).Value is { Kind:CallKind.Managed,Candidates.Candidates.Length:2 },"托管调用保留全部候选");
        a.True(c.Get(calls,init.Identity).Value is { Kind:CallKind.Runtime,Operation.Name:"InitializeMetadata" } named && named.Inputs!["slot"].Source is TermSource source && source.Term==slot,"运行时操作及命名实参");
        a.True(c.Get(names,klass).Value is { Name:EntityName { Entity:ClassEntity } },"槽读取命名成类");
        a.True(c.Get(names,statics).Value is { Name:FieldName { Field:"Il2CppClass.static_fields" } },"规格静态字段块");
        a.True(c.Get(names,forwarded).Value==c.Get(names,klass).Value,"经帧转发保留名字");
        a.True(c.Get(names,t.Unknown(64,new("test","未知"))).Value.Kind==ValueKind.Unnamed,"未知定义不猜名字");
        a.True(!facts.Flags[200].IsFlag,"没有对应测试的置位不构成方法初始化模板");
        survey.Incomplete(); a.True(!survey.Finish().Complete && !survey.Finish().Flags[200].IsFlag,"观察范围状态不替代函数内模板判定");
        var mergeId = new MergeIdentity(); var mergeValue=t.Atom(new ResultAtom(mergeId),64); var loop=new BlockIdentity();
        var merged = new FunctionBuilder(t,b,64,new(frame)) { ImageBase=image };
        merged.Blocks.Add(function.Blocks[0] with { End=new Jump(loop) });
        merged.Blocks.Add(new(loop,[new(mergeId,mergeValue,[new(b,klass),new(loop,mergeValue)])],[],new Branch(t.Constant(1,1),loop,exit)));
        merged.Blocks.Add(function.Blocks[1]);
        a.True(names.CreateContext(merged.Freeze()).Get(names,mergeValue).Value.Name is EntityName,"循环合流的外部一致名字");
        foreach (var mode in new[] { 0,1,2 })
        {
            bool conflict=mode==1;
            var terms=new TermTable(); var block=new BlockIdentity();
            var value=mode==2?terms.Undefined(64):terms.Atom(new EntryAtom(new(SlotKind.Integer)),64);
            var klassInput=conflict?value:terms.Atom(new EntryAtom(new(SlotKind.Integer,1)),64);
            var operation=catalog.Functions.First(f=>f.Operation.Name=="IsInstance" && f.Signature is not null);
            var callQuery=new CallNamingQuery(binder,new Map([]),new RuntimeMap(operation),catalog);
            var callId=new CallIdentity();
            var graph=new FunctionBuilder(terms,block,64,new(terms.Atom(new RootAtom(AddressRoot.Frame),64)));
            graph.Blocks.Add(new(block,[],[new Call(callId,new ImageFunction(1),[new(new(SlotKind.Integer),value),new(new(SlotKind.Integer,1),klassInput)],
                [new(new(SlotKind.Integer),terms.Atom(new ResultAtom(callId),64))])],new Return([])));
            var memory=new StateQueries(); var query=new ValueNamingQuery(memory,callQuery,NamingFacts.Empty,spec,binder);
            var context=query.CreateContext(graph.Freeze()); var found=context.Get(query,value);
            a.True(found.IsSuccess && (mode!=0?found.Value.Kind==ValueKind.Unnamed:found.Value.Kind==ValueKind.ManagedReference),"运行时输入的种类、冲突与未定义位："+mode);
            if (!conflict) a.True(context.Get(query,klassInput).Value.Record=="Il2CppClass","运行时输入的类指针种类");
        }
        LoadedValues(a, spec);
        SpecificationValues(a, spec);
        SharedReferenceLoop(a, spec);
        return a.Finish("命名查询");
    }
    private static void LoadedValues(Assertions a, RuntimeSpec spec)
    {
        var layouts = new FieldLayouts(spec, 8, 8); var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var operation=catalog.Functions.First(f=>f.Operation.Name=="IsInstance" && f.Signature is not null);
        var calls = new CallNamingQuery(binder, new Map([]), new RuntimeMap(operation), catalog);
        TypeDef Type(string name, bool value = false, string ns = "", string assembly = "test") => new()
        { Index=0, Assembly=assembly, Namespace=ns, Name=name, Token=0, Attributes=TypeAttributes.Public,
            IsValueType=value, IsEnum=false, Size=128, PackingSize=0, ClassSizeIsDefault=true };
        DefinitionRef Primitive(string name) => new(Type(name, true, "System", "mscorlib.dll"), []);
        var integer=Primitive("Int32"); var floating=Primitive("Single"); var pointer=Primitive("IntPtr");
        var text=new DefinitionRef(Type("String", false, "System", "mscorlib.dll"), []);
        var item=Type("Item"); var itemType=new DefinitionRef(item, []); var array=new ArrayRef(itemType, 1);
        int header=(int)spec.Layout.ObjectHeaderSize;
        FieldDef Field(TypeDef owner, string name, TypeRef type, int offset, bool statics=false) => new()
        { Index=offset, Owner=owner, Name=name, Type=type, Offset=offset, Attributes=statics ? FieldAttributes.Static : FieldAttributes.Public };
        var textCount = Field(text.Definition, "Count", integer, header); text.Definition.Fields = [textCount];
        item.Fields=[Field(item,"Value",integer,header)];
        var nested=Type("Nested",true); nested.Size=8; nested.Fields=[Field(nested,"Item",itemType,0)];
        var owner=Type("Owner"); var ownerType=new DefinitionRef(owner, []);
        owner.Fields=[Field(owner,"First",itemType,header),Field(owner,"Second",itemType,header+8),
            Field(owner,"Number",integer,header+16),Field(owner,"Fraction",floating,header+20),
            Field(owner,"Pointer",pointer,header+24),Field(owner,"Items",array,header+32),
            Field(owner,"Text",text,header+40),Field(owner,"Nested",new DefinitionRef(nested,[]),header+48),
            Field(owner,"Global",itemType,0,true),Field(owner,"RuntimeItem",itemType,header+56)];
        var t=new TermTable(); var block=new BlockIdentity(); var left=new BlockIdentity(); var right=new BlockIdentity(); var join=new BlockIdentity();
        var frame=t.Atom(new RootAtom(AddressRoot.Frame),64); var image=t.Atom(new RootAtom(AddressRoot.Image),64);
        var input=t.Atom(new EntryAtom(new(SlotKind.Integer)),64); var elements=t.Atom(new EntryAtom(new(SlotKind.Integer,1)),64);
        var textParameter=t.Atom(new EntryAtom(new(SlotKind.Integer,2)),64);
        var builder=new FunctionBuilder(t,block,64,new(frame)) { ImageBase=image };
        builder.Inputs.Add(new(new(SlotKind.Integer,2),textParameter));
        builder.Inputs.Add(new(new(SlotKind.Integer),input)); builder.Inputs.Add(new(new(SlotKind.Integer,1),elements));
        var statements=new List<Statement>();
        Term Read(Term root,long offset,int width=64)
        {
            var id=new ReadIdentity(); var result=t.Atom(new ResultAtom(id),width);
            statements.Add(new MemoryRead(id,t.Apply(new CoreOperator(CoreOperation.Add),64,root,t.Constant(offset,64)),width,result)); return result;
        }
        var first=Read(input,header); var second=Read(input,header+8); var number=Read(input,header+16,32);
        var fraction=Read(input,header+20,32); var native=Read(input,header+24); var items=Read(input,header+32);
        var textHeader=Read(textParameter,0);
        var textValue=Read(input,header+40); var textLength=Read(textValue,header,32);
        var leaf=Read(input,header+48); var element=Read(elements,spec.Layout.ArrayDataStart);
        var index=t.Unknown(64,new("test.index","数组下标。"));
        var indexed=t.Apply(new CoreOperator(CoreOperation.Add),64,elements,
            t.Apply(new CoreOperator(CoreOperation.ShiftLeft),64,index,t.Constant(3,64)));
        var dynamicElement=Read(indexed,spec.Layout.ArrayDataStart);
        var chained=Read(first,header,32); var partial=Read(input,header+16,16);
        var klass=Read(image,256); var statics=Read(klass,spec.Layout.Field("Il2CppClass","static_fields").ByteOffset); var global=Read(statics,0);
        var used=Read(input,header+56); var runtimeCall=new CallIdentity();
        statements.Add(new Call(runtimeCall,new ImageFunction(98),[new(new(SlotKind.Integer),used),new(new(SlotKind.Integer,1),t.Constant(0,64))],
            [new(new(SlotKind.Integer),t.Atom(new ResultAtom(runtimeCall),64))]));
        var unknownCall=new CallIdentity(); statements.Add(new Call(unknownCall,new ImageFunction(99),[],[]));
        var reloaded=Read(input,header);
        var mergeId=new MergeIdentity(); var merged=t.Atom(new ResultAtom(mergeId),64);
        builder.Blocks.Add(new(block,[],statements.ToImmutableArray(),new Branch(t.Unknown(1,new("test.condition","分支输入")),left,right)));
        builder.Blocks.Add(new(left,[],[],new Jump(join))); builder.Blocks.Add(new(right,[],[],new Jump(join)));
        builder.Blocks.Add(new(join,[new(mergeId,merged,[new(left,first),new(right,second)])],[],new Return([])));
        var method=new MethodRef(new MethodDef { Index=0, Owner=owner, Name="Read", Token=0, Attributes=MethodAttributes.Static,
            ImplAttributes=0, Slot=-1, ReturnType=integer, Parameters=[new("owner",ownerType,0,null,false),new("items",array,0,null,false),new("text",text,0,null,false)] },[],[]);
        var facts=NamingFacts.Empty with { Slots=ImmutableDictionary<ulong,Outcome<MetadataEntity>>.Empty
            .Add(256,Outcome<MetadataEntity>.Success(new ClassEntity(ownerType))) };
        var state=new StateQueries(); var names=new ValueNamingQuery(state,calls,facts,spec,binder,binder.Entry(method,BindingEntryKind.Ordinary).Value);
        var locations=new ManagedLocationQuery(state,names,layouts,spec); var function=builder.Freeze();
        foreach (bool typesFirst in new[] { false,true })
        {
            var c=names.CreateContext(function);
            if (typesFirst) a.True(c.Get(locations.Types,chained).Value?.Type==integer,"先求读取类型可收敛");
            var one=c.Get(names,first); var two=c.Get(names,second);
            a.True(one.IsSuccess && one.Value is { Kind:ValueKind.ManagedReference, Record:"Il2CppObject", Name:LoadedName { StaticType:var firstType } } && firstType==itemType,"实例字段对象按声明类型命名");
            a.True(c.Get(names,used).Value.Name is RuntimeInputName,"既有运行时实参名字优先于托管读取补名");
            a.True(c.Get(names,element).Value is { Kind:ValueKind.ManagedReference, Name:LoadedName },"数组元素对象按声明类型命名");
            a.True(c.Get(names,dynamicElement).Value is { Kind:ValueKind.ManagedReference, Name:LoadedName },"变动下标数组元素按声明类型命名");
            a.True(c.Get(names,global).Value is { Kind:ValueKind.ManagedReference, Name:LoadedName },"静态字段对象按声明类型命名");
            a.True(c.Get(names,number).Value is { Kind:ValueKind.Integer, Record:null, Name:LoadedName },"整数字段的值种类");
            a.True(c.Get(names,fraction).Value is { Kind:ValueKind.Floating, Record:null },"浮点字段的值种类");
            a.True(c.Get(names,native).Value is { Kind:ValueKind.NativePointer, Record:null },"原生指针字段的值种类");
            a.True(c.Get(names,items).Value.Record=="Il2CppArray" && c.Get(names,textValue).Value.Record=="Il2CppString","数组和字符串读取的运行时结构");
            var textLocation=c.Get(locations,new(t.Apply(new CoreOperator(CoreOperation.Add),64,textValue,t.Constant(header,64)),32));
            a.True(c.Get(names,textLength).Value.Name is FieldName && textLocation.Value is { Kind:ManagedLocationKind.InstanceField, Views:[var textView] }
                && textView.Path[^1].Field==textCount,"规格字段名字不遮蔽同一范围内真实的托管字段声明");
            a.True(c.Get(names,textParameter).Value is { Record:"Il2CppObject", Name:ParameterName } &&
                c.Get(names,textHeader).Value.Name is FieldName { Record:"Il2CppObject", Field:"Il2CppObject.klass" },"签名字符串及其规格字段名字保持不变");
            a.True(c.Get(names,leaf).Value.StaticType==itemType,"结构体字段读取按叶子声明类型");
            a.True(c.Get(names,chained).Value.Kind==ValueKind.Integer,"连续字段读取有底递归");
            a.True(one.Value.Name!=two.Value.Name && c.Get(names,merged).Value is { Kind:ValueKind.ManagedReference, Name:ReferenceValueName, StaticType:var mergedType }
                && mergedType==itemType,"不同字段的引用读取合流有独立身份与公共类型");
            a.True(!names.SameValue(c, merged, first).Value && !names.SameValue(c, merged, second).Value,"公共类型不证明合流等于任一输入");
            a.True(one.Value.Name!=c.Get(names,reloaded).Value.Name,"可能改写后的读取保留不同身份");
            a.True(names.FixedValue(c, first).Value is LoadedName && !names.SameValue(c, first, reloaded).Value,
                "完整读取的定义名字保留内存版本，不同版本的可变字段不等值");
            a.True(c.Get(names,partial).Value.Kind==ValueKind.Unnamed,"部分整数读取不冒充整体读取");
            a.True(c.Get(names,statics).Value.Name is FieldName && c.Get(names,klass).Value.Name is EntityName,"既有规格和实体名字优先");
        }
    }

}
