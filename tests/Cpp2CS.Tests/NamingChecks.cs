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
internal static class NamingChecks
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
        var survey = new NamingSurvey(calls,new Decoder(new ClassEntity(reference))); survey.Observe(function); var facts = survey.Finish();
        var names = new ValueNamingQuery(state,calls,facts,spec,binder); c = names.CreateContext(function);
        a.True(c.Get(calls,managed.Identity).Value is { Kind:CallKind.Managed,Candidates.Candidates.Length:2 },"托管调用保留全部候选");
        a.True(c.Get(calls,init.Identity).Value is { Kind:CallKind.Runtime,Operation.Name:"InitializeMetadata" } named && named.Inputs!["slot"].Source is TermSource source && source.Term==slot,"运行时操作及命名实参");
        a.True(c.Get(names,klass).Value is { Name:EntityName { Entity:ClassEntity } },"槽读取命名成类");
        a.True(c.Get(names,statics).Value is { Name:FieldName { Field:"Il2CppClass.static_fields" } },"规格静态字段块");
        a.True(c.Get(names,forwarded).Value==c.Get(names,klass).Value,"经帧转发保留名字");
        a.True(c.Get(names,t.Unknown(64,new("test","未知"))).Value.Kind==ValueKind.Unnamed,"未知定义不猜名字");
        a.True(facts.Flags[200].IsFlag,"初始化后写 1 的全局字节");
        survey.Incomplete(); a.True(!survey.Finish().Flags[200].IsFlag,"不完整普查不能证明标志");
        FlagEvidence Evidence(IEnumerable<Statement> statements)
        {
            var changed = new FunctionBuilder(t,b,64,new(frame)) { ImageBase=image };
            changed.Blocks.Add(function.Blocks[0] with { Statements=statements.ToImmutableArray() });
            changed.Blocks.Add(function.Blocks[1]);
            var scan = new NamingSurvey(calls,new Decoder(new ClassEntity(reference))); scan.Observe(changed.Freeze());
            return scan.Finish().Flags[200];
        }
        var statements = function.Blocks[0].Statements;
        a.True(!Evidence(statements.Where(s=>s!=init).Append(init)).IsFlag,"写 1 在初始化之前拒绝");
        a.True(!Evidence(statements.Select(s=>s is MemoryWrite w && w.Address==flag ? w with { Value=t.Constant(2,8) } : s)).IsFlag,"写非 1 拒绝");
        a.True(!Evidence(statements.Append(new Call(new(),new ComputedTarget(flag),[],[]))).IsFlag,"标志地址逃逸拒绝");
        a.True(!Evidence(statements.Append(new MemoryWrite(new(),Add(image,199),16,t.Constant(0,16)))).IsFlag,"邻接宽写覆盖标志拒绝");
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
        return a.Finish("命名查询");
    }
}
