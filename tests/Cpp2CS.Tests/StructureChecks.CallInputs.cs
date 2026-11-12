using System.Reflection;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Structure;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Tests;
internal static partial class StructureChecks
{
    private static void SignatureBeforeForwarding(Assertions checks)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var binder = new MethodBinder(new(new FieldLayouts(spec, 8, 8)), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var owner = new TypeDef { Index=0, Assembly="test", Namespace="", Name="Owner", Token=0, Attributes=TypeAttributes.Public, IsValueType=false, IsEnum=false };
        var integer = new TypeDef { Index=1, Assembly="mscorlib.dll", Namespace="System", Name="Int32", Token=0, Attributes=TypeAttributes.Public, IsValueType=true, IsEnum=false };
        var empty = new TypeDef { Index=2, Assembly="mscorlib.dll", Namespace="System", Name="Void", Token=0, Attributes=TypeAttributes.Public, IsValueType=true, IsEnum=false };
        foreach (bool required in new[] { false, true })
        {
            var method = MethodRef.Open(new MethodDef { Index=0, Owner=owner, Name="Observe", Token=0, Attributes=MethodAttributes.Public|MethodAttributes.Static,
                ImplAttributes=0, Slot=-1, ReturnType=new DefinitionRef(empty,[]), Parameters=required ? [new("value",new ByRefRef(new DefinitionRef(integer,[])),0,null,false)] : [] });
            var calls = new CallNamingQuery(binder,new NamingChecks.Map([new(method,BindingEntryKind.Ordinary)]),new NamingChecks.RuntimeMap(),catalog);
            var t = new TermTable(); var entry = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame),64); var image=t.Atom(new RootAtom(AddressRoot.Image),64);
            var f = new FunctionBuilder(t,entry,64,new(frame)){ImageBase=image};
            var id=new CallIdentity(); var readId=new ReadIdentity(); var value=t.Atom(new ResultAtom(readId),32);
            f.Blocks.Add(new(entry,[],[
                new MemoryWrite(new(),frame,32,t.Constant(37,32)),
                new MemoryWrite(new(),image,8,t.Constant(1,8)),
                new Call(id,new ImageFunction(10),[new(new(SlotKind.Integer),required ? frame : t.Constant(0,64)),
                    new(new(SlotKind.Integer,1),required ? t.Constant(0,64) : frame)],[]),
                new MemoryRead(readId,frame,32,value)],new Return([new(new(SlotKind.Integer),value)])));
            var function=f.Freeze(); var state=new StateQueries(new ManagedCallEffects(calls));
            checks.True(state.CreateContext(function).Get(state.Escapes,0) is {IsSuccess:true,Value.Any:true},"原生帧位型出现在调用槽中");
            var names=new ValueNamingQuery(state,calls,NamingFacts.Empty,spec,binder);
            var result=new UnobservableEffects(state,calls,names,new InputMemoryImage(),new HashSet<AbstractSlot>{new(SlotKind.Integer)}).Run(function).Function;
            checks.True(ExitChecker.Check(result).IsValid,"裁槽后读取转发通过原生契约");
            var resultValue=((Return)result.Blocks.Single().End).Results.Single().Value;
            checks.True(required ? result.Blocks.Single().Statements.OfType<MemoryRead>().Any(r=>r.Identity==readId)
                : resultValue.ConstantValue==37,"真实帧指针仍会被调用改写；无用槽不阻断帧值转发");
        }
    }
}
